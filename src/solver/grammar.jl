
struct Grammar
    log_variable::Float64
    log_lambda::Float64
    log_free_var::Float64
    library::Vector{Tuple{Program,Tp,Float64}}
    continuation_type::Union{Tp,Nothing}
end

struct ContextualGrammar
    no_context::Grammar
    variable_context::Grammar
    contextual_library::Dict{Program,Vector{Grammar}}
end

function make_dummy_contextual(g::Grammar)
    contextual_library = Dict(e => [g for _ in arguments_of_type(t)] for (e, t, _) in g.library)
    cg = ContextualGrammar(g, g, contextual_library)
    prune_contextual_grammar(cg)
end

function _prune(expression, gs)
    t = closed_inference(expression)
    argument_types = arguments_of_type(t)

    map(zip(argument_types, gs)) do (arg_type, g)
        argument_type = return_of_type(arg_type)
        context, argument_type = instantiate(argument_type, empty_context)
        filtered_library = filter(g.library) do (_, child_type, _)
            child_type = return_of_type(child_type)
            if might_unify(argument_type, child_type)
                k, child_type = instantiate(child_type, context)
                return !isnothing(unify(k, child_type, argument_type))
            else
                return false
            end
        end
        Grammar(g.log_variable, g.log_lambda, g.log_free_var, filtered_library, g.continuation_type)
    end
end

function prune_contextual_grammar(g::ContextualGrammar)
    ContextualGrammar(g.no_context, g.variable_context, Dict(e => _prune(e, gs) for (e, gs) in g.contextual_library))
end

function lse(l::Vector{Float64})::Float64
    if length(l) == 0
        error("LSE: Empty sequence")
    elseif length(l) == 1
        return l[1]
    end
    largest = maximum(l)
    return largest + log(sum(exp(z - largest) for z in l))
end

function _get_free_var_types(p::FreeVar)
    if isnothing(p.var_id)
        return [p.t]
    else
        return []
    end
end

function _get_free_var_types(p::Apply)
    return vcat(_get_free_var_types(p.f), _get_free_var_types(p.x))
end

function _get_free_var_types(p::Abstraction)
    return _get_free_var_types(p.b)
end

function _get_free_var_types(p::Program)
    return []
end

function unifying_expressions(
    cg::ContextualGrammar,
    environment::Vector{Tp},
    context,
    current_hole::Hole,
    skeleton,
    path,
)::Vector{Tuple{Program,Vector{Tp},Context,Float64}}
    #  given a grammar environment requested type and typing context,
    #    what are all of the possible leaves that we might use?
    #    These could be productions in the grammar or they could be variables.
    #    Yields a sequence of:
    #    (leaf, argument types, context with leaf return type unified with requested type, normalized log likelihood)
    request = current_hole.t

    if isempty(current_hole.locations)
        g = cg.no_context
    else
        f, ind = current_hole.locations[1]
        g = cg.contextual_library[f][ind]
    end

    candidates_filter = current_hole.candidates_filter

    if length(path) >= 2 && isa(path[end], ArgTurn) && isa(path[end-1], LeftTurn)
        in_lambda_wrapper = true
    else
        in_lambda_wrapper = false
    end

    if in_lambda_wrapper
        variable_candidates = []
    else
        variable_candidates = collect(skipmissing(map(enumerate(environment)) do (j, t)
            p = Index(j - 1)
            if !candidates_filter(p, skeleton, path)
                return missing
            end
            ll = g.log_variable
            (new_context, t) = apply_context(context, t)
            return_type = return_of_type(t)
            if might_unify(return_type, request)
                new_context = unify(new_context, return_type, request)
                if isnothing(new_context)
                    return missing
                end
                (new_context, t) = apply_context(new_context, t)
                return (p, arguments_of_type(t), new_context, ll)
            else
                return missing
            end
        end))

        nv = log(length(variable_candidates))
        variable_candidates =
            Tuple{Program,Vector{Tp},Context,Float64}[(p, t, k, ll - nv) for (p, t, k, ll) in variable_candidates]
    end

    grammar_candidates = collect(
        Tuple{Program,Vector{Tp},Context,Float64},
        skipmissing(map(g.library) do (p, t, ll)
            if in_lambda_wrapper && p != every_primitive["rev_fix_param"]
                return missing
            end

            for (f, ind) in current_hole.locations
                if violates_symmetry(f, p, ind)
                    return missing
                end
            end

            if !candidates_filter(p, skeleton, path)
                return missing
            end

            if !might_unify(return_of_type(t), request)
                return missing
            else
                new_context, t = instantiate(t, context)
                new_context = unify(new_context, return_of_type(t), request)
                if isnothing(new_context)
                    return missing
                end
                (new_context, t) = apply_context(new_context, t)
                return (p, arguments_of_type(t), new_context, ll)
            end
        end),
    )

    if !isempty(grammar_candidates)
        lambda_context, arg_type = instantiate(t0, context)
        lambda_context, lambda_type = apply_context(lambda_context, request)
        lambda_candidates = [(
            Abstraction(
                Hole(
                    lambda_type,
                    nothing,
                    current_hole.locations,
                    step_arg_checker(candidates_filter, ArgTurn(arg_type)),
                    nothing,
                ),
            ),
            [arg_type],
            lambda_context,
            g.log_lambda,
        )]
    else
        lambda_candidates = []
    end

    free_var_candidates = []
    if candidates_filter.can_have_free_vars
        if !isa(skeleton, Hole)
            p = FreeVar(request, nothing, isempty(current_hole.locations) ? nothing : current_hole.locations[1])
            if candidates_filter(p, skeleton, path)
                push!(free_var_candidates, (p, [], context, g.log_free_var))
            end
        end

        for (i, t) in enumerate(_get_free_var_types(skeleton))
            (new_context, t) = apply_context(context, t)
            return_type = return_of_type(t)
            if might_unify(return_type, request)
                new_context = unify(new_context, return_type, request)
                if isnothing(new_context)
                    continue
                end
                (new_context, t) = apply_context(new_context, t)
                p = FreeVar(t, "r$i", isempty(current_hole.locations) ? nothing : current_hole.locations[1])
                if candidates_filter(p, skeleton, path)
                    push!(free_var_candidates, (p, [], new_context, g.log_free_var))
                end
            end
        end
        nv = log(length(free_var_candidates))
        free_var_candidates =
            Tuple{Program,Vector{Tp},Context,Float64}[(p, t, k, ll - nv) for (p, t, k, ll) in free_var_candidates]
    end

    candidates = vcat(variable_candidates, grammar_candidates, lambda_candidates, free_var_candidates)
    if !isempty(candidates)
        z = lse([ll for (_, _, _, ll) in candidates])
        candidates = Tuple{Program,Vector{Tp},Context,Float64}[(p, t, k, z - ll) for (p, t, k, ll) in candidates]
    end

    if !isnothing(current_hole.possible_values)
        possible_values = current_hole.possible_values
        const_candidates = _const_options(possible_values[1])
        for i in 2:length(possible_values)
            next_const_candidates = Set()
            filter_const_options(const_candidates, possible_values[i], next_const_candidates)
            const_candidates = next_const_candidates
            if isempty(const_candidates)
                break
            end
        end
        for candidate in const_candidates
            p = SetConst(request, candidate)

            if candidates_filter(p, skeleton, path)
                push!(candidates, (p, [], context, 0.001))
            end
        end
    end

    return candidates
end
