
function _make_next_mask(next_masks)
    next_count = sum(max(length(m), 1) for m in next_masks)
    next_mask = zeros(Float32, next_count, length(next_masks))

    i = 1
    for (j, m) in enumerate(next_masks)
        if isempty(m)
            next_mask[i, j] = 1
            i += 1
        else
            next_mask[i:i+length(m)-1, j] = m
            i += length(m)
        end
    end
    return next_mask
end

function _extract_program_blocks(p::LetRevClause, blocks)
    push!(blocks, (p.inp_var_id, p.v, true))
    return _extract_program_blocks(p.b, blocks)
end

function _extract_program_blocks(p::LetClause, blocks)
    if !isa(p.v, FreeVar)
        push!(blocks, (p.var_id, p.v, false))
    end
    return _extract_program_blocks(p.b, blocks)
end

function _extract_program_blocks(p::FreeVar, blocks)
    return blocks
end

function _extract_program_blocks(p, blocks)
    push!(blocks, ("output", p, false))
    return blocks
end

function extract_program_blocks(program_str)
    p = parse_program(program_str)
    return _extract_program_blocks(p, [])
end

mutable struct LikelihoodSummary
    uses::Dict
    normalizers::Dict
    constant::Float32
end

function LikelihoodSummary()
    return LikelihoodSummary(Dict(), Dict(), 0.0)
end

function _build_likelihood_summary(
    grammar,
    full_p,
    request,
    p::SetConst,
    context,
    environment,
    checker,
    path,
    locations,
    var_types,
    summary,
)
    return context, summary
end

function _build_likelihood_summary(
    grammar,
    full_p,
    request,
    p,
    context,
    environment,
    checker,
    path,
    locations,
    var_types,
    summary,
)
    if isarrow(request)
        if !isa(p, Abstraction)
            error("Expected abstraction, got $p")
        end
        return _build_likelihood_summary(
            grammar,
            full_p,
            request.arguments[2],
            p.b,
            context,
            vcat([request.arguments[1]], environment),
            step_arg_checker(checker, ArgTurn(request.arguments[1], request.arguments[1])),
            vcat(path, [ArgTurn(request.arguments[1], request.arguments[1])]),
            locations,
            var_types,
            summary,
        )
    end

    f, xs = application_parse(p)

    candidates = []
    next_requests = nothing

    if length(path) >= 2 && isa(path[end], ArgTurn) && isa(path[end-1], LeftTurn)
        in_lambda_wrapper = true
    else
        in_lambda_wrapper = false
    end

    for (i, p) in enumerate(grammar)
        if in_lambda_wrapper && p != every_primitive["rev_fix_param"]
            continue
        end

        for (f, ind) in locations
            if violates_symmetry(f, p, ind)
                continue
            end
        end

        if !checker(p, full_p, path)
            continue
        end

        if might_unify(return_of_type(p.t), request)
            new_context, t = instantiate(p.t, context)
            new_context = unify(new_context, return_of_type(t), request)
            if isnothing(new_context)
                continue
            end
            push!(candidates, i)
            if p == f
                summary.uses[i] = get(summary.uses, i, 0) + 1

                (new_context, t) = apply_context(new_context, t)
                next_requests = (arguments_of_type(t), new_context)
            end
        end
    end

    grammar_length = length(grammar)

    if !isempty(candidates)
        lambda_context, arg_type = instantiate(t0, context)
        lambda_context, lambda_type = apply_context(lambda_context, request)
        push!(candidates, grammar_length + 2)

        if isa(f, Abstraction)
            summary.uses[grammar_length+2] = get(summary.uses, grammar_length + 2, 0) + 1
            next_requests = ([lambda_type, arg_type], lambda_context)
        end
    end

    if !in_lambda_wrapper
        variable_candidates = 0
        is_index = false
        for (j, t) in enumerate(environment)
            p = Index(j - 1)
            if !checker(p, full_p, path)
                continue
            end
            (new_context, t) = apply_context(context, t)
            return_type = return_of_type(t)
            if might_unify(return_type, request)
                new_context = unify(new_context, return_type, request)
                if isnothing(new_context)
                    continue
                end
                variable_candidates += 1

                if p == f
                    is_index = true
                    summary.uses[grammar_length+1] = get(summary.uses, grammar_length + 1, 0) + 1

                    (new_context, t) = apply_context(new_context, t)
                    next_requests = (arguments_of_type(t), new_context)
                end
            end
        end
        if variable_candidates > 0
            push!(candidates, grammar_length + 1)
            if is_index
                summary.constant -= log(variable_candidates)
            end
        end
    end

    if checker.can_have_free_vars
        free_var_candidates = 0
        is_free_var = false

        for (var_id, t) in var_types
            (new_context, t) = apply_context(context, t)
            return_type = return_of_type(t)
            if might_unify(return_type, request)
                new_context = unify(new_context, return_type, request)
                if isnothing(new_context)
                    continue
                end
                p = FreeVar(request, request, var_id, isempty(locations) ? nothing : locations[1])
                if checker(p, full_p, path)
                    free_var_candidates += 1
                    if isa(f, FreeVar) && f.var_id == var_id
                        (new_context, t) = apply_context(new_context, t)
                        var_types[f.var_id] = t
                        is_free_var = true
                        next_requests = ([], new_context)
                    end
                end
            end
        end

        if !isa(full_p, FreeVar)
            p = FreeVar(
                request,
                request,
                UInt64(maximum(filter(k -> isa(k, UInt64), keys(var_types)); init = 0) + 1),
                isempty(locations) ? nothing : locations[1],
            )
            if checker(p, full_p, path)
                free_var_candidates += 1
                if isa(f, FreeVar) && !haskey(var_types, f.var_id)
                    var_types[f.var_id] = request
                    is_free_var = true
                    next_requests = ([], context)
                end
            end
        end

        if free_var_candidates > 0
            push!(candidates, grammar_length + 3)
            if is_free_var
                summary.uses[grammar_length+3] = get(summary.uses, grammar_length + 3, 0) + 1
                summary.constant -= log(free_var_candidates)
            end
        end
    end

    if isnothing(next_requests)
        error("$f is not in possible candidates for $request")
    end

    summary.normalizers[candidates] = get(summary.normalizers, candidates, 0) + 1

    arg_types = next_requests[1]
    context = next_requests[2]

    if isa(f, Abstraction)
        context, summary = _build_likelihood_summary(
            grammar,
            full_p,
            arg_types[1],
            f.b,
            context,
            vcat([arg_types[2]], environment),
            step_arg_checker(checker, ArgTurn(arg_types[2], arg_types[2])),
            vcat(path, [LeftTurn(), ArgTurn(arg_types[2], arg_types[2])]),
            locations,
            var_types,
            summary,
        )
        return _build_likelihood_summary(
            grammar,
            full_p,
            arg_types[2],
            xs[1],
            context,
            environment,
            checker,
            vcat(path, [RightTurn()]),
            [],
            var_types,
            summary,
        )
    end

    if !isempty(arg_types)
        custom_arg_checkers = _get_custom_arg_checkers(f)
        custom_checkers_args_count = length(custom_arg_checkers)

        for (i, (arg_type, x)) in enumerate(zip(arg_types, xs))
            current_checker = step_arg_checker(checker, (f, i))

            if i > custom_checkers_args_count || isnothing(custom_arg_checkers[i])
                arg_checker = current_checker
            else
                arg_checker = combine_arg_checkers(current_checker, custom_arg_checkers[i])
            end

            context, summary = _build_likelihood_summary(
                grammar,
                full_p,
                arg_type,
                x,
                context,
                environment,
                arg_checker,
                vcat(path, [LeftTurn() for _ in i+1:length(xs)], [RightTurn()]),
                [(f, i)],
                var_types,
                summary,
            )
        end
    end
    return context, summary
end

function _preprocess_summary(summary::LikelihoodSummary, grammar_length)
    uses = zeros(Float32, grammar_length)
    for (i, count) in summary.uses
        uses[i] = count
    end
    mask = fill(-Inf32, grammar_length, length(summary.normalizers))
    N = zeros(Float32, length(summary.normalizers))
    for (i, (norm_set, count)) in enumerate(summary.normalizers)
        N[i] = count
        mask[norm_set, i] .= 0
    end
    return (uses, mask, N, summary.constant)
end

function build_likelihood_summary(grammar, request, p, is_reversed)
    summary = LikelihoodSummary()
    context, request = instantiate(request, empty_context)
    _, summary = _build_likelihood_summary(
        grammar,
        p,
        request,
        p,
        context,
        [],
        CombinedArgChecker([SimpleArgChecker(is_reversed, -1, true, nothing)]),
        [],
        [],
        Dict(),
        summary,
    )
    if sum(values(summary.uses); init = 0) != sum(values(summary.normalizers); init = 0)
        @info request
        @info p
        @info is_reversed
        @info summary
        error("Length of uses and normalizers should be the same")
    end
    return _preprocess_summary(summary, length(grammar) + 3)
end
