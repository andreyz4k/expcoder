
using DataStructures


get_enumeration_timeout(timeout) = time() + timeout
enumeration_timed_out(timeout) = time() > timeout


get_argument_requests(::Index, argument_types, cg) = [(at, cg.variable_context) for at in argument_types]
get_argument_requests(::FreeVar, argumet_types, cg) = []
get_argument_requests(candidate, argument_types, cg) = zip(argument_types, cg.contextual_library[candidate])


struct WrongPath <: Exception end

follow_path(skeleton::Apply, path) =
    if isa(path[1], LeftTurn)
        follow_path(skeleton.f, view(path, 2:length(path)))
    elseif isa(path[1], RightTurn)
        follow_path(skeleton.x, view(path, 2:length(path)))
    else
        throw(WrongPath())
    end

follow_path(skeleton::Abstraction, path) =
    if isa(path[1], ArgTurn)
        follow_path(skeleton.b, view(path, 2:length(path)))
    else
        throw(WrongPath())
    end

follow_path(skeleton::Hole, path) =
    if isempty(path)
        skeleton
    else
        throw(WrongPath())
    end

follow_path(::Any, path) = throw(WrongPath())

path_environment(path) = reverse([t.type for t in path if isa(t, ArgTurn)])

modify_skeleton(skeleton::Abstraction, template, path) =
    if isa(path[1], ArgTurn)
        Abstraction(modify_skeleton(skeleton.b, template, view(path, 2:length(path))))
    else
        throw(WrongPath())
    end

modify_skeleton(::Hole, template, path) =
    if isempty(path)
        template
    else
        throw(WrongPath())
    end

modify_skeleton(skeleton::Apply, template, path) =
    if isa(path[1], LeftTurn)
        Apply(modify_skeleton(skeleton.f, template, view(path, 2:length(path))), skeleton.x)
    elseif isa(path[1], RightTurn)
        Apply(skeleton.f, modify_skeleton(skeleton.x, template, view(path, 2:length(path))))
    else
        throw(WrongPath())
    end

function _unwind_path(path)
    k = length(path)
    while k > 0
        if isa(path[k], LeftTurn)
            break
        end
        k -= 1
    end
    if k > 0
        vcat(path[1:k-1], [RightTurn()])
    else
        []
    end
end

function unwind_path(path, skeleton)
    new_path = _unwind_path(path)
    if !isempty(new_path)
        try
            follow_path(skeleton, new_path)
        catch e
            if isa(e, WrongPath)
                return unwind_path(new_path, skeleton)
            else
                rethrow()
            end
        end
    end
    return new_path
end

violates_symmetry(::Program, a, n) = false
function violates_symmetry(f::Primitive, a, n)
    a = application_function(a)
    if !isa(a, Primitive)
        return false
    end
    return in(
        (n, f.name, a.name),
        Set([
            #  McCarthy primitives
            (0, "car", "cons"),
            (0, "car", "empty"),
            (0, "cdr", "cons"),
            (0, "cdr", "empty"),
            (1, "-", "0"),
            (0, "+", "+"),
            (0, "*", "*"),
            (0, "empty?", "cons"),
            (0, "empty?", "empty"),
            (0, "zero?", "0"),
            (0, "zero?", "1"),
            (0, "zero?", "-1"),
            #  bootstrap target
            (1, "map", "empty"),
            (0, "fold", "empty"),
            (1, "index", "empty"),
        ]),
    ) || in(
        (f.name, a.name),
        Set([
            ("+", "0"),
            ("*", "0"),
            ("*", "1"),
            ("zip", "empty"),
            ("left", "left"),
            ("left", "right"),
            ("right", "right"),
            ("right", "left"),
            #   ("tower_embed","tower_embed")
        ]),
    )
end


block_state_violates_symmetry(state::EnumerationState) =
    if isa(state.skeleton, FreeVar)
        true
    else
        state_violates_symmetry(state.skeleton)
    end

has_index(p::Index, i) = p.n == i
has_index(p::Hole, i) = true
has_index(p::Primitive, i) = false
has_index(p::Invented, i) = false
has_index(p::Apply, i) = has_index(p.f, i) || has_index(p.x, i)
has_index(p::FreeVar, i) = false
has_index(p::Abstraction, i) = has_index(p.b, i + 1)

state_violates_symmetry(p::Abstraction) = state_violates_symmetry(p.b) || !has_index(p.b, 0)
function state_violates_symmetry(p::Apply)
    (f, a) = application_parse(p)
    return state_violates_symmetry(f) ||
           any(state_violates_symmetry, a) ||
           any(violates_symmetry(f, x, n) for (n, x) in enumerate(a))
end
state_violates_symmetry(::Program) = false


function block_state_successors(
    maxFreeParameters,
    cg::ContextualGrammar,
    state::EnumerationState,
)::Vector{EnumerationState}
    current_hole = follow_path(state.skeleton, state.path)
    if !isa(current_hole, Hole)
        error("Error during following path")
    end
    request = current_hole.t
    g = current_hole.grammar

    context = state.context
    context, request = apply_context(context, request)
    if isarrow(request)
        return [
            EnumerationState(
                modify_skeleton(state.skeleton, (Abstraction(Hole(request.arguments[2], g))), state.path),
                context,
                vcat(state.path, [ArgTurn(request.arguments[1])]),
                state.cost,
                state.free_parameters,
            ),
        ]
    else
        environment = path_environment(state.path)
        candidates = unifying_expressions(g, environment, request, context)
        push!(candidates, (FreeVar(request, nothing), [], context, g.log_variable))

        states = map(candidates) do (candidate, argument_types, context, ll)
            new_free_parameters = number_of_free_parameters(candidate)
            argument_requests = get_argument_requests(candidate, argument_types, cg)

            if isempty(argument_types)
                new_skeleton = modify_skeleton(state.skeleton, candidate, state.path)
                return EnumerationState(
                    new_skeleton,
                    context,
                    unwind_path(state.path, new_skeleton),
                    state.cost - ll,
                    state.free_parameters + new_free_parameters,
                )
            else
                application_template = candidate
                for (a, at) in argument_requests
                    application_template = Apply(application_template, Hole(a, at))
                end
                return EnumerationState(
                    modify_skeleton(state.skeleton, application_template, state.path),
                    context,
                    vcat(state.path, [LeftTurn() for _ = 2:length(argument_types)], [RightTurn()]),
                    state.cost - ll,
                    state.free_parameters + new_free_parameters,
                )
            end

        end
        return filter(
            (new_state -> !block_state_violates_symmetry(new_state) && new_state.free_parameters <= maxFreeParameters),
            states,
        )
    end

end


capture_free_vars(sc::SolutionContext, p::Program, context, common_branch) = p, []

function capture_free_vars(sc::SolutionContext, p::Apply, context, common_branch)
    new_f, new_keys_f = capture_free_vars(sc, p.f, context, common_branch)
    new_x, new_keys_x = capture_free_vars(sc, p.x, context, common_branch)
    Apply(new_f, new_x), vcat(new_keys_f, new_keys_x)
end

function capture_free_vars(sc::SolutionContext, p::Abstraction, context, common_branch)
    new_b, new_keys = capture_free_vars(sc, p.b, context, common_branch)
    Abstraction(new_b), new_keys
end

function capture_free_vars(sc::SolutionContext, p::FreeVar, context, common_branch)
    _, t = apply_context(context, p.t)
    key = "\$v$(create_next_var(sc))"
    common_branch.values[key] = EntryBranchItem(NoDataEntry(t), Dict(), [], false)
    FreeVar(t, key), [(key, common_branch, t)]
end


fix_known_free_vars(sc, p::Program, context, fixed_vars) = [(p, [], context, fixed_vars)]

function fix_known_free_vars(sc, p::Abstraction, context, fixed_vars)
    (
        (Abstraction(new_b), inp_keys, ctx, f_vars) for
        (new_b, inp_keys, ctx, f_vars) in fix_known_free_vars(sc, p.b, context, fixed_vars)
    )
end

function fix_known_free_vars(sc, p::Apply, context, fixed_vars)
    output = []
    for (new_f, inp_keys_f, ctx, f_vars1) in fix_known_free_vars(sc, p.f, context, fixed_vars)
        for (new_x, inp_keys_x, ctx2, f_vars2) in fix_known_free_vars(sc, p.x, ctx, f_vars1)
            push!(output, (Apply(new_f, new_x), vcat(inp_keys_f, inp_keys_x), ctx2, f_vars2))
        end
    end
    output
end

function fix_known_free_vars(sc, p::FreeVar, context, fixed_vars)
    if isnothing(p.key)
        output = []
        ctx, t = apply_context(context, p.t)
        for (k, branch, branch_item) in iter_known_vars(sc)
            if is_branch_compatible(k, branch, unique(values(fixed_vars))) && might_unify(t, branch_item.value.type)
                new_ctx = unify(ctx, t, branch_item.value.type)
                new_f_vars = copy(fixed_vars)
                new_f_vars[k] = branch
                push!(
                    output,
                    (FreeVar(branch_item.value.type, k), [(k, branch, branch_item.value.type)], new_ctx, new_f_vars),
                )
            end
        end
        output
    else
        [(p, [(p.key, fixed_vars[p.key], p.t)], context, fixed_vars)]
    end
end


function try_evaluate_program(p, xs, workspace)
    try
        run_analyzed_with_arguments(p, xs, workspace)
    catch e
        #  We have to be a bit careful with exceptions if the
        #     synthesized program generated an exception, then we just
        #     terminate w/ false but if the enumeration timeout was
        #     triggered during program evaluation, we need to pass the
        #     exception on
        if isa(e, InterruptException)
            rethrow()
        elseif isa(e, UnknownPrimitive)
            error("Unknown primitive: $(e.name)")
        elseif isa(e, MethodError)
            @error(xs)
            @error(workspace)
            rethrow()
        else
            # @error e
            return nothing
        end
    end
end

function try_run_block(block::ProgramBlock, inputs)
    input_vals = zip(inputs...)
    if !isnothing(block.output_var[2])
        expected_output = block.output_var[2].values[block.output_var[1]].value
        out_matcher = get_matching_seq(expected_output)
    else
        out_matcher = Iterators.repeated(_ -> Strict)
    end

    p = analyze_evaluation(block.p)

    bm = Strict
    outs = []
    for (xs, matcher) in zip(input_vals, out_matcher)
        out_value = try
            try_evaluate_program(p, [], Dict(k => v for (k, v) in zip(block.input_vars, xs)))
        catch e
            @error xs
            @error block.p
            rethrow()
        end
        if isnothing(out_value)
            # @error block.p
            # @error Dict(k => v for (k, v) in zip(block.inputs, xs))
            return NoMatch, []
        end
        m = matcher(out_value)
        if m == NoMatch
            return NoMatch, []
        else
            bm = min(bm, m)
        end
        push!(outs, out_value)
    end
    new_branch = value_updates(block, outs)
    return bm, new_branch
end

function try_run_block_with_downstream(run_context, sc::SolutionContext, block::ProgramBlock, fixed_branches)
    outs = Dict()
    @info block
    @info fixed_branches
    inputs = []
    for key in block.input_vars
        push!(inputs, fixed_branches[key].values[key].value.values)
    end
    result = @run_with_timeout run_context["timeout"] run_context["redis"] try_run_block(block, inputs)
    @info result
    if isnothing(result) || result[1] == NoMatch
        return (NoMatch, nothing)
    else
        bm, new_branch = result
        outs[block.output_var[1]] = block, new_branch, fixed_branches
        new_fixed_branches = merge(fixed_branches, Dict(k => new_branch for k in keys(new_branch.values)))
        for b in new_branch.values[block.output_var[1]].outgoing_blocks
            unknown = false
            for key in b.input_vars
                if !haskey(new_fixed_branches, key)
                    error("Missing variable $key in fixed branches $new_fixed_branches")
                end
                if !new_fixed_branches[key].values[key].is_known
                    unknown = true
                    break
                end
            end
            if unknown
                continue
            end
            down_match, updates = try_run_block_with_downstream(run_context, sc, b, new_fixed_branches)
            if down_match == NoMatch
                return (NoMatch, nothing)
            else
                bm = min(down_match, bm)
                merge!(outs, updates)
            end
        end
        return (bm, outs)
    end
end

function add_new_block(run_context, sc::SolutionContext, block::ProgramBlock, inputs)
    if all(isknown(branch, key) for (key, branch, _) in inputs)
        fixed_branches = Dict(key => branch for (key, branch, _) in inputs)
        best_match, updates = try_run_block_with_downstream(run_context, sc, block, fixed_branches)
        @info updates
        if best_match == NoMatch
            false
        else
            insert_operation(sc, updates)
            true
        end
    else
        updates = Dict(
            block.output_var[1] => (block, block.output_var[2], Dict(key => branch for (key, branch, _) in inputs)),
        )
        insert_operation(sc, updates)
        true
    end
end

include("extract_solution.jl")

struct HitResult
    hit_program::String
    hit_prior::Any
    hit_likelihood::Any
    hit_time::Any
end

Base.hash(r::HitResult, h::UInt64) = hash(r.hit_program, h)

function insert_new_block(
    run_context,
    s_ctx,
    hits,
    p,
    input_vars,
    output_val,
    request,
    cost,
    start_time,
    task,
    maximum_frontier,
)
    arg_types = [v[3] for v in input_vars]
    if isempty(arg_types)
        p_type = return_of_type(request)
    else
        p_type = arrow(arg_types..., return_of_type(request))
    end

    @info p
    @info input_vars
    @info output_val
    new_block = ProgramBlock(p, p_type, [v[1] for v in input_vars], output_val)
    # @info new_block
    if !add_new_block(run_context, s_ctx, new_block, input_vars)
        return
    end
    get_matches(run_context, s_ctx)
    @info [ke[1] for ke in s_ctx.updated_options]
    # for branch in matches
    #     if is_solved(branch)
    #         # @info p
    #         solution = extract_solution(branch)
    #         ll = @run_with_timeout run_context["program_timeout"] run_context["redis"] task.log_likelihood_checker(task, solution)
    #         if !isnothing(ll) && !isinf(ll)
    #             dt = time() - start_time
    #             hits[HitResult(join(show_program(solution, false)), -cost, ll, dt)] = -cost + ll
    #             while length(hits) > maximum_frontier
    #                 dequeue!(hits)
    #             end
    #         end
    #     else
    #     end
    # end
end

function enumerate_for_task(run_context, g::ContextualGrammar, task, maximum_frontier, verbose = true)
    #    Returns, for each task, (program,logPrior) as well as the total number of enumerated programs
    enumeration_timeout = get_enumeration_timeout(run_context["timeout"])

    start_solution_ctx = create_starting_context(task)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue()

    total_number_of_enumerated_programs = 0
    maxFreeParameters = 2

    pq = PriorityQueue()
    start_time = time()

    for (key, branch, branch_item) in iter_known_vars(start_solution_ctx)
        for candidate in get_candidates_for_known_var(key, branch, branch_item, g)
            pq[(start_solution_ctx, candidate)] = candidate.state.cost
        end
    end
    for (key, branch, branch_item) in iter_unknown_vars(start_solution_ctx)
        for candidate in get_candidates_for_unknown_var(key, branch, branch_item, g)
            pq[(start_solution_ctx, candidate)] = candidate.state.cost
        end
    end

    while (!(enumeration_timed_out(enumeration_timeout))) && !isempty(pq) && length(hits) < maximum_frontier
        (s_ctx, bp), pr = peek(pq)
        dequeue!(pq)
        if state_finished(bp.state)
            state = bp.state
            if isnothing(bp.output_var)
                # @info bp.input_vars
                fixed_inputs = Dict(kv[1] => kv[2] for kv in bp.input_vars if !isnothing(kv))
                fix_options = fix_known_free_vars(s_ctx, state.skeleton, state.context, fixed_inputs)
                # @info fix_options
                for (p, input_vars, _, _) in fix_options
                    reset_updated_keys(s_ctx)
                    output_var = ("\$v$(create_next_var(s_ctx))", nothing)
                    insert_new_block(
                        run_context,
                        s_ctx,
                        hits,
                        p,
                        input_vars,
                        output_var,
                        bp.request,
                        state.cost,
                        start_time,
                        task,
                        maximum_frontier,
                    )
                    total_number_of_enumerated_programs += 1
                end
            else
                p, input_vars =
                    capture_free_vars(s_ctx, state.skeleton, state.context, EntriesBranch(Dict(), nothing, Set()))
                reset_updated_keys(s_ctx)
                insert_new_block(
                    run_context,
                    s_ctx,
                    hits,
                    p,
                    input_vars,
                    bp.output_var,
                    bp.request,
                    state.cost,
                    start_time,
                    task,
                    maximum_frontier,
                )
                total_number_of_enumerated_programs += 1
            end
            # @info s_ctx
        else
            for child in block_state_successors(maxFreeParameters, g, bp.state)
                _, new_request = apply_context(child.context, bp.request)
                pq[(s_ctx, BlockPrototype(child, new_request, bp.input_vars, bp.output_var))] = child.cost
            end
        end
    end

    @info(collect(keys(hits)))

    (collect(keys(hits)), total_number_of_enumerated_programs)

end
