
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
                state.abstractors_only,
            ),
        ]
    else
        environment = path_environment(state.path)
        candidates = unifying_expressions(g, environment, request, context, state.abstractors_only)
        if !isa(state.skeleton, Hole)
            push!(candidates, (FreeVar(request, nothing), [], context, g.log_variable))
        end

        states = map(candidates) do (candidate, argument_types, context, ll)
            new_free_parameters = number_of_free_parameters(candidate)
            argument_requests = get_argument_requests(candidate, argument_types, cg)

            if isempty(argument_types)
                new_skeleton = modify_skeleton(state.skeleton, candidate, state.path)
                new_path = unwind_path(state.path, new_skeleton)
            else
                application_template = candidate
                for (a, at) in argument_requests
                    application_template = Apply(application_template, Hole(a, at))
                end
                new_skeleton = modify_skeleton(state.skeleton, application_template, state.path)
                new_path = vcat(state.path, [LeftTurn() for _ = 2:length(argument_types)], [RightTurn()])
            end
            return EnumerationState(
                new_skeleton,
                context,
                new_path,
                state.cost + ll,
                state.free_parameters + new_free_parameters,
                state.abstractors_only,
            )

        end
        return filter(
            (
                new_state ->
                    !state_violates_symmetry(new_state.skeleton) && new_state.free_parameters <= maxFreeParameters
            ),
            states,
        )
    end

end


capture_free_vars(sc::SolutionContext, p::Program, context, min_path_cost, complexity_factor) = p, []

function capture_free_vars(sc::SolutionContext, p::Apply, context, min_path_cost, complexity_factor)
    new_f, new_keys_f = capture_free_vars(sc, p.f, context, min_path_cost, complexity_factor)
    new_x, new_keys_x = capture_free_vars(sc, p.x, context, min_path_cost, complexity_factor)
    Apply(new_f, new_x), vcat(new_keys_f, new_keys_x)
end

function capture_free_vars(sc::SolutionContext, p::Abstraction, context, min_path_cost, complexity_factor)
    new_b, new_keys = capture_free_vars(sc, p.b, context, min_path_cost, complexity_factor)
    Abstraction(new_b), new_keys
end

function capture_free_vars(sc::SolutionContext, p::FreeVar, context, min_path_cost, complexity_factor)
    _, t = apply_context(context, p.t)
    key = "v$(create_next_var(sc))"
    entry = NoDataEntry(t)
    entry_index = add_entry(sc.entries_storage, entry)
    new_branch =
        EntryBranch(entry_index, key, t, Set(), Set(), Set(), [], Set(), false, false, min_path_cost, complexity_factor)
    FreeVar(t, key), [(key, new_branch, t)]
end


function try_get_reversed_inputs(sc, p::Program, output_var::EntryBranch, cost)
    reversed_programs = get_reversed_program(p, output_var)
    output_entry = get_entry(sc.entries_storage, output_var.value_index)
    outputs = output_entry.values
    calculated_inputs = []
    for rev_pr in reversed_programs
        analazed_rev_pr = analyze_evaluation(rev_pr)
        inp_values = []
        for target_output in outputs
            inp_value = try_evaluate_program(analazed_rev_pr, [], Dict(output_var.key => target_output))
            if isnothing(inp_value)
                return nothing
            end
            push!(inp_values, inp_value)
        end
        input_type = closed_inference(rev_pr)
        complexity_summary = get_complexity_summary(inp_values, input_type)
        push!(
            calculated_inputs,
            ValueEntry(input_type, inp_values, complexity_summary, get_complexity(sc, complexity_summary)),
        )
    end
    inputs = []
    complexity_factor =
        output_var.complexity_factor - output_entry.complexity + sum(entry.complexity for entry in calculated_inputs)
    for entry in calculated_inputs
        key = "v$(create_next_var(sc))"
        entry_index = add_entry(sc.entries_storage, entry)
        branch = EntryBranch(
            entry_index,
            key,
            entry.type,
            Set(),
            Set(),
            Set(),
            [],
            Set(),
            false,
            false,
            output_var.min_path_cost + cost,
            complexity_factor,
        )
        push!(inputs, (key, branch, entry.type))
    end
    new_p, _ = fix_new_free_vars(p, [i[1] for i in inputs])
    return new_p, inputs
end

fix_new_free_vars(p::FreeVar, new_names) = FreeVar(p.t, new_names[1]), view(new_names, 2:length(new_names))
function fix_new_free_vars(p::Apply, new_names)
    new_f, new_f_names = fix_new_free_vars(p.f, new_names)
    new_x, new_x_names = fix_new_free_vars(p.x, new_f_names)
    Apply(new_f, new_x), new_x_names
end
function fix_new_free_vars(p::Abstraction, new_names)
    new_b, new_b_names = fix_new_free_vars(p.b, new_names)
    Abstraction(new_b), new_b_names
end
fix_new_free_vars(p::Program, new_names) = p, new_names

function create_reversed_block(sc, p::Program, input_var::Tuple{String,EntryBranch}, cost)
    reversed_programs = get_reversed_program(p, input_var[2])
    reverse_blocks = []
    input_entry = get_entry(sc.entries_storage, input_var[2].value_index)
    inputs = input_entry.values
    calculated_outputs = []
    for rev_pr in reversed_programs
        analazed_rev_pr = analyze_evaluation(rev_pr)
        out_values = []
        for target_input in inputs
            out_value = try_evaluate_program(analazed_rev_pr, [], Dict(input_var[1] => target_input))
            if isnothing(out_value)
                return nothing
            end
            push!(out_values, out_value)
        end
        out_type = closed_inference(rev_pr)
        complexity_summary = get_complexity_summary(out_values, out_type)
        push!(
            calculated_outputs,
            ValueEntry(out_type, out_values, complexity_summary, get_complexity(sc, complexity_summary)),
        )
    end
    output_vars = []
    complexity_factor =
        input_var[2].complexity_factor - input_entry.complexity + sum(entry.complexity for entry in calculated_outputs)
    for (entry, rev_pr) in zip(calculated_outputs, reversed_programs)
        t = arrow(input_var[2].type, entry.type)
        out_key = "v$(create_next_var(sc))"
        entry_index = add_entry(sc.entries_storage, entry)
        branch = EntryBranch(
            entry_index,
            out_key,
            entry.type,
            Set(),
            Set(),
            Set(),
            [],
            Set(),
            true,
            true,
            input_var[2].min_path_cost + cost,
            complexity_factor,
        )
        push!(output_vars, (out_key, branch))
        push!(reverse_blocks, ProgramBlock(rev_pr, t, 0.0, [input_var], (out_key, branch)))
    end
    new_p, _ = fix_new_free_vars(p, [i[1] for i in output_vars])
    block = ReverseProgramBlock(new_p, reverse_blocks, cost, [input_var], output_vars)
    return block
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

function try_run_block(sc::SolutionContext, block::ProgramBlock, inputs)
    input_vals = zip(inputs...)
    if !isnothing(block.output_var[2])
        expected_output = get_entry(sc.entries_storage, block.output_var[2].value_index)
        out_matcher = get_matching_seq(expected_output)
    else
        out_matcher = Iterators.repeated(_ -> Strict)
    end

    bm = Strict
    outs = []
    for (xs, matcher) in zip(input_vals, out_matcher)
        out_value = try
            try_evaluate_program(block.analized_p, [], Dict(k => v for ((k, _), v) in zip(block.input_vars, xs)))
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
    new_branches, next_blocks = value_updates(sc, block, outs)
    return bm, new_branches, next_blocks
end

function try_run_block(sc::SolutionContext, block::ReverseProgramBlock, inputs)
    bm = Strict
    out_new_branches = []
    next = Set()
    for rev_bl in block.reverse_blocks
        result = try_run_block(sc, rev_bl, inputs)
        if isnothing(result) || result[1] == NoMatch
            return (NoMatch, nothing)
        else
            m, new_branches, next_blocks = result
            bm = min(bm, m)
            append!(out_new_branches, new_branches)
            union!(next, next_blocks)
        end
    end
    return bm, out_new_branches, next
end


function _update_fixed_branches(fixed_branches, new_branches::Vector)
    out_fixed_branches = copy(fixed_branches)
    for new_branch in new_branches
        if new_branch.is_known
            out_fixed_branches[new_branch.key] = new_branch
        end
    end
    out_fixed_branches
end

function _downstream_branch_options(sc, block, fixed_branches, active_constraints, unfixed_keys)
    if isempty(unfixed_keys)
        return false, Set([fixed_branches])
    end
    key = unfixed_keys[1]
    options = Set()
    for constraint in active_constraints
        if constraints_key(constraint, key)
            matching_branches = get_matching_branches(constraint, key)

            if isempty(options)
                options = matching_branches
            else
                options = Set(i for i in options if in(i, matching_branches))
            end
            if isempty(options)
                return Set()
            end
        end
    end
    if isempty(options)
        options = get_all_children(first(br for (k, br) in block.input_vars if k == key))
    end
    results = Set()
    have_unknowns = false
    for option in options
        if !option.is_known
            if !have_unknowns
                entry = get_entry(sc.entries_storage, option.value_index)
                if !isa(entry, ValueEntry)
                    have_unknowns = true
                end
            end
        else
            tail_have_unknowns, tail_results = _downstream_branch_options(
                    sc,
                    block,
                    merge(fixed_branches, Dict(key => option)),
                    union(active_constraints, option.constraints),
                    unfixed_keys[2:end],
                )
            have_unknowns |= tail_have_unknowns
            results = union(
                results,
                tail_results
            )
        end
    end
    have_unknowns, results
end

function _downstream_branch_options(sc, block, fixed_branches)
    active_constraints = union([br.constraints for br in values(fixed_branches)]...)
    unfixed_keys = [key for (key, _) in block.input_vars if !haskey(fixed_branches, key)]
    return _downstream_branch_options(sc, block, fixed_branches, active_constraints, unfixed_keys)
end

function try_run_block_with_downstream(run_context, sc::SolutionContext, block, fixed_branches)
    outs = OrderedSet()
    # @info "Running $block"
    # @info fixed_branches
    inputs = []
    for (key, _) in block.input_vars
        fixed_branch = fixed_branches[key]
        entry = get_entry(sc.entries_storage, fixed_branch.value_index)
        push!(inputs, entry.values)
    end
    result = @run_with_timeout run_context["timeout"] run_context["redis"] try_run_block(sc, block, inputs)
    # @info result[1]
    if isnothing(result) || result[1] == NoMatch
        return (NoMatch, nothing)
    else
        bm, new_branches, next_blocks = result
        push!(outs, (block, new_branches, fixed_branches))
        new_fixed_branches = _update_fixed_branches(fixed_branches, new_branches)
        # @info next_blocks
        # @info new_branch.values[block.output_var[1]].outgoing_blocks
        for b in next_blocks
            have_unknowns, all_downstream_branches = _downstream_branch_options(sc, b, new_fixed_branches)
            for downstream_branches in all_downstream_branches
                down_match, updates = try_run_block_with_downstream(run_context, sc, b, downstream_branches)
                if down_match == NoMatch
                    if have_unknowns
                        continue
                    else
                        return (NoMatch, nothing)
                    end
                else
                    bm = min(down_match, bm)
                    for bl in updates
                        if in(bl, outs)
                            # @warn "Duplicate block in run path: $(bl[1])"
                            delete!(outs, bl)
                        end
                        push!(outs, bl)
                    end
                end
            end
        end
        # @info "End run downstream"
        return (bm, outs)
    end
end

function add_new_block(run_context, sc::SolutionContext, block, inputs)
    assert_context_consistency(sc)
    if all(branch.is_known for (key, branch) in inputs)
        best_match, updates = try_run_block_with_downstream(run_context, sc, block, inputs)
        assert_context_consistency(sc)
        # @info updates
        if best_match == NoMatch
            return nothing
        else
            # @info [(bl, "$(hash(br))", Dict(k => "$(hash(b))" for (k, b) in inps)) for (bl, br, inps) in updates]
            result = insert_operation(sc, updates)
            assert_context_consistency(sc)
            return result
        end
    else
        result = insert_operation(sc, Set([(block, [block.output_var[2]], inputs)]))
        assert_context_consistency(sc)
        return result
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
Base.:(==)(r1::HitResult, r2::HitResult) = r1.hit_program == r2.hit_program


function enqueue_updates(s_ctx::SolutionContext, g)
    assert_context_consistency(s_ctx)
    for branch in union(s_ctx.inserted_options, s_ctx.updated_cost_options)
        if !haskey(s_ctx.branch_queues, branch)
            # if isnothing(branch.min_path_cost)
            #     continue
            # end
            if !branch.is_known
                enqueue_unknown_var(s_ctx, branch, g)
            elseif branch.is_meaningful
                enqueue_known_var(s_ctx, branch, g)
            end
        else
            if branch.is_known
                pq = s_ctx.pq_input
            else
                pq = s_ctx.pq_output
            end
            q = s_ctx.branch_queues[branch]
            min_cost = peek(q)[2]
            pq[branch] = (branch.min_path_cost + min_cost) * branch.complexity_factor
        end
    end
    reset_updated_keys(s_ctx)
    assert_context_consistency(s_ctx)
end

function enumeration_iteration_finished_input(run_context, s_ctx, bp)
    state = bp.state
    if bp.reverse
        new_block = @run_with_timeout run_context["program_timeout"] run_context["redis"] create_reversed_block(s_ctx, state.skeleton, bp.output_var, state.cost)
        if isnothing(new_block)
            return
        end
        input_branches = Dict(bp.output_var[1] => bp.output_var[2])
    else
        arg_types = [branch.type for (_, branch) in bp.input_vars]
        p_type = arrow(arg_types..., return_of_type(bp.request))
        new_block = ProgramBlock(state.skeleton, p_type, state.cost, bp.input_vars, bp.output_var)
        input_branches = Dict(key => branch for (key, branch) in bp.input_vars)
    end
    return new_block, input_branches
end

function enumeration_iteration_finished_output(run_context, s_ctx, bp::BlockPrototype, reversible)
    state = bp.state
    if reversible
        abstractor_results =
            @run_with_timeout run_context["program_timeout"] run_context["redis"] try_get_reversed_inputs(
                s_ctx,
                state.skeleton,
                bp.output_var[2],
                state.cost,
            )
        if !isnothing(abstractor_results)
            p, input_vars = abstractor_results
        else
            return
        end
    else
        p, input_vars = capture_free_vars(
            s_ctx,
            state.skeleton,
            state.context,
            bp.output_var[2].min_path_cost + state.cost,
            bp.output_var[2].complexity_factor,
        )
        create_type_constraint(input_vars, state.context)
    end
    arg_types = [v[3] for v in input_vars]
    if isempty(arg_types)
        p_type = return_of_type(bp.request)
    else
        p_type = arrow(arg_types..., return_of_type(bp.request))
    end
    new_block = ProgramBlock(p, p_type, state.cost, [(v[1], v[2]) for v in input_vars], bp.output_var)
    input_branches = Dict(key => branch for (key, branch, _) in input_vars)
    return new_block, input_branches
end

function enumeration_iteration(run_context, s_ctx, finalizer, maxFreeParameters, g, q, bp, br::EntryBranch)
    reversible = false
    if is_reversible(bp.state.skeleton)
        new_skeleton = fill_free_holes(bp.state.skeleton)
        bp = BlockPrototype(
            EnumerationState(
                new_skeleton,
                bp.state.context,
                [],
                bp.state.cost,
                bp.state.free_parameters,
                bp.state.abstractors_only,
            ),
            bp.request,
            bp.input_vars,
            bp.output_var,
            bp.reverse,
        )
        reversible = true
    end
    if state_finished(bp.state)
        if br.is_known
            new_block_result = enumeration_iteration_finished_input(run_context, s_ctx, bp)
        else
            new_block_result = enumeration_iteration_finished_output(run_context, s_ctx, bp, reversible)
        end
        if !isnothing(new_block_result)
            new_block, input_branches = new_block_result
            new_solution_paths = add_new_block(run_context, s_ctx, new_block, input_branches)
            if !isnothing(new_solution_paths)
                for solution_path in new_solution_paths
                    solution, cost = extract_solution(s_ctx, solution_path)
                    finalizer(solution, cost)
                end
            end
            enqueue_updates(s_ctx, g)
            s_ctx.total_number_of_enumerated_programs += 1
        end
    else
        for child in block_state_successors(maxFreeParameters, g, bp.state)
            _, new_request = apply_context(child.context, bp.request)
            q[BlockPrototype(child, new_request, bp.input_vars, bp.output_var, bp.reverse)] = child.cost
        end
    end
    if br.is_known
        pq = s_ctx.pq_input
    else
        pq = s_ctx.pq_output
    end
    if !isempty(q)
        min_cost = peek(q)[2]
        pq[br] = (br.min_path_cost + min_cost) * br.complexity_factor
    else
        delete!(pq, br)
    end
end


function enumerate_for_task(run_context, g::ContextualGrammar, type_weights, task, maximum_frontier, verbose = true)
    #    Returns, for each task, (program,logPrior) as well as the total number of enumerated programs
    enumeration_timeout = get_enumeration_timeout(run_context["timeout"])
    run_context["timeout_checker"] = () -> enumeration_timed_out(enumeration_timeout)

    s_ctx = create_starting_context(task, type_weights)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue()

    maxFreeParameters = 2

    start_time = time()

    assert_context_consistency(s_ctx)
    for (_, branches) in s_ctx.known_branches
        for branch in branches
            enqueue_known_var(s_ctx, branch, g)
        end
    end
    for (_, branches) in s_ctx.unknown_branches
        for branch in branches
            enqueue_unknown_var(s_ctx, branch, g)
        end
    end
    assert_context_consistency(s_ctx)

    finalizer = function (solution, cost)
        ll = @run_with_timeout run_context["program_timeout"] run_context["redis"] task.log_likelihood_checker(
            task,
            solution,
        )
        if !isnothing(ll) && !isinf(ll)
            dt = time() - start_time
            res = HitResult(join(show_program(solution, false)), -cost, ll, dt)
            if haskey(hits, res)
                # @warn "Duplicated solution $solution"
            else
                hits[res] = -cost + ll
            end
            while length(hits) > maximum_frontier
                dequeue!(hits)
            end
        end
    end

    from_input = true

    while (!(enumeration_timed_out(enumeration_timeout))) &&
              (!isempty(s_ctx.pq_input) || !isempty(s_ctx.pq_output)) &&
              length(hits) < maximum_frontier
        from_input = !from_input
        pq = from_input ? s_ctx.pq_input : s_ctx.pq_output
        if isempty(pq)
            continue
        end
        br, pr = peek(pq)
        # @info "Pull from queue: $br, $pr"
        q = s_ctx.branch_queues[br]
        bp = dequeue!(q)
        enumeration_iteration(run_context, s_ctx, finalizer, maxFreeParameters, g, q, bp, br)
    end

    @info(collect(keys(hits)))

    (collect(keys(hits)), s_ctx.total_number_of_enumerated_programs)

end
