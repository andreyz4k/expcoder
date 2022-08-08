
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


capture_free_vars(sc::SolutionContext, p::Program, context) = p, []

function capture_free_vars(sc::SolutionContext, p::Apply, context)
    new_f, new_vars_f = capture_free_vars(sc, p.f, context)
    new_x, new_vars_x = capture_free_vars(sc, p.x, context)
    Apply(new_f, new_x), vcat(new_vars_f, new_vars_x)
end

function capture_free_vars(sc::SolutionContext, p::Abstraction, context)
    new_b, new_vars = capture_free_vars(sc, p.b, context)
    Abstraction(new_b), new_vars
end

function capture_free_vars(sc::SolutionContext, p::FreeVar, context)
    _, t = apply_context(context, p.t)
    var_id = create_next_var(sc)
    FreeVar(t, var_id), [(var_id, t)]
end


function try_get_reversed_values(sc::SolutionContext, p::Program, context, abstract_branch_id, cost, is_known)
    p, reverse_program = get_reversed_filled_program(p)
    abs_entry = sc.entries[sc.branch_entries[abstract_branch_id]]

    calculated_values = []
    for value in abs_entry.values
        calculated_value = try_run_function(reverse_program, [value])
        if isnothing(calculated_value)
            return nothing
        end
        push!(calculated_values, calculated_value)
    end

    new_p, new_vars = capture_free_vars(sc, p, context)

    new_entries = []
    for ((var_id, t), values) in zip(new_vars, zip(calculated_values...))
        values = collect(values)
        complexity_summary = get_complexity_summary(values, t)
        t_id = push!(sc.types, t)
        if any(isa(value, EitherOptions) for value in values)
            new_entry = EitherEntry(t_id, values, complexity_summary, get_complexity(sc, complexity_summary))
        else
            new_entry = ValueEntry(t_id, values, complexity_summary, get_complexity(sc, complexity_summary))
        end
        push!(new_entries, (var_id, new_entry))
    end

    complexity_factor =
        sc.complexity_factors[abstract_branch_id] - abs_entry.complexity +
        sum(entry.complexity for (_, entry) in new_entries)

    new_branches = []
    either_branch_ids = Int[]
    either_var_ids = Int[]

    abstract_constraints = nonzeroinds(sc.constrained_branches[abstract_branch_id, :])[2]
    has_existing_constraints = length(abstract_constraints) > 0

    abs_related_complexity_branches = sc.related_complexity_branches[abstract_branch_id, :]

    for (var_id, entry) in new_entries
        entry_index = push!(sc.entries, entry)
        branch_id = increment!(sc.created_branches)
        sc.branch_entries[branch_id] = entry_index
        sc.branch_vars[branch_id] = var_id
        sc.branch_types[branch_id, entry.type_id] = entry.type_id
        if is_known
            sc.branches_is_known[branch_id] = true
        else
            sc.branches_is_unknown[branch_id] = true
        end
        sc.min_path_costs[branch_id] = cost + sc.min_path_costs[abstract_branch_id]
        sc.complexity_factors[branch_id] = complexity_factor
        sc.complexities[branch_id] = entry.complexity
        sc.added_upstream_complexities[branch_id] = sc.added_upstream_complexities[abstract_branch_id]
        sc.best_complexities[branch_id] = entry.complexity
        sc.unmatched_complexities[branch_id] = entry.complexity

        if has_existing_constraints
            sc.constrained_branches[branch_id, abstract_constraints] = var_id
            sc.constrained_vars[var_id, abstract_constraints] = branch_id
        elseif isa(entry, EitherEntry)
            push!(either_branch_ids, branch_id)
            push!(either_var_ids, var_id)
        end

        sc.related_complexity_branches[branch_id, :] = abs_related_complexity_branches

        push!(new_branches, (var_id, branch_id, entry.type_id))
    end
    for (_, branch_id, _) in new_branches
        inds = [b_id for (_, b_id, _) in new_branches if b_id != branch_id]
        sc.related_complexity_branches[branch_id, inds] = 1
    end
    if !has_existing_constraints && length(either_branch_ids) > 1
        new_constraint_id = increment!(sc.constraints_count)
        sc.constrained_branches[either_branch_ids, new_constraint_id] = either_var_ids
        sc.constrained_vars[either_var_ids, new_constraint_id] = either_branch_ids
    end

    return new_p, reverse_program, new_branches
end


function try_get_reversed_inputs(sc, p::Program, context, output_branch_id, cost)
    reverse_results = try_get_reversed_values(sc, p, context, output_branch_id, cost, false)
    if !isnothing(reverse_results)
        new_p, _, inputs = reverse_results
        return new_p, inputs
    end
end

function create_reversed_block(sc, p::Program, context, input_var::Tuple{Int,Int}, cost)
    reverse_results = try_get_reversed_values(sc, p, context, input_var[2], cost, true)

    if !isnothing(reverse_results)
        new_p, reverse_program, output_vars = reverse_results
        block = ReverseProgramBlock(
            new_p,
            reverse_program,
            cost,
            Dict([input_var]),
            [(v_id, br) for (v_id, br, _) in output_vars],
        )
        block_id = push!(sc.blocks, block)
        return block_id
    end
end

function try_run_function(f, xs)
    try
        f(xs...)
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

function try_evaluate_program(p, xs, workspace)
    try_run_function(run_analyzed_with_arguments, [p, xs, workspace])
end

function try_run_block(sc::SolutionContext, block::ProgramBlock, fixed_branches, active_constraints)
    inputs = []
    for _ = 1:sc.example_count
        push!(inputs, Dict())
    end
    for (var_id, _) in block.input_vars
        fixed_branch_id = fixed_branches[var_id]
        entry = sc.entries[sc.branch_entries[fixed_branch_id]]
        for (i, input) in enumerate(entry.values)
            inputs[i][var_id] = input
        end
    end

    out_branch_id = get_branch_with_constraints(sc, block.output_var[1], active_constraints, block.output_var[2])
    expected_output = sc.entries[sc.branch_entries[out_branch_id]]
    out_matcher = get_matching_seq(expected_output)

    bm = Strict
    outs = []
    for (xs, matcher) in zip(inputs, out_matcher)
        out_value = try
            try_evaluate_program(block.analized_p, [], xs)
        catch e
            @error xs
            @error block.p
            rethrow()
        end
        if isnothing(out_value)
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
    new_out_branch, old_constraints, new_constraints, has_new_branches =
        value_updates(sc, block, out_branch_id, outs, active_constraints)
    return bm, Dict(sc.branch_vars[out_branch_id] => new_out_branch), old_constraints, new_constraints, has_new_branches
end

function try_run_block(sc::SolutionContext, block::ReverseProgramBlock, fixed_branches, active_constraints)
    inputs = []
    for (var_id, _) in block.input_vars
        fixed_branch_id = fixed_branches[var_id]
        entry = sc.entries[sc.branch_entries[fixed_branch_id]]
        push!(inputs, entry.values)
    end
    bm = Strict
    out_matchers = []
    out_branches = []

    for (var_id, out_branch_root_id) in block.output_vars
        out_branch_id = get_branch_with_constraints(sc, var_id, active_constraints, out_branch_root_id)
        push!(out_branches, out_branch_id)
        expected_output = sc.entries[sc.branch_entries[out_branch_id]]
        out_matcher = get_matching_seq(expected_output)
        push!(out_matchers, out_matcher)
    end

    outs = []
    input_vals = zip(inputs...)

    for (xs, matchers) in zip(input_vals, zip(out_matchers...))
        out_values = try
            try_run_function(block.reverse_program, xs)
        catch e
            @error xs
            @error block.p
            rethrow()
        end
        if isnothing(out_values)
            return NoMatch, []
        end
        for (out_value, matcher) in zip(out_values, matchers)
            m = matcher(out_value)
            if m == NoMatch
                return NoMatch, []
            else
                bm = min(bm, m)
            end
        end
        push!(outs, out_values)
    end
    new_out_branches, old_constraints, new_constraints, has_new_branches =
        value_updates(sc, block, out_branches, outs, active_constraints)

    return bm, new_out_branches, old_constraints, new_constraints, has_new_branches
end


function _update_fixed_branches(fixed_branches, new_branches::Dict)
    out_fixed_branches = merge(fixed_branches, new_branches)
    out_fixed_branches
end

function _update_active_constraints(active_constraints, old_constraints, new_constraints)::Vector{Int}
    return union(setdiff(active_constraints, old_constraints), new_constraints)
end

function _downstream_branch_options(
    sc::SolutionContext,
    block,
    fixed_branches,
    active_constraints::Vector,
    unfixed_vars,
)
    if isempty(unfixed_vars)
        return false, Set([(fixed_branches, active_constraints)])
    end
    var_id = unfixed_vars[1]
    branch_options = DefaultDict(() -> [])
    common_constraints = UInt64[]
    constrained_branches = sc.constrained_vars[var_id, active_constraints]
    for (constraint_id, branch_id) in zip(active_constraints, constrained_branches)
        if isnothing(branch_id)
            push!(common_constraints, constraint_id)
        else
            push!(branch_options[branch_id], constraint_id)
        end
    end
    if isempty(branch_options)
        br_id = block.input_vars[var_id]
        branch_options[br_id] = nonzeroinds(sc.constrained_branches[br_id, :])[2]
    end
    options = Dict()
    have_unknowns = false
    for (branch_id, constraint_ids) in branch_options
        for br_id in get_all_children(sc, branch_id)
            if haskey(options, br_id)
                continue
            end
            if sc.branches_is_unknown[br_id]
                if !have_unknowns
                    entry = sc.entries[sc.branch_entries[br_id]]
                    if !isa(entry, ValueEntry)
                        have_unknowns = true
                    end
                end
            else
                updated_constraints = Set{UInt64}()
                br_constraints = nonzeroinds(sc.constrained_branches[br_id, :])[2]
                for constraint_id in constraint_ids
                    for br_constraint_id in br_constraints
                        c = merge_constraints(sc, constraint_id, br_constraint_id)
                        if !isnothing(c)
                            push!(updated_constraints, c)
                        end
                    end
                end
                if isempty(constraint_ids)
                    updated_constraints = br_constraints
                end
                options[br_id] = updated_constraints
            end
        end
    end
    results = Set()
    for (option, updated_constraints) in options
        tail_have_unknowns, tail_results = _downstream_branch_options(
            sc,
            block,
            merge(fixed_branches, Dict(var_id => option)),
            union(common_constraints, updated_constraints),
            unfixed_vars[2:end],
        )
        have_unknowns |= tail_have_unknowns
        results = union(results, tail_results)
    end
    have_unknowns, results
end

function _downstream_branch_options(sc, block_id, fixed_branches, active_constraints)
    block = sc.blocks[block_id]
    unfixed_vars = [var_id for (var_id, _) in block.input_vars if !haskey(fixed_branches, var_id)]
    return _downstream_branch_options(sc, block, fixed_branches, active_constraints, unfixed_vars)
end

function _save_block_branch_connections(sc::SolutionContext, block_id, block, fixed_branches, out_branches)
    input_br_ids = UInt64[fixed_branches[var_id] for (var_id, _) in block.input_vars]
    sc.branch_outgoing_blocks[input_br_ids, block_id] = 1
    output_br_ids = UInt64[br_id for (_, br_id) in out_branches]
    sc.branch_incoming_blocks[output_br_ids, block_id] = 1
end

function try_run_block_with_downstream(
    run_context,
    sc::SolutionContext,
    block_id,
    fixed_branches,
    active_constraints,
    is_new_block,
    created_paths,
)
    # @info "Running $block_id $(sc.blocks[block_id])"
    # @info fixed_branches
    block = sc.blocks[block_id]
    result = @run_with_timeout run_context["timeout"] run_context["redis"] try_run_block(
        sc,
        block,
        fixed_branches,
        active_constraints,
    )
    # @info result
    if isnothing(result) || result[1] == NoMatch
        return NoMatch
    else
        bm, out_branches, old_constraints, new_constraints, has_new_branches = result
        _save_block_branch_connections(sc, block_id, block, fixed_branches, out_branches)
        block_created_paths =
            get_new_paths_for_block(sc, block_id, is_new_block, created_paths, out_branches, fixed_branches)

        if is_new_block || has_new_branches
            update_complexity_factors_known(sc, block, fixed_branches, out_branches, active_constraints)
        end
        new_paths = merge(created_paths, block_created_paths)
        new_fixed_branches = _update_fixed_branches(fixed_branches, out_branches)
        new_active_constraints = _update_active_constraints(active_constraints, old_constraints, new_constraints)
        out_branch_ids = Int[branch_id for (_, branch_id) in out_branches]
        next_blocks = unique(nonzeroinds(sc.branch_outgoing_blocks[out_branch_ids, :])[2])
        for b_id in next_blocks
            b_id = convert(Int, b_id)
            have_unknowns, all_downstream_branches =
                _downstream_branch_options(sc, b_id, new_fixed_branches, new_active_constraints)
            for (downstream_branches, downstream_constraints) in all_downstream_branches
                down_match = try_run_block_with_downstream(
                    run_context,
                    sc,
                    b_id,
                    downstream_branches,
                    downstream_constraints,
                    false,
                    new_paths,
                )
                if down_match == NoMatch
                    if have_unknowns
                        continue
                    else
                        return NoMatch
                    end
                else
                    bm = min(down_match, bm)
                end
            end
        end
        # @info "End run downstream"
        return bm
    end
end

function add_new_block(run_context, sc::SolutionContext, block_id, inputs)
    assert_context_consistency(sc)
    # @info "Adding block $block_id $(sc.blocks[block_id])"
    block = sc.blocks[block_id]
    update_prev_follow_vars(sc, block)
    if all(!sc.branches_is_unknown[branch_id] for (var_id, branch_id) in inputs)
        active_constraints = Int[]
        if length(inputs) > 1
            error("Not implemented, fix active constraints")
        end
        for (var_id, branch_id) in inputs
            active_constraints = convert(Vector{Int}, nonzeroinds(sc.constrained_branches[branch_id, :])[2])
            # TODO: fix for multiple inputs
        end
        best_match = try_run_block_with_downstream(run_context, sc, block_id, inputs, active_constraints, true, Dict())
        assert_context_consistency(sc)
        if best_match == NoMatch
            return nothing
        else
            result = update_context(sc)
            assert_context_consistency(sc)
            return result
        end
    else
        _save_block_branch_connections(sc, block_id, block, inputs, Dict(block.output_var[1] => block.output_var[2]))
        if all(sc.branches_is_unknown[branch_id] for (var_id, branch_id) in inputs)
            update_complexity_factors_unknown(sc, block)
        else
            error("Not implemented")
        end
        result = update_context(sc)
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


function enqueue_updates(sc::SolutionContext, g)
    assert_context_consistency(sc)
    for branch_id in union(get_new_values(sc.created_branches), get_new_values(sc.complexity_factors))
        if !haskey(sc.branch_queues, branch_id)
            # if isnothing(branch.min_path_cost)
            #     continue
            # end
            if sc.branches_is_unknown[branch_id]
                enqueue_unknown_var(sc, branch_id, g)
            elseif sc.branches_is_known[branch_id]
                enqueue_known_var(sc, branch_id, g)
            end
        else
            if sc.branches_is_known[branch_id]
                pq = sc.pq_input
            elseif sc.branches_is_unknown[branch_id]
                pq = sc.pq_output
            else
                @warn "Branch $branch_id is not meaningful but has a queue"
                continue
            end
            q = sc.branch_queues[branch_id]
            if !isempty(q)
                pq[branch_id] = get_branch_priority(sc, branch_id)
            end
        end
    end
    assert_context_consistency(sc)
end

function enumeration_iteration_finished_input(run_context, sc, bp)
    state = bp.state
    if bp.reverse
        # @info "Try get reversed for $bp"
        new_block_id = @run_with_timeout run_context["program_timeout"] run_context["redis"] create_reversed_block(
            sc,
            state.skeleton,
            state.context,
            bp.output_var,
            state.cost,
        )
        if isnothing(new_block_id)
            return
        end
        input_branches = Dict(bp.output_var[1] => bp.output_var[2])
    else
        arg_types = [sc.types[reduce(any, sc.branch_types[branch_id, :])] for (_, branch_id) in bp.input_vars]
        p_type = arrow(arg_types..., return_of_type(bp.request))
        new_block = ProgramBlock(state.skeleton, p_type, state.cost, bp.input_vars, bp.output_var, false)
        new_block_id = push!(sc.blocks, new_block)
        input_branches = Dict(var_id => branch_id for (var_id, branch_id) in bp.input_vars)
    end
    return new_block_id, input_branches
end

function enumeration_iteration_finished_output(run_context, sc::SolutionContext, bp::BlockPrototype)
    state = bp.state
    is_reverse = is_reversible(state.skeleton)
    if is_reverse
        # @info "Try get reversed for $bp"
        abstractor_results =
            @run_with_timeout run_context["program_timeout"] run_context["redis"] try_get_reversed_inputs(
                sc,
                state.skeleton,
                state.context,
                bp.output_var[2],
                state.cost,
            )
        if !isnothing(abstractor_results)
            p, input_vars = abstractor_results
        else
            return
        end
    elseif isnothing(bp.input_vars)
        p, new_vars = capture_free_vars(sc, state.skeleton, state.context)
        input_vars = []
        output_branch_id = bp.output_var[2]
        min_path_cost = sc.min_path_costs[output_branch_id] + state.cost
        complexity_factor = sc.complexity_factors[output_branch_id]
        added_upstream_complexity = sc.added_upstream_complexities[output_branch_id]
        existing_constraints = nonzeroinds(sc.constrained_branches[output_branch_id, :])[2]
        for (var_id, t) in new_vars
            t_id = push!(sc.types, t)
            entry = NoDataEntry(t_id)
            entry_index = push!(sc.entries, entry)
            branch_id = increment!(sc.created_branches)
            sc.branch_entries[branch_id] = entry_index
            sc.branch_vars[branch_id] = var_id
            sc.branch_types[branch_id, t_id] = t_id
            sc.branches_is_unknown[branch_id] = true
            sc.constrained_branches[branch_id, existing_constraints] = var_id
            sc.constrained_vars[var_id, existing_constraints] = branch_id
            sc.min_path_costs[branch_id] = min_path_cost
            sc.complexity_factors[branch_id] = complexity_factor
            sc.added_upstream_complexities[branch_id] = added_upstream_complexity

            push!(input_vars, (var_id, branch_id, t_id))
        end
        constrained_branches = [b_id for (_, b_id, t_id) in input_vars if is_polymorphic(sc.types[t_id])]
        constrained_vars = [v_id for (v_id, _, t_id) in input_vars if is_polymorphic(sc.types[t_id])]
        if length(constrained_branches) >= 2
            context_id = push!(sc.constraint_contexts, state.context)
            if isempty(existing_constraints)
                new_constraint_id = increment!(sc.constraints_count)
                sc.constrained_branches[constrained_branches, new_constraint_id] = constrained_vars
                sc.constrained_vars[constrained_vars, new_constraint_id] = constrained_branches
                sc.constrained_contexts[constrained_vars, new_constraint_id] = context_id
            else
                sc.constrained_contexts[constrained_vars, existing_constraints] = context_id
            end
        end
    else
        p = state.skeleton
        input_vars =
            [(var_id, branch_id, reduce(any, sc.branch_types[branch_id, :])) for (var_id, branch_id) in bp.input_vars]
    end
    arg_types = [sc.types[v[3]] for v in input_vars]
    if isempty(arg_types)
        p_type = return_of_type(bp.request)
    else
        p_type = arrow(arg_types..., return_of_type(bp.request))
    end
    input_branches = Dict(var_id => branch_id for (var_id, branch_id, _) in input_vars)
    new_block = ProgramBlock(p, p_type, state.cost, input_branches, bp.output_var, is_reverse)
    block_id = push!(sc.blocks, new_block)
    return block_id, input_branches
end

function enumeration_iteration(run_context, sc, finalizer, maxFreeParameters, g, q, bp, br_id)
    if is_reversible(bp.state.skeleton) || state_finished(bp.state)
        # @info "Checking finished $bp"
        if sc.branches_is_unknown[br_id]
            new_block_result = enumeration_iteration_finished_output(run_context, sc, bp)
        else
            new_block_result = enumeration_iteration_finished_input(run_context, sc, bp)
        end
        if !isnothing(new_block_result)
            new_block_id, input_branches = new_block_result
            new_solution_paths = add_new_block(run_context, sc, new_block_id, input_branches)
            if !isnothing(new_solution_paths)
                # @info "Got results $new_solution_paths"
                for solution_path in new_solution_paths
                    solution, cost = extract_solution(sc, solution_path)
                    finalizer(solution, cost)
                end
                enqueue_updates(sc, g)
                sc.total_number_of_enumerated_programs += 1
                save_changes!(sc)
            else
                drop_changes!(sc)
            end
        else
            drop_changes!(sc)
        end
    else
        for child in block_state_successors(maxFreeParameters, g, bp.state)
            _, new_request = apply_context(child.context, bp.request)
            q[BlockPrototype(child, new_request, bp.input_vars, bp.output_var, bp.reverse)] = child.cost
        end
    end
    if sc.branches_is_unknown[br_id]
        pq = sc.pq_output
    else
        pq = sc.pq_input
    end
    if !isempty(q)
        min_cost = peek(q)[2]
        pq[br_id] = (sc.min_path_costs[br_id] + min_cost) * sc.complexity_factors[br_id]
        # @info "$(sc.branches_is_unknown[br_id] ? "Out" : "In") branch $br_id priority is $(pq[br_id])"
    else
        delete!(pq, br_id)
        # @info "Dropped $(sc.branches_is_unknown[br_id] ? "out" : "in") branch $br_id"
    end
end


function enumerate_for_task(run_context, g::ContextualGrammar, type_weights, task, maximum_frontier, verbose = true)
    #    Returns, for each task, (program,logPrior) as well as the total number of enumerated programs
    enumeration_timeout = get_enumeration_timeout(run_context["timeout"])
    run_context["timeout_checker"] = () -> enumeration_timed_out(enumeration_timeout)

    sc = create_starting_context(task, type_weights)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue()

    maxFreeParameters = 2

    start_time = time()

    assert_context_consistency(sc)
    enqueue_updates(sc, g)
    save_changes!(sc)
    assert_context_consistency(sc)

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
              (!isempty(sc.pq_input) || !isempty(sc.pq_output)) &&
              length(hits) < maximum_frontier
        from_input = !from_input
        pq = from_input ? sc.pq_input : sc.pq_output
        if isempty(pq)
            continue
        end
        br_id, pr = peek(pq)
        q = sc.branch_queues[br_id]
        bp = dequeue!(q)
        enumeration_iteration(run_context, sc, finalizer, maxFreeParameters, g, q, bp, br_id)
    end

    @info(collect(keys(hits)))

    (collect(keys(hits)), sc.total_number_of_enumerated_programs)

end
