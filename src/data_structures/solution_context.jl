

"Solution context"
mutable struct SolutionContext
    entries::IndexedStorage{Entry}
    types::TypeStorage
    created_vars::CountStorage
    created_branches::CountStorage

    branches_is_unknown::VectorStorage{Bool}
    branches_is_known::VectorStorage{Bool}
    branch_entries::VectorStorage{Int}
    branch_vars::VectorStorage{Int}

    "[branch_id x type_id] -> type_id"
    branch_types::GraphStorage

    blocks::IndexedStorage{AbstractProgramBlock}
    constraints_count::CountStorage
    constraint_contexts::IndexedStorage{Context}

    "[parent_branch_id x child_branch_id] -> {nothing, 1}"
    branch_children::GraphStorage

    "[branch_id x block_id] -> {nothing, 1}"
    branch_incoming_blocks::GraphStorage
    "[branch_id x block_id] -> {nothing, 1}"
    branch_outgoing_blocks::GraphStorage

    "[var_id x constraint_id] -> branch_id"
    constrained_vars::GraphStorage
    "[branch_id x constraint_id] -> var_id"
    constrained_branches::GraphStorage
    "[var_id x constraint_id] -> context_id"
    constrained_contexts::GraphStorage

    "[branch_id x related_branch_id] -> {nothing, 1}"
    related_complexity_branches::GraphStorage

    "branch_id -> [{var_id -> block_id}]"
    incoming_paths::PathsStorage

    min_path_costs::VectorStorage{Float64}
    complexity_factors::VectorStorage{Float64}
    complexities::VectorStorage{Float64}
    added_upstream_complexities::VectorStorage{Float64}
    best_complexities::VectorStorage{Float64}
    unmatched_complexities::VectorStorage{Float64}

    "[previous_var_id x following_var_id] -> {nothing, 1}"
    previous_vars::GraphStorage

    input_keys::Dict{Int,String}
    target_branch_id::Int
    example_count::Int64
    type_weights::Dict{String,Float64}
    total_number_of_enumerated_programs::Int64
    pq_input::PriorityQueue
    pq_output::PriorityQueue
    branch_queues::Dict{Int,PriorityQueue}
end

function create_starting_context(task::Task, type_weights)::SolutionContext
    argument_types = arguments_of_type(task.task_type)
    example_count = length(task.train_outputs)
    sc = SolutionContext(
        IndexedStorage{Entry}(),
        TypeStorage(),
        CountStorage(),
        CountStorage(),
        VectorStorage{Bool}(false),
        VectorStorage{Bool}(false),
        VectorStorage{Int}(),
        VectorStorage{Int}(),
        GraphStorage(),
        IndexedStorage{AbstractProgramBlock}(),
        CountStorage(),
        IndexedStorage{Context}(),
        GraphStorage(),
        GraphStorage(),
        GraphStorage(),
        GraphStorage(),
        GraphStorage(),
        GraphStorage(),
        GraphStorage(),
        PathsStorage(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        GraphStorage(),
        Dict{Int,String}(),
        0,
        example_count,
        type_weights,
        0,
        PriorityQueue(),
        PriorityQueue(),
        Dict(),
    )
    for (key, t) in argument_types
        values = [inp[key] for inp in task.train_inputs]
        complexity_summary = get_complexity_summary(values, t)
        type_id = push!(sc.types, t)
        entry = ValueEntry(type_id, values, complexity_summary, get_complexity(sc, complexity_summary))
        entry_id = push!(sc.entries, entry)
        var_id = increment!(sc.created_vars)
        sc.input_keys[var_id] = key

        branch_id = increment!(sc.created_branches)

        sc.branch_entries[branch_id] = entry_id
        sc.branch_vars[branch_id] = var_id
        sc.branch_types[branch_id, type_id] = type_id
        sc.branches_is_known[branch_id] = true

        sc.min_path_costs[branch_id] = 0.0
        sc.complexity_factors[branch_id] = entry.complexity
        sc.complexities[branch_id] = entry.complexity
        sc.added_upstream_complexities[branch_id] = 0.0
        sc.best_complexities[branch_id] = entry.complexity
        sc.unmatched_complexities[branch_id] = entry.complexity

        sc.previous_vars[var_id, var_id] = 1
        add_path!(sc.incoming_paths, branch_id, OrderedDict{String,Int}())
    end
    return_type = return_of_type(task.task_type)
    complexity_summary = get_complexity_summary(task.train_outputs, return_type)
    type_id = push!(sc.types, return_type)
    entry = ValueEntry(type_id, task.train_outputs, complexity_summary, get_complexity(sc, complexity_summary))
    entry_id = push!(sc.entries, entry)
    var_id = increment!(sc.created_vars)
    branch_id = increment!(sc.created_branches)

    sc.branch_entries[branch_id] = entry_id
    sc.branch_vars[branch_id] = var_id
    sc.branch_types[branch_id, type_id] = type_id
    sc.branches_is_unknown[branch_id] = true

    sc.target_branch_id = branch_id

    sc.min_path_costs[branch_id] = 0.0
    sc.complexity_factors[branch_id] = entry.complexity
    sc.complexities[branch_id] = entry.complexity
    sc.added_upstream_complexities[branch_id] = 0.0
    sc.best_complexities[branch_id] = entry.complexity
    sc.unmatched_complexities[branch_id] = entry.complexity

    sc.previous_vars[var_id, var_id] = 1
    return sc
end

function save_changes!(sc::SolutionContext)
    save_changes!(sc.entries)
    save_changes!(sc.types)
    save_changes!(sc.created_vars)
    save_changes!(sc.created_branches)
    save_changes!(sc.branches_is_known)
    save_changes!(sc.branches_is_unknown)
    save_changes!(sc.branch_entries)
    save_changes!(sc.branch_vars)
    save_changes!(sc.branch_types)
    save_changes!(sc.blocks)
    save_changes!(sc.constraints_count)
    save_changes!(sc.constraint_contexts)
    save_changes!(sc.branch_children)
    save_changes!(sc.branch_incoming_blocks)
    save_changes!(sc.branch_outgoing_blocks)
    save_changes!(sc.constrained_vars)
    save_changes!(sc.constrained_branches)
    save_changes!(sc.constrained_contexts)
    save_changes!(sc.related_complexity_branches)
    save_changes!(sc.incoming_paths)
    save_changes!(sc.min_path_costs)
    save_changes!(sc.complexity_factors)
    save_changes!(sc.complexities)
    save_changes!(sc.added_upstream_complexities)
    save_changes!(sc.best_complexities)
    save_changes!(sc.unmatched_complexities)
    save_changes!(sc.previous_vars)
end

function drop_changes!(sc::SolutionContext)
    drop_changes!(sc.entries)
    drop_changes!(sc.types)
    drop_changes!(sc.created_vars)
    drop_changes!(sc.created_branches)
    drop_changes!(sc.branches_is_known)
    drop_changes!(sc.branches_is_unknown)
    drop_changes!(sc.branch_entries)
    drop_changes!(sc.branch_vars)
    drop_changes!(sc.branch_types)
    drop_changes!(sc.blocks)
    drop_changes!(sc.constraints_count)
    drop_changes!(sc.constraint_contexts)
    drop_changes!(sc.branch_children)
    drop_changes!(sc.branch_incoming_blocks)
    drop_changes!(sc.branch_outgoing_blocks)
    drop_changes!(sc.constrained_vars)
    drop_changes!(sc.constrained_branches)
    drop_changes!(sc.constrained_contexts)
    drop_changes!(sc.related_complexity_branches)
    drop_changes!(sc.incoming_paths)
    drop_changes!(sc.min_path_costs)
    drop_changes!(sc.complexity_factors)
    drop_changes!(sc.complexities)
    drop_changes!(sc.added_upstream_complexities)
    drop_changes!(sc.best_complexities)
    drop_changes!(sc.unmatched_complexities)
    drop_changes!(sc.previous_vars)
end

function create_next_var(sc::SolutionContext)
    v = increment!(sc.created_vars)
    sc.previous_vars[v, v] = 1
    return v
end

function get_branch_priority(sc::SolutionContext, branch_id::Int)
    q = sc.branch_queues[branch_id]
    if !isempty(q)
        min_cost = peek(q)[2]
        return (sc.min_path_costs[branch_id] + min_cost) * sc.complexity_factors[branch_id]
    end
end

function get_input_paths_for_new_block(sc::SolutionContext, bl, input_branches)
    new_block_paths = [OrderedDict{String,ProgramBlock}()]
    for (in_var, _) in bl.input_vars
        inp_branch_id = input_branches[in_var]
        next_paths = []
        for path in new_block_paths
            for inp_path in sc.incoming_paths[inp_branch_id]
                bad_path = false
                for (v, b) in inp_path
                    if haskey(path, v) && path[v] != b
                        bad_path = true
                        # @warn "Paths mismatch $bl" path inp_path
                        break
                    end
                end
                if !bad_path
                    new_path = merge(path, inp_path)
                    push!(next_paths, new_path)
                end
            end
        end
        new_block_paths = next_paths
    end
    return new_block_paths
end

function get_input_paths_for_existing_block(sc::SolutionContext, bl, input_branches, new_paths)
    new_block_paths = []
    for v_id in keys(bl.input_vars)
        if !haskey(new_paths, input_branches[v_id])
            continue
        end
        new_block_paths_part = [OrderedDict{String,ProgramBlock}()]
        for in_var_id in keys(bl.input_vars)
            inp_branch_id = input_branches[in_var_id]
            next_paths = []
            for path in new_block_paths_part
                if in_var_id == v_id
                    inp_paths = new_paths[inp_branch_id]
                elseif in_var_id < v_id && haskey(new_paths, inp_branch_id)
                    inp_paths = filter(p -> !in(p, new_paths[inp_branch_id]), sc.incoming_paths[inp_branch_id])
                else
                    inp_paths = sc.incoming_paths[inp_branch_id]
                end
                for inp_path in inp_paths
                    bad_path = false
                    for (v, b) in inp_path
                        if haskey(path, v) && path[v] != b
                            bad_path = true
                            # @warn "Paths mismatch $bl" path inp_path
                            break
                        end
                    end
                    if !bad_path
                        new_path = merge(path, inp_path)
                        push!(next_paths, new_path)
                    end
                end
            end
            new_block_paths_part = next_paths
        end
        append!(new_block_paths, new_block_paths_part)
    end
    return new_block_paths
end

function get_new_paths_for_block(sc::SolutionContext, bl_id, is_new_block, new_paths, output_branches, input_branches)
    # @info "Getting paths for new block $bl"
    bl = sc.blocks[bl_id]
    if is_new_block
        input_paths = get_input_paths_for_new_block(sc, bl, input_branches)
    else
        input_paths = get_input_paths_for_existing_block(sc, bl, input_branches, new_paths)
    end
    check_path_cost = nnz(sc.min_path_costs[UInt64[input_branches[v_id] for (v_id, _) in bl.input_vars]]) > 0
    best_cost = Inf
    if check_path_cost
        for path in input_paths
            cost = sum(sc.blocks[b_id].cost for b_id in values(path); init = 0.0) + bl.cost
            if cost < best_cost
                best_cost = cost
            end
        end
    end
    return set_new_paths_for_block(sc, bl_id, bl, input_paths, output_branches, check_path_cost, best_cost)
end

function set_new_paths_for_block(
    sc::SolutionContext,
    bl_id,
    bl::ProgramBlock,
    input_paths,
    output_branches,
    check_path_cost,
    best_cost,
)
    return Dict([
        set_new_paths_for_var(
            sc,
            bl_id,
            bl.output_var[1],
            input_paths,
            output_branches,
            check_path_cost,
            best_cost,
            !isa(bl.p, FreeVar),
        ),
    ])
end

function set_new_paths_for_block(
    sc::SolutionContext,
    bl_id,
    bl::ReverseProgramBlock,
    input_paths,
    output_branches,
    check_path_cost,
    best_cost,
)
    return Dict([
        set_new_paths_for_var(sc, bl_id, out_var_id, input_paths, output_branches, check_path_cost, best_cost, true) for
        (out_var_id, _) in bl.output_vars
    ])
end

function set_new_paths_for_var(
    sc::SolutionContext,
    bl_id,
    var_id,
    input_paths,
    output_branches,
    check_path_cost,
    best_cost,
    is_meaningful,
)
    out_branch_id = output_branches[var_id]
    new_block_paths = []
    for path in input_paths
        p = merge(path, Dict(var_id => bl_id))
        add_path!(sc.incoming_paths, out_branch_id, p)
        push!(new_block_paths, p)
    end
    if check_path_cost && (isnothing(sc.min_path_costs[out_branch_id]) || best_cost < sc.min_path_costs[out_branch_id])
        sc.min_path_costs[out_branch_id] = best_cost
    end
    if is_meaningful && !sc.branches_is_known[out_branch_id]
        sc.branches_is_known[out_branch_id] = true
    end
    return (out_branch_id, new_block_paths)
end

function update_prev_follow_vars(sc::SolutionContext, bl::ProgramBlock)
    if isempty(bl.input_vars)
        return
    end
    inp_vars = [v_id for (v_id, _) in bl.input_vars]
    out_var = bl.output_var[1]
    inp_prev_vars = reduce(any, sc.previous_vars[:, inp_vars], dims = 2)
    subassign!(sc.previous_vars, inp_prev_vars, :, out_var; mask = inp_prev_vars)
    out_foll_vars = sc.previous_vars[out_var, :]
    for inp_var_id in inp_vars
        subassign!(sc.previous_vars, out_foll_vars, inp_var_id, :; mask = out_foll_vars)
    end
end

function update_prev_follow_vars(sc, bl::ReverseProgramBlock)
    inp_vars = [v_id for (v_id, _) in bl.input_vars]
    out_vars = [v_id for (v_id, _) in bl.output_vars]
    inp_prev_vars = reduce(any, sc.previous_vars[:, inp_vars], dims = 2)
    out_foll_vars = reduce(any, sc.previous_vars[out_vars, :], dims = 1; desc = Descriptor())
    # for inp_var_id in inp_vars
    #     subassign!(sc.previous_vars, out_foll_vars', inp_var_id, :; mask=out_foll_vars')
    # end
    out_foll_var_inds = nonzeroinds(out_foll_vars)
    sc.previous_vars[inp_vars, out_foll_var_inds] = 1
    for out_var_id in out_vars
        subassign!(sc.previous_vars, inp_prev_vars, :, out_var_id; mask = inp_prev_vars)
    end
end

function branch_complexity_factor(sc::SolutionContext, branch_id)
    related_branches = nonzeroinds(sc.related_complexity_branches[branch_id, :])[2]
    return _branch_complexity_factor(sc, branch_id, sc.added_upstream_complexities[branch_id], related_branches)
end

function _branch_complexity_factor(sc::SolutionContext, branch_id, added_complexity, related_branches)
    unmatched_branch_ids = []
    regular_branch_ids = []
    branch_is_unknown = sc.branches_is_unknown[branch_id]
    for br_id in related_branches
        if sc.branches_is_unknown[br_id] == branch_is_unknown
            push!(unmatched_branch_ids, br_id)
        else
            push!(regular_branch_ids, br_id)
        end
    end
    return sc.complexities[branch_id] +
           added_complexity +
           sum(sc.unmatched_complexities[br_id] for br_id in unmatched_branch_ids; init = 0.0) +
           sum(sc.complexities[br_id] for br_id in regular_branch_ids; init = 0.0)
end

function _update_complexity_factor_unknown(sc::SolutionContext, branch_id)
    if !isnothing(sc.complexities[branch_id])
        new_factor = branch_complexity_factor(sc, branch_id)
        if new_factor < sc.complexity_factors[branch_id]
            sc.complexity_factors[branch_id] = new_factor
        end
    else
        for out_block_id in nonzeroinds(sc.branch_outgoing_blocks[branch_id, :])[2]
            out_block = sc.blocks[out_block_id]
            out_branch_id = out_block.output_var[2]
            if sc.complexity_factors[out_branch_id] < sc.complexity_factors[branch_id]
                sc.complexity_factors[branch_id] = sc.complexity_factors[out_branch_id]
            end
        end
    end
end

function _push_best_complexity_to_output(
    sc::SolutionContext,
    branch_id,
    fixed_branches,
    active_constraints,
    best_complexity,
    unmatched_complexity,
)
    current_best_complexity = sc.best_complexities[branch_id]
    current_unmatched_complexity = sc.unmatched_complexities[branch_id]
    if current_best_complexity > best_complexity || current_unmatched_complexity > unmatched_complexity
        sc.best_complexities[branch_id] = min(best_complexity, current_best_complexity)
        sc.unmatched_complexities[branch_id] = min(unmatched_complexity, current_unmatched_complexity)

        out_blocks = nonzeroinds(sc.branch_outgoing_blocks[branch_id, :])[2]

        for out_block_id in out_blocks
            new_branches = copy(fixed_branches)
            new_constraints = active_constraints
            in_complexity = 0.0
            un_complexity = 0.0

            out_block = sc.blocks[out_block_id]

            for (in_var_id, in_root_branch_id) in out_block.input_vars
                if haskey(new_branches, in_var_id)
                    in_branch_id = new_branches[in_var_id]
                else
                    in_branch_id = get_branch_with_constraints(sc, in_var_id, new_constraints, in_root_branch_id)
                end
                in_complexity += sc.best_complexities[in_branch_id]
                un_complexity += sc.unmatched_complexities[in_branch_id]
                new_branches[in_var_id] = in_branch_id
                if nnz(sc.constrained_vars[in_var_id, new_constraints]) == 0
                    new_constraints = union(new_constraints, nonzeroinds(sc.constrained_branches[in_branch_id, :])[2])
                end
            end
            out_var_id = out_block.output_var[1]
            out_branch_id = get_branch_with_constraints(sc, out_var_id, new_constraints, out_block.output_var[2])
            if nnz(sc.constrained_vars[out_var_id, new_constraints]) == 0
                new_constraints = union(new_constraints, nonzeroinds(sc.constrained_branches[out_branch_id, :])[2])
            end
            new_branches[out_var_id] = out_branch_id
            _push_best_complexity_to_output(
                sc,
                out_branch_id,
                new_branches,
                new_constraints,
                in_complexity,
                un_complexity,
            )
        end
    end
end

function _push_unmatched_complexity_to_input(sc::SolutionContext, branch_id, fixed_branches, unmatched_complexity)
    if sc.unmatched_complexities[branch_id] > unmatched_complexity
        sc.unmatched_complexities[branch_id] = unmatched_complexity
        for in_block_id in nonzeroinds(sc.branch_incoming_blocks[branch_id, :])[2]
            in_block = sc.blocks[in_block_id]
            if isa(in_block, ReverseProgramBlock)
                un_complexity = sum(
                    sc.unmatched_complexities[(haskey(fixed_branches, v) ? fixed_branches[v] : b_id)] for
                    (v, b_id) in in_block.output_vars
                )
            else
                v = in_block.output_var[1]
                un_complexity =
                    sc.unmatched_complexities[(haskey(fixed_branches, v) ? fixed_branches[v] : in_block.output_var[2])]
            end
            for (in_var, in_branch_id) in in_block.input_vars
                if haskey(fixed_branches, in_var)
                    in_branch_id = fixed_branches[in_var]
                end
                _push_unmatched_complexity_to_input(sc, in_branch_id, fixed_branches, un_complexity)
            end
        end
    end
end

function update_complexity_factors_unknown(sc::SolutionContext, bl::ProgramBlock)
    if any(isnothing(sc.complexities[br_id]) for (_, br_id) in bl.input_vars)
        return
    end
    branch_ids = [br_id for (_, br_id) in bl.input_vars]
    in_complexity = reduce(+, sc.complexities[branch_ids])

    active_constraints = unique(nonzeroinds(sc.constrained_branches[branch_ids, :])[2])

    _push_best_complexity_to_output(
        sc,
        bl.output_var[2],
        bl.input_vars,
        active_constraints,
        in_complexity,
        in_complexity,
    )

    related_branches = nonzeroinds(sc.related_complexity_branches[bl.output_var[2], :])[2]
    for related_branch_id in related_branches
        update_related_branch(sc, related_branch_id)
    end
end

function update_complexity_factors_known(
    sc::SolutionContext,
    bl::ProgramBlock,
    input_branches,
    output_branches,
    active_constraints,
)
    out_branch_id = output_branches[bl.output_var[1]]
    parents = nonzeroinds(sc.branch_children[:, out_branch_id])[1]
    if isempty(bl.input_vars)
        if isempty(parents)
            error("No parents for branch $out_branch")
        end
        # parent_complexities = Set()
        best_parent = nothing
        for parent in parents
            # if !isnothing(sc.complexities[parent])
            #     push!(parent_complexities, sc.complexities[parent])
            # end
            if isnothing(best_parent) || sc.complexity_factors[parent] > sc.complexity_factors[best_parent]
                best_parent = parent
            end
        end
        if isnothing(sc.complexity_factors[out_branch_id]) ||
           sc.complexity_factors[best_parent] < sc.complexity_factors[out_branch_id]
            sc.complexity_factors[out_branch_id] = sc.complexity_factors[best_parent]
            sc.added_upstream_complexities[out_branch_id] =
                sc.complexity_factors[out_branch_id] - sc.complexities[out_branch_id]
            # out_branch.related_complexity_branches = best_parent.related_complexity_branches
        end
        # if !isempty(parent_complexities) && new_complexity < maximum(parent_complexities)
        #     _push_factor_diff_to_output(sc, out_branch, maximum(parent_complexities) - new_complexity)
        # end
    else
        related_branches = Dict()
        in_complexity = 0.0
        added_upstream_complexity = 0.0
        for (inp_var_id, _) in bl.input_vars
            inp_branch_id = input_branches[inp_var_id]
            in_complexity += sc.complexities[inp_branch_id]
            added_upstream_complexity += sc.added_upstream_complexities[inp_branch_id]
            related_brs = nonzeroinds(sc.related_complexity_branches[inp_branch_id, :])[2]
            merge!(related_branches, Dict(zip(related_brs, sc.branch_vars[related_brs])))
        end

        for path in get_new_paths(sc.incoming_paths, out_branch_id)
            filtered_related_branches = UInt64[b_id for (b_id, var_id) in related_branches if !haskey(path, var_id)]
            if isa(bl.p, FreeVar) || bl.is_reversible
                new_added_complexity = added_upstream_complexity
            else
                new_added_complexity =
                    added_upstream_complexity + max(sc.complexities[out_branch_id] - in_complexity, 0.0)
            end
            new_complexity_factor =
                _branch_complexity_factor(sc, out_branch_id, new_added_complexity, filtered_related_branches)
            current_factor = sc.complexity_factors[out_branch_id]
            if isnothing(current_factor) || new_complexity_factor < current_factor
                sc.complexity_factors[out_branch_id] = new_complexity_factor
                sc.added_upstream_complexities[out_branch_id] = new_added_complexity
                deleteat!(sc.related_complexity_branches, out_branch_id, :)
                sc.related_complexity_branches[out_branch_id, filtered_related_branches] = 1
            end
        end
    end
    # @info out_branch

    for parent in parents
        if !isnothing(sc.complexities[parent])
            _push_best_complexity_to_output(
                sc,
                parent,
                input_branches,
                active_constraints,
                sc.best_complexities[parent],
                0.0,
            )
            for (inp_branch_var, _) in bl.input_vars
                _push_unmatched_complexity_to_input(sc, input_branches[inp_branch_var], input_branches, 0.0)
            end
        end
    end
end

function _update_complexity_factor_known(sc::SolutionContext, branch_id)
    new_factor = branch_complexity_factor(sc, branch_id)
    if sc.complexity_factors[branch_id] > new_factor
        sc.complexity_factors[branch_id] = new_factor
    end
end

function _push_factor_diff_reverse_to_input(sc::SolutionContext, branch_id, best_complexity, unmatched_complexity)
    current_best_complexity = sc.best_complexities[branch_id]
    current_unmatched_complexity = sc.unmatched_complexities[branch_id]
    if current_best_complexity > best_complexity || current_unmatched_complexity > unmatched_complexity
        sc.best_complexities[branch_id] = min(current_best_complexity, best_complexity)
        sc.unmatched_complexities[branch_id] = min(current_unmatched_complexity, unmatched_complexity)

        in_blocks = nonzeroinds(sc.branch_incoming_blocks[branch_id, :])[2]

        for in_block_id in in_blocks
            in_block = sc.blocks[in_block_id]
            if !isa(in_block, ReverseProgramBlock)
                continue
            end
            out_complexity = reduce(+, sc.best_complexities[[b for (_, b) in in_block.output_vars]])
            un_complexity = reduce(+, sc.unmatched_complexities[[b for (_, b) in in_block.output_vars]])
            _push_factor_diff_reverse_to_input(sc, first(values(in_block.input_vars)), out_complexity, un_complexity)
        end
    end
end

function update_complexity_factors_known(
    sc,
    bl::ReverseProgramBlock,
    input_branches,
    output_branches,
    active_constraints,
)
    in_branch_id = input_branches[first(keys(bl.input_vars))]
    out_complexity = reduce(+, sc.complexities[[b_id for (_, b_id) in bl.output_vars]])
    _push_factor_diff_reverse_to_input(sc, in_branch_id, out_complexity, out_complexity)
end

function update_related_branch(sc, branch_id)
    if !sc.branches_is_unknown[branch_id]
        _update_complexity_factor_known(sc, branch_id)
    else
        _update_complexity_factor_unknown(sc, branch_id)
    end
end

function update_context(sc::SolutionContext)
    updated_unmatched_complexities = get_new_values(sc.unmatched_complexities)
    new_branches = get_new_values(sc.created_branches)
    setdiff!(updated_unmatched_complexities, new_branches)
    related_branches = nonzeroinds(sc.related_complexity_branches[:, updated_unmatched_complexities])[1]
    for branch_id in related_branches
        update_related_branch(sc, branch_id)
    end

    new_full_paths = []
    for br_id in get_known_children(sc, sc.target_branch_id)
        append!(new_full_paths, get_new_paths(sc.incoming_paths, br_id))
    end
    return new_full_paths
end

function vars_in_loop(sc::SolutionContext, known_var_id, unknown_var_id)
    prev_known = sc.previous_vars[:, known_var_id]
    foll_unknown = sc.previous_vars[unknown_var_id, :]
    !isnothing((foll_unknown*prev_known)[1])
end

function assert_context_consistency(sc::SolutionContext)
    function _validate_branch(branch_id)
        if !sc.branches_is_unknown[branch_id]
            if nnz(sc.branch_children[branch_id, :]) > 0
                error("Known branch $branch_id has children")
            end
        else
            if sc.branches_is_known[branch_id]
                error("Unknown branch $branch_id is in known_branches")
            end
        end
        branch_parents = nonzeroinds(sc.branch_children[:, branch_id])[1]
        var_id = sc.branch_vars[branch_id]
        for block_id in nonzeroinds(sc.branch_outgoing_blocks[branch_id, :])[2]
            block = sc.blocks[block_id]
            if isempty(branch_parents)
                if block.input_vars[var_id] != branch_id
                    error("Branch $branch_id is not in inputs of block $block")
                end
            end
        end

        branch_outgoing_blocks = sc.branch_outgoing_blocks[branch_id, :]
        for child_id in nonzeroinds(sc.branch_children[branch_id, :])[2]
            if any(in(p_id, branch_parents) for p_id in nonzeroinds(sc.branch_children[:, child_id])[1])
                error("Branch $child_id is a child of $branch_id but also is a child of one of its parents")
            end
            child_outgoing_blocks = sc.branch_outgoing_blocks[child_id, :]
            if nnz(branch_outgoing_blocks) != nnz(emul(branch_outgoing_blocks, child_outgoing_blocks))
                error("Branch $branch_id outgoing blocks are missing from child $child_id outgoing blocks")
            end
            if sc.branch_vars[branch_id] != sc.branch_vars[child_id]
                error("Branch $branch_id key differs from child $child_id key")
            end
        end
        for constraint_id in nonzeroinds(sc.constrained_branches[branch_id, :])[2]
            if sc.constrained_branches[branch_id, constraint_id] != var_id
                error(
                    "Constrained var_id in constraint $constraint_id for branch $branch_id differs from original $var_id",
                )
            end
            if sc.constrained_vars[var_id, constraint_id] != branch_id
                error(
                    "Constrained branch_id in constraint $constraint_id for var_id $var_id differs from expected $branch_id",
                )
            end
        end
        # if !isnothing(branch.complexity) &&
        #    branch.complexity_factor !=
        #    branch.complexity + sum(b.best_complexity for b in branch.related_complexity_branches; init = 0.0)
        #     error(
        #         "Branch $branch complexity factor is should be $(branch.complexity + sum(b.best_complexity for b in branch.related_complexity_branches; init=0.0)) but is $(branch.complexity_factor)",
        #     )
        # end

    end
    for branch_id = 1:sc.created_branches[]
        _validate_branch(branch_id)
    end
end
