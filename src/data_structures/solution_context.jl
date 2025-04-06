
using DataStructures: PriorityQueue
using NDPriorityQueues

"Solution context"
mutable struct SolutionContext
    task::Task
    task_name::String
    entries::IndexedStorage{Entry}
    types::TypeStorage
    vars_count::CountStorage
    branches_count::CountStorage

    branch_is_unknown::VectorStorage{Bool}
    branch_is_explained::VectorStorage{Bool}
    branch_is_not_copy::VectorStorage{Bool}
    branch_is_not_const::VectorStorage{Bool}

    branch_entries::ConnectionGraphStorage
    branch_vars::ConnectionGraphStorage

    "[branch_id x type_id] -> {false, true}"
    branch_types::ConnectionGraphStorage

    blocks::IndexedStorage{AbstractProgramBlock}
    block_copies_count::CountStorage

    constraints_count::CountStorage
    constraint_contexts::IndexedStorage{Context}

    "[parent_branch_id x child_branch_id] -> {false, true}"
    branch_children::ConnectionGraphStorage

    "[branch_id x block_copy_id] -> block_id"
    branch_incoming_blocks::ValueGraphStorage
    "[branch_id x block_copy_id] -> block_id"
    branch_outgoing_blocks::ValueGraphStorage
    "block_id -> branch_id"
    block_root_branches::VectorStorage{UInt64}

    "[var_id x incoming_entry_id] -> count"
    var_incoming_matches_counts::ValueGraphStorage

    "[var_id x constraint_id] -> branch_id"
    constrained_vars::ValueGraphStorage
    "[branch_id x constraint_id] -> var_id"
    constrained_branches::ValueGraphStorage
    "constraint_id -> context_id"
    constrained_contexts::VectorStorage{UInt64}

    "[branch_id x related_branch_id] -> {false, true}"
    related_explained_complexity_branches::ConnectionGraphStorage
    "[branch_id x related_branch_id] -> {false, true}"
    related_unknown_complexity_branches::ConnectionGraphStorage

    "branch_id -> [{var_id -> block_id}]"
    incoming_paths::PathsStorage

    unknown_min_path_costs::VectorStorage{Float64}
    explained_min_path_costs::VectorStorage{Float64}
    unknown_complexity_factors::VectorStorage{Float64}
    explained_complexity_factors::VectorStorage{Float64}
    complexities::VectorStorage{Float64}
    added_upstream_complexities::VectorStorage{Float64}
    unused_explained_complexities::VectorStorage{Float64}
    unmatched_complexities::VectorStorage{Float64}

    "[previous_var_id x following_var_id] -> {false, true}"
    previous_vars::ConnectionGraphStorage
    previous_branches::ConnectionGraphStorage

    "[branch_id x previous_entry_id] -> {false, true}"
    branch_prev_entries::ConnectionGraphStorage
    "[branch_id x following_entry_id] -> {false, true}"
    branch_foll_entries::ConnectionGraphStorage

    input_keys::Dict{UInt64,String}
    target_branch_id::UInt64
    example_count::Int64
    type_weights::Dict{String,Float64}
    hyperparameters::Dict{String,Any}
    total_number_of_enumerated_programs::Int64
    iterations_count::Int64

    pq_forward::NDPriorityQueue{UInt64,Float64}
    pq_reverse::NDPriorityQueue{UInt64,Float64}
    entry_queues_forward::Dict{UInt64,PriorityQueue}
    entry_queues_reverse::Dict{UInt64,PriorityQueue}
    copies_queue::PriorityQueue
    found_blocks_forward::Dict{UInt64,Vector}
    found_blocks_reverse::Dict{UInt64,Vector}
    blocks_to_insert::Vector

    branch_unknown_from_output::VectorStorage{Bool}
    branch_known_from_input::VectorStorage{Bool}

    entry_grammars::Dict{Tuple{UInt64,Bool},Any}
    waiting_entries::Set{Tuple{UInt64,Bool}}

    known_var_locations::VectorStorage{Vector{Tuple{Program,Int64}}}
    unknown_var_locations::VectorStorage{Vector{Tuple{Program,Int64}}}

    verbose::Bool
    transaction_depth::Int
    stats::DefaultDict
    traced::Bool
end

function create_starting_context(
    task::Task,
    task_name,
    type_weights,
    hyperparameters,
    verbose,
    traced = false,
)::SolutionContext
    argument_types = arguments_of_type(task.task_type)
    example_count = length(task.train_outputs)
    sc = SolutionContext(
        task,
        task_name,
        IndexedStorage{Entry}(),
        TypeStorage(),
        CountStorage(),
        CountStorage(),
        VectorStorage{Bool}(),
        VectorStorage{Bool}(),
        VectorStorage{Bool}(),
        VectorStorage{Bool}(),
        ConnectionGraphStorage(),
        ConnectionGraphStorage(),
        ConnectionGraphStorage(),
        IndexedStorage{AbstractProgramBlock}(),
        CountStorage(),
        CountStorage(),
        IndexedStorage{Context}(),
        ConnectionGraphStorage(),
        ValueGraphStorage(),
        ValueGraphStorage(),
        VectorStorage{UInt64}(),
        ValueGraphStorage(),
        ValueGraphStorage(),
        ValueGraphStorage(),
        VectorStorage{UInt64}(),
        ConnectionGraphStorage(),
        ConnectionGraphStorage(),
        PathsStorage(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        VectorStorage{Float64}(),
        ConnectionGraphStorage(),
        ConnectionGraphStorage(),
        ConnectionGraphStorage(),
        ConnectionGraphStorage(),
        Dict{UInt64,String}(),
        0,
        example_count,
        type_weights,
        hyperparameters,
        0,
        0,
        NDPriorityQueue{UInt64,Float64}(),
        NDPriorityQueue{UInt64,Float64}(),
        Dict(),
        Dict(),
        PriorityQueue(),
        Dict{UInt64,Vector{UInt64}}(),
        Dict{UInt64,Vector{UInt64}}(),
        [],
        VectorStorage{Bool}(),
        VectorStorage{Bool}(),
        Dict{Tuple{UInt64,Bool},Any}(),
        Set{Tuple{UInt64,Bool}}(),
        VectorStorage{Vector{Tuple{Program,Int64}}}(),
        VectorStorage{Vector{Tuple{Program,Int64}}}(),
        verbose,
        0,
        DefaultDict(() -> []),
        traced,
    )
    start_transaction!(sc, 1)
    for (key, t) in argument_types
        values = [inp[key] for inp in task.train_inputs]
        complexity_summary, max_summary, options_count = get_complexity_summary(values, t)
        type_id = push!(sc.types, t)
        entry = ValueEntry(
            type_id,
            values,
            complexity_summary,
            max_summary,
            options_count,
            get_complexity(sc, complexity_summary),
        )
        entry_id = push!(sc.entries, entry)
        var_id = create_next_var(sc)
        sc.input_keys[var_id] = key

        branch_id = increment!(sc.branches_count)

        sc.branch_entries[branch_id] = entry_id
        sc.branch_vars[branch_id] = var_id
        sc.branch_types[branch_id] = type_id
        sc.branch_is_explained[branch_id] = true
        sc.branch_is_not_copy[branch_id] = true
        sc.branch_is_not_const[branch_id] = true
        sc.branch_known_from_input[branch_id] = true

        sc.explained_min_path_costs[branch_id] = 0.0
        sc.explained_complexity_factors[branch_id] = entry.complexity
        sc.complexities[branch_id] = entry.complexity
        sc.added_upstream_complexities[branch_id] = 0.0
        sc.unused_explained_complexities[branch_id] = entry.complexity

        sc.known_var_locations[var_id] = []

        add_path!(sc.incoming_paths, branch_id, empty_path())
    end
    return_type = return_of_type(task.task_type)
    complexity_summary, max_summary, options_count = get_complexity_summary(task.train_outputs, return_type)
    type_id = push!(sc.types, return_type)
    entry = ValueEntry(
        type_id,
        task.train_outputs,
        complexity_summary,
        max_summary,
        options_count,
        get_complexity(sc, complexity_summary),
    )
    entry_id = push!(sc.entries, entry)
    var_id = create_next_var(sc)
    branch_id = increment!(sc.branches_count)

    sc.branch_entries[branch_id] = entry_id
    sc.branch_vars[branch_id] = var_id
    sc.branch_types[branch_id] = type_id
    sc.branch_is_unknown[branch_id] = true
    sc.branch_unknown_from_output[branch_id] = true

    sc.target_branch_id = branch_id

    sc.unknown_min_path_costs[branch_id] = 0.0
    sc.unknown_complexity_factors[branch_id] = entry.complexity
    sc.complexities[branch_id] = entry.complexity
    sc.unmatched_complexities[branch_id] = entry.complexity

    sc.unknown_var_locations[var_id] = []

    return sc
end

function transaction(f, sc::SolutionContext)
    depth = sc.transaction_depth
    local result
    try
        start_transaction!(sc, depth + 1)
        result = f()
    catch e
        # bt = catch_backtrace()
        # @error "Got error in transaction" exception = (e, bt)
        finished = false
        interrupted = nothing
        while !finished
            try
                drop_changes!(sc, depth)
            catch e
                @info e
                if isa(e, InterruptException)
                    interrupted = e
                else
                    rethrow()
                end
            else
                finished = true
            end
        end
        if !isnothing(interrupted)
            throw(interrupted)
        end
        if !isa(e, EnumerationException)
            rethrow()
        end
        return nothing
    else
        finished = false
        interrupted = nothing
        while !finished
            try
                save_changes!(sc, depth)
            catch e
                @info e
                if isa(e, InterruptException)
                    interrupted = e
                else
                    rethrow()
                end
            else
                finished = true
            end
        end
        if !isnothing(interrupted)
            throw(interrupted)
        end
    end
    return result
end

function start_transaction!(sc::SolutionContext, depth)
    start_transaction!(sc.entries, depth)
    start_transaction!(sc.types, depth)
    start_transaction!(sc.vars_count, depth)
    start_transaction!(sc.branches_count, depth)
    start_transaction!(sc.branch_is_explained, depth)
    start_transaction!(sc.branch_is_not_copy, depth)
    start_transaction!(sc.branch_is_not_const, depth)
    start_transaction!(sc.branch_is_unknown, depth)
    start_transaction!(sc.branch_entries, depth)
    start_transaction!(sc.branch_vars, depth)
    start_transaction!(sc.branch_types, depth)
    start_transaction!(sc.blocks, depth)
    start_transaction!(sc.block_copies_count, depth)
    start_transaction!(sc.constraints_count, depth)
    start_transaction!(sc.constraint_contexts, depth)
    start_transaction!(sc.branch_children, depth)
    start_transaction!(sc.branch_incoming_blocks, depth)
    start_transaction!(sc.branch_outgoing_blocks, depth)
    start_transaction!(sc.block_root_branches, depth)
    start_transaction!(sc.var_incoming_matches_counts, depth)
    start_transaction!(sc.constrained_vars, depth)
    start_transaction!(sc.constrained_branches, depth)
    start_transaction!(sc.constrained_contexts, depth)
    start_transaction!(sc.related_explained_complexity_branches, depth)
    start_transaction!(sc.related_unknown_complexity_branches, depth)
    start_transaction!(sc.incoming_paths, depth)
    start_transaction!(sc.unknown_min_path_costs, depth)
    start_transaction!(sc.explained_min_path_costs, depth)
    start_transaction!(sc.unknown_complexity_factors, depth)
    start_transaction!(sc.explained_complexity_factors, depth)
    start_transaction!(sc.complexities, depth)
    start_transaction!(sc.added_upstream_complexities, depth)
    start_transaction!(sc.unused_explained_complexities, depth)
    start_transaction!(sc.unmatched_complexities, depth)
    start_transaction!(sc.previous_vars, depth)
    start_transaction!(sc.branch_unknown_from_output, depth)
    start_transaction!(sc.branch_known_from_input, depth)
    start_transaction!(sc.known_var_locations, depth)
    start_transaction!(sc.unknown_var_locations, depth)
    sc.transaction_depth = depth
    nothing
end

function save_changes!(sc::SolutionContext, depth)
    save_changes!(sc.entries, depth)
    save_changes!(sc.types, depth)
    save_changes!(sc.vars_count, depth)
    save_changes!(sc.branches_count, depth)
    save_changes!(sc.branch_is_explained, depth)
    save_changes!(sc.branch_is_not_copy, depth)
    save_changes!(sc.branch_is_not_const, depth)
    save_changes!(sc.branch_is_unknown, depth)
    save_changes!(sc.branch_entries, depth)
    save_changes!(sc.branch_vars, depth)
    save_changes!(sc.branch_types, depth)
    save_changes!(sc.blocks, depth)
    save_changes!(sc.block_copies_count, depth)
    save_changes!(sc.constraints_count, depth)
    save_changes!(sc.constraint_contexts, depth)
    save_changes!(sc.branch_children, depth)
    save_changes!(sc.branch_incoming_blocks, depth)
    save_changes!(sc.branch_outgoing_blocks, depth)
    save_changes!(sc.block_root_branches, depth)
    save_changes!(sc.var_incoming_matches_counts, depth)
    save_changes!(sc.constrained_vars, depth)
    save_changes!(sc.constrained_branches, depth)
    save_changes!(sc.constrained_contexts, depth)
    save_changes!(sc.related_explained_complexity_branches, depth)
    save_changes!(sc.related_unknown_complexity_branches, depth)
    save_changes!(sc.incoming_paths, depth)
    save_changes!(sc.unknown_min_path_costs, depth)
    save_changes!(sc.explained_min_path_costs, depth)
    save_changes!(sc.unknown_complexity_factors, depth)
    save_changes!(sc.explained_complexity_factors, depth)
    save_changes!(sc.complexities, depth)
    save_changes!(sc.added_upstream_complexities, depth)
    save_changes!(sc.unused_explained_complexities, depth)
    save_changes!(sc.unmatched_complexities, depth)
    save_changes!(sc.previous_vars, depth)
    save_changes!(sc.branch_unknown_from_output, depth)
    save_changes!(sc.branch_known_from_input, depth)
    save_changes!(sc.known_var_locations, depth)
    save_changes!(sc.unknown_var_locations, depth)
    sc.transaction_depth = depth
    nothing
end

function drop_changes!(sc::SolutionContext, depth)
    drop_changes!(sc.entries, depth)
    drop_changes!(sc.types, depth)
    drop_changes!(sc.vars_count, depth)
    drop_changes!(sc.branches_count, depth)
    drop_changes!(sc.branch_is_explained, depth)
    drop_changes!(sc.branch_is_not_copy, depth)
    drop_changes!(sc.branch_is_not_const, depth)
    drop_changes!(sc.branch_is_unknown, depth)
    drop_changes!(sc.branch_entries, depth)
    drop_changes!(sc.branch_vars, depth)
    drop_changes!(sc.branch_types, depth)
    drop_changes!(sc.blocks, depth)
    drop_changes!(sc.block_copies_count, depth)
    drop_changes!(sc.constraints_count, depth)
    drop_changes!(sc.constraint_contexts, depth)
    drop_changes!(sc.branch_children, depth)
    drop_changes!(sc.branch_incoming_blocks, depth)
    drop_changes!(sc.branch_outgoing_blocks, depth)
    drop_changes!(sc.block_root_branches, depth)
    drop_changes!(sc.var_incoming_matches_counts, depth)
    drop_changes!(sc.constrained_vars, depth)
    drop_changes!(sc.constrained_branches, depth)
    drop_changes!(sc.constrained_contexts, depth)
    drop_changes!(sc.related_explained_complexity_branches, depth)
    drop_changes!(sc.related_unknown_complexity_branches, depth)
    drop_changes!(sc.incoming_paths, depth)
    drop_changes!(sc.unknown_min_path_costs, depth)
    drop_changes!(sc.explained_min_path_costs, depth)
    drop_changes!(sc.unknown_complexity_factors, depth)
    drop_changes!(sc.explained_complexity_factors, depth)
    drop_changes!(sc.complexities, depth)
    drop_changes!(sc.added_upstream_complexities, depth)
    drop_changes!(sc.unused_explained_complexities, depth)
    drop_changes!(sc.unmatched_complexities, depth)
    drop_changes!(sc.previous_vars, depth)
    drop_changes!(sc.branch_unknown_from_output, depth)
    drop_changes!(sc.branch_known_from_input, depth)
    drop_changes!(sc.known_var_locations, depth)
    drop_changes!(sc.unknown_var_locations, depth)
    sc.transaction_depth = depth
    nothing
end

function create_next_var(sc::SolutionContext)
    v = increment!(sc.vars_count)
    sc.previous_vars[v, v] = true
    return v
end

const MAX_COST = 1e10

function update_entry_priority(sc::SolutionContext, entry_id::UInt64, is_rev::Bool)
    if is_rev
        pq = sc.pq_reverse
        qs = sc.entry_queues_reverse
    else
        pq = sc.pq_forward
        qs = sc.entry_queues_forward
    end
    if !haskey(qs, entry_id)
        return
    end
    q = qs[entry_id]
    if !isempty(q)
        min_cost = peek(q)[2]

        cost = MAX_COST
        if is_rev
            explained_from_consts = []

            for branch_id in get_connected_to(sc.branch_entries, entry_id)
                if sc.branch_is_explained[branch_id] && sc.branch_is_not_copy[branch_id]
                    if !isnothing(sc.explained_min_path_costs[branch_id])
                        cost = min(
                            cost,
                            (
                                sc.explained_min_path_costs[branch_id]^sc.hyperparameters["path_cost_power"] +
                                min_cost^sc.hyperparameters["block_cost_power"]
                            ) * sc.explained_complexity_factors[branch_id]^sc.hyperparameters["complexity_power"],
                        )
                    elseif !isnothing(sc.unknown_min_path_costs[branch_id])
                        push!(explained_from_consts, branch_id)
                    end
                end
            end

            if cost == MAX_COST
                for branch_id in explained_from_consts
                    cost = min(
                        cost,
                        (
                            sc.unknown_min_path_costs[branch_id]^sc.hyperparameters["path_cost_power"] +
                            min_cost^sc.hyperparameters["block_cost_power"]
                        ) * sc.unknown_complexity_factors[branch_id]^sc.hyperparameters["complexity_power"],
                    )
                end
            end
        else
            for branch_id in get_connected_to(sc.branch_entries, entry_id)
                if sc.branch_is_unknown[branch_id]
                    cost = min(
                        cost,
                        (
                            sc.unknown_min_path_costs[branch_id]^sc.hyperparameters["path_cost_power"] +
                            min_cost^sc.hyperparameters["block_cost_power"]
                        ) * sc.unknown_complexity_factors[branch_id]^sc.hyperparameters["complexity_power"],
                    )
                end
            end
        end
        pq[entry_id] = 1 / cost
        if sc.verbose
            @info "$(is_rev ? "Known" : "Unknown") entry $entry_id priority is $(1 / cost)"
        end
    elseif haskey(pq, entry_id)
        delete!(pq, entry_id)
        if sc.verbose
            @info "Dropped $(is_rev ? "known" : "unknown") entry $entry_id"
        end
    end
end

function get_input_paths_for_new_block(sc::SolutionContext, bl, input_branches)
    new_block_paths = [empty_path()]
    for in_var in bl.input_vars
        inp_branch_id = input_branches[in_var]
        next_paths = []
        for path in new_block_paths
            for inp_path in sc.incoming_paths[inp_branch_id]
                new_path = merge_paths(sc, path, inp_path)
                if !isnothing(new_path)
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
    for v_id in bl.input_vars
        if !haskey(new_paths, input_branches[v_id])
            continue
        end
        new_block_paths_part = [empty_path()]
        for in_var_id in bl.input_vars
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
                    new_path = merge_paths(sc, path, inp_path)
                    if !isnothing(new_path)
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

function get_new_paths_for_block(
    sc::SolutionContext,
    bl_id,
    is_new_block,
    new_paths,
    out_var_id,
    output_branch_id,
    input_branches,
)
    bl = sc.blocks[bl_id]
    if sc.verbose
        @info "Getting paths for new block $bl"
    end
    if is_new_block
        input_paths = get_input_paths_for_new_block(sc, bl, input_branches)
    else
        input_paths = get_input_paths_for_existing_block(sc, bl, input_branches, new_paths)
    end
    if sc.verbose
        @info "Got $(length(input_paths)) $input_paths paths for new block $bl"
    end
    check_path_cost = any(!isnothing(sc.explained_min_path_costs[input_branches[v_id]]) for v_id in bl.input_vars)
    best_cost = Inf
    if check_path_cost
        for path in input_paths
            cost = path_cost(sc, path) + bl.cost
            if cost < best_cost
                best_cost = cost
            end
        end
    end
    return set_new_paths_for_block(sc, bl_id, bl, input_paths, out_var_id, output_branch_id, check_path_cost, best_cost)
end

function set_new_paths_for_block(
    sc::SolutionContext,
    bl_id,
    bl::ProgramBlock,
    input_paths,
    out_var_id,
    output_branch_id,
    check_path_cost,
    best_cost,
)
    filter!(input_paths) do path
        if isa(bl.p, FreeVar)
            if haskey(path.main_path, bl.input_vars[1])
                prev_block = sc.blocks[path.main_path[bl.input_vars[1]]]
                if isa(prev_block, ProgramBlock) && isa(prev_block.p, FreeVar)
                    return false
                end
            end
        else
            for in_var_id in bl.input_vars
                if haskey(path.main_path, in_var_id)
                    prev_block = sc.blocks[path.main_path[in_var_id]]
                    if isa(prev_block, ProgramBlock) && isa(prev_block.p, FreeVar)
                        v_id = prev_block.input_vars[1]
                        if !haskey(path.main_path, v_id)
                            return true
                        end
                        prev_block = sc.blocks[path.main_path[v_id]]
                    end
                    if !isa(prev_block, ProgramBlock) || !isa(prev_block.p, SetConst)
                        return true
                    end
                else
                    return true
                end
            end
            return length(bl.input_vars) == 0
        end
        return true
    end
    if sc.verbose
        @info "Filtered $(length(input_paths)) $input_paths paths for new block $bl"
    end
    return set_new_paths_for_var(
        sc,
        bl_id,
        out_var_id,
        [],
        input_paths,
        output_branch_id,
        check_path_cost,
        best_cost,
        !isa(bl.p, FreeVar),
        !isa(bl.p, SetConst),
    )
end

function set_new_paths_for_block(
    sc::SolutionContext,
    bl_id,
    bl::ReverseProgramBlock,
    input_paths,
    out_var_id,
    output_branch_id,
    check_path_cost,
    best_cost,
)
    filter!(input_paths) do path
        for in_var_id in bl.input_vars
            if haskey(path.main_path, in_var_id)
                prev_block = sc.blocks[path.main_path[in_var_id]]
                return !isa(prev_block, ProgramBlock) || (!isa(prev_block.p, SetConst) && !isa(prev_block.p, FreeVar))
            else
                return true
            end
        end
        error("Reverse block $bl has no input vars; unreachable")
    end
    return set_new_paths_for_var(
        sc,
        bl_id,
        out_var_id,
        [v for v in bl.output_vars if v != out_var_id],
        input_paths,
        output_branch_id,
        check_path_cost,
        best_cost,
        true,
        true,
    )
end

function set_new_paths_for_var(
    sc::SolutionContext,
    bl_id,
    var_id,
    side_vars,
    input_paths,
    out_branch_id,
    check_path_cost,
    best_cost,
    is_not_copy,
    is_not_const,
)
    new_block_paths = []
    for path in input_paths
        p = merge_path(sc, path, var_id, bl_id, side_vars)
        path_added = add_path!(sc.incoming_paths, out_branch_id, p)
        if path_added
            push!(new_block_paths, p)
        end
    end
    if check_path_cost &&
       (isnothing(sc.explained_min_path_costs[out_branch_id]) || best_cost < sc.explained_min_path_costs[out_branch_id])
        sc.explained_min_path_costs[out_branch_id] = best_cost
    end
    if !sc.branch_is_explained[out_branch_id]
        sc.branch_is_explained[out_branch_id] = true
    end
    if is_not_copy && !sc.branch_is_not_copy[out_branch_id]
        sc.branch_is_not_copy[out_branch_id] = true
    end
    if is_not_const && !sc.branch_is_not_const[out_branch_id]
        sc.branch_is_not_const[out_branch_id] = true
    end
    return new_block_paths
end

function branch_complexity_factor_unknown(sc::SolutionContext, branch_id)
    related_branches = get_connected_from(sc.related_unknown_complexity_branches, branch_id)
    return _branch_complexity_factor_unknown(sc, branch_id, related_branches)
end

function branch_complexity_factor_known(sc::SolutionContext, branch_id)
    related_branches = get_connected_from(sc.related_explained_complexity_branches, branch_id)
    return _branch_complexity_factor_known(sc, branch_id, sc.added_upstream_complexities[branch_id], related_branches)
end

function _branch_complexity_factor_known(sc::SolutionContext, branch_id, added_complexity, related_branches)
    return sc.complexities[branch_id] +
           added_complexity +
           sum(sc.unused_explained_complexities[br_id] for br_id in related_branches; init = 0.0)
end

function _branch_complexity_factor_unknown(sc::SolutionContext, branch_id, related_branches)
    return sc.complexities[branch_id] + sum(sc.unmatched_complexities[br_id] for br_id in related_branches; init = 0.0)
end

function _update_complexity_factor_unknown(sc::SolutionContext, branch_id)
    if !isnothing(sc.complexities[branch_id])
        new_factor = branch_complexity_factor_unknown(sc, branch_id)
        if new_factor < sc.unknown_complexity_factors[branch_id]
            sc.unknown_complexity_factors[branch_id] = new_factor
        end
    else
        for out_block_copy_id in keys(get_connected_from(sc.branch_outgoing_blocks, branch_id))
            out_branches = keys(get_connected_to(sc.branch_incoming_blocks, out_block_copy_id))
            for out_branch_id in out_branches
                if sc.unknown_complexity_factors[branch_id] > sc.unknown_complexity_factors[out_branch_id]
                    sc.unknown_complexity_factors[branch_id] = sc.unknown_complexity_factors[out_branch_id]
                end
            end
        end
    end
end

function _push_unmatched_complexity_to_output(sc::SolutionContext, branch_id, fixed_branches, unmatched_complexity)
    current_unmatched_complexity = sc.unmatched_complexities[branch_id]
    if isnothing(current_unmatched_complexity) || current_unmatched_complexity > unmatched_complexity
        sc.unmatched_complexities[branch_id] = unmatched_complexity

        # @info "Updating complexities for $branch_id"
        # @info fixed_branches

        out_block_copies = keys(get_connected_from(sc.branch_outgoing_blocks, branch_id))

        for out_block_copy_id in out_block_copies
            inp_branches = keys(get_connected_to(sc.branch_outgoing_blocks, out_block_copy_id))

            un_complexity = get_sum(sc.unmatched_complexities, inp_branches, 0.0)

            out_branches = keys(get_connected_to(sc.branch_incoming_blocks, out_block_copy_id))

            if any(!isempty(get_connected_from(sc.constrained_branches, out_branch)) for out_branch in out_branches)
                continue
                # error("Not implemented")
            end

            for out_branch_id in out_branches
                _push_unmatched_complexity_to_output(sc, out_branch_id, fixed_branches, un_complexity)
            end
        end
    end
end

function _push_unused_complexity_to_input(sc::SolutionContext, branch_id, fixed_branches, unused_complexity)
    current_unused_complexity = sc.unused_explained_complexities[branch_id]
    parents = get_connected_to(sc.branch_children, branch_id)
    for parent in parents
        if sc.complexities[parent] == 0
            parent_entry = sc.entries[sc.branch_entries[parent]]
            if (
                isa(parent_entry, PatternEntry) &&
                all(value == PatternWrapper(any_object) for value in parent_entry.values)
            ) || (
                isa(parent_entry, AbductibleEntry) &&
                all(value == AbductibleValue(any_object) for value in parent_entry.values)
            )
                return
            end
        end
    end
    if isnothing(current_unused_complexity) || current_unused_complexity > unused_complexity
        sc.unused_explained_complexities[branch_id] = unused_complexity
        for (in_block_copy_id, in_block_id) in get_connected_from(sc.branch_incoming_blocks, branch_id)
            in_block = sc.blocks[in_block_id]

            out_branches = keys(get_connected_to(sc.branch_incoming_blocks, in_block_copy_id))
            if isa(in_block, ReverseProgramBlock)
                if any(
                    v_id -> haskey(fixed_branches, v_id) && !in(fixed_branches[v_id], out_branches),
                    in_block.output_vars,
                )
                    continue
                end
            end

            in_branches = keys(get_connected_to(sc.branch_outgoing_blocks, in_block_copy_id))
            if any(!sc.branch_is_explained[br] for br in in_branches)
                continue
            end
            if any(
                in_var -> haskey(fixed_branches, in_var) && !in(fixed_branches[in_var], in_branches),
                in_block.input_vars,
            )
                continue
            end
            un_complexity = get_sum(sc.unused_explained_complexities, out_branches, 0.0)
            for in_branch_id in in_branches
                _push_unused_complexity_to_input(sc, in_branch_id, fixed_branches, un_complexity)
            end
        end
    end
end

function update_complexity_factors_unknown(sc::SolutionContext, input_branches, output_branch)
    if any(isnothing(sc.complexities[br_id]) for (_, br_id) in input_branches)
        return
    end
    branch_ids = UInt64[br_id for (_, br_id) in input_branches]
    un_complexity = get_sum(sc.unmatched_complexities, branch_ids, 0.0)

    _push_unmatched_complexity_to_output(sc, output_branch, input_branches, un_complexity)

    related_branches = get_connected_to(sc.related_unknown_complexity_branches, output_branch)
    for related_branch_id in related_branches
        # @info "Updating unknown complexity factor for related branch $related_branch_id"
        _update_complexity_factor_unknown(sc, related_branch_id)
    end
end

function update_complexity_factors_known(sc::SolutionContext, bl::ProgramBlock, input_branches, output_branches)
    out_branch_id = output_branches[bl.output_var]
    parents = get_all_parents(sc, out_branch_id)
    # if sc.verbose
    #     @info "Updating known complexity factors for $bl with input branches $input_branches and output branches $output_branches"
    #     @info "Current known complexity factor is $(sc.explained_complexity_factors[out_branch_id])"
    #     @info parents
    #     @info [sc.unknown_complexity_factors[parent] for parent in parents]
    # end
    if isempty(bl.input_vars)
        if isnothing(sc.explained_complexity_factors[out_branch_id])
            best_parent = nothing
            for parent in parents
                if sc.branch_is_unknown[parent] && isnothing(sc.unknown_complexity_factors[parent])
                    @warn "Unknown complexity factor is nothing for $parent"
                    @warn bl
                    @warn input_branches
                    @warn output_branches
                    @warn out_branch_id
                    @warn parents
                    export_solution_context(sc)
                end
                if sc.branch_is_unknown[parent] &&
                   !isnothing(sc.complexities[parent]) &&
                   (
                       isnothing(best_parent) ||
                       sc.unknown_complexity_factors[parent] > sc.unknown_complexity_factors[best_parent]
                   )
                    best_parent = parent
                end
            end
            if isnothing(best_parent)
                sc.added_upstream_complexities[out_branch_id] =
                    sc.unknown_complexity_factors[out_branch_id] - sc.complexities[out_branch_id]
            else
                sc.added_upstream_complexities[out_branch_id] =
                    sc.unknown_complexity_factors[best_parent] - sc.complexities[best_parent]
            end
            sc.explained_complexity_factors[out_branch_id] =
                sc.added_upstream_complexities[out_branch_id] + sc.complexities[out_branch_id]
        end
    else
        related_branches = Dict()
        in_complexity = 0.0
        added_upstream_complexity = 0.0
        for inp_var_id in bl.input_vars
            inp_branch_id = input_branches[inp_var_id]
            in_complexity += sc.complexities[inp_branch_id]
            added_upstream_complexity += sc.added_upstream_complexities[inp_branch_id]
            related_brs = get_connected_from(sc.related_explained_complexity_branches, inp_branch_id)
            merge!(related_branches, Dict(b_id => sc.branch_vars[b_id] for b_id in related_brs))
        end

        for path in get_new_paths(sc.incoming_paths, out_branch_id)
            filtered_related_branches =
                UInt64[b_id for (b_id, var_id) in related_branches if !path_sets_var(path, var_id)]
            if isa(bl.p, FreeVar) || bl.is_reversible
                new_added_complexity = added_upstream_complexity
            else
                new_added_complexity =
                    added_upstream_complexity + max(sc.complexities[out_branch_id] - in_complexity, 0.0)
            end
            new_complexity_factor =
                _branch_complexity_factor_known(sc, out_branch_id, new_added_complexity, filtered_related_branches)
            current_factor = sc.explained_complexity_factors[out_branch_id]
            if isnothing(current_factor) || new_complexity_factor < current_factor
                sc.explained_complexity_factors[out_branch_id] = new_complexity_factor
                sc.added_upstream_complexities[out_branch_id] = new_added_complexity
                deleteat!(sc.related_explained_complexity_branches, out_branch_id, :)
                sc.related_explained_complexity_branches[out_branch_id, filtered_related_branches] = true
            end
        end
    end

    if !any(isnothing, sc.complexities[parent] for parent in parents) && (
        sc.branch_unknown_from_output[out_branch_id] ||
        any(sc.branch_unknown_from_output[parent] for parent in parents)
    )
        # _push_unmatched_complexity_to_output(sc, out_branch_id, input_branches, 0.0)
        # _push_unused_complexity_to_input(sc, out_branch_id, input_branches, 0.0)
        # for inp_branch_var in bl.input_vars
        #     _push_unused_complexity_to_input(sc, input_branches[inp_branch_var], input_branches, 0.0)
        # end
    end
    # if sc.verbose
    #     @info "Updated known complexity factor is $(sc.explained_complexity_factors[out_branch_id])"
    # end
end

function _update_complexity_factor_known(sc::SolutionContext, branch_id)
    new_factor = branch_complexity_factor_known(sc, branch_id)
    if sc.explained_complexity_factors[branch_id] > new_factor
        sc.explained_complexity_factors[branch_id] = new_factor
    end
end

function update_complexity_factors_known(sc::SolutionContext, bl::ReverseProgramBlock, input_branches, output_branches)
    in_branch_id = input_branches[bl.input_vars[1]]

    added_upstream_complexity = sc.added_upstream_complexities[in_branch_id]

    for out_var_id in bl.output_vars
        out_branch_id = output_branches[out_var_id]
        related_brs = get_connected_from(sc.related_explained_complexity_branches, out_branch_id)
        related_branches = Dict(b_id => sc.branch_vars[b_id] for b_id in related_brs)
        for path in get_new_paths(sc.incoming_paths, out_branch_id)
            filtered_related_branches =
                UInt64[b_id for (b_id, var_id) in related_branches if !path_sets_var(path, var_id)]

            new_complexity_factor =
                _branch_complexity_factor_known(sc, out_branch_id, added_upstream_complexity, filtered_related_branches)
            current_factor = sc.explained_complexity_factors[out_branch_id]
            if isnothing(current_factor) || new_complexity_factor < current_factor
                sc.explained_complexity_factors[out_branch_id] = new_complexity_factor
                sc.added_upstream_complexities[out_branch_id] = added_upstream_complexity
                deleteat!(sc.related_explained_complexity_branches, out_branch_id, :)
                sc.related_explained_complexity_branches[out_branch_id, filtered_related_branches] = true
            end
        end
    end

    out_complexity = get_sum(sc.complexities, [output_branches[v_id] for v_id in bl.output_vars], 0.0)
    _push_unused_complexity_to_input(sc, in_branch_id, Dict(), out_complexity)
end

function update_context(sc::SolutionContext)
    updated_unmatched_complexities = get_new_values(sc.unmatched_complexities)
    new_branches = get_new_values(sc.branch_is_unknown)
    setdiff!(updated_unmatched_complexities, new_branches)
    related_branches = union(
        Set{UInt64}(),
        [
            get_connected_to(sc.related_unknown_complexity_branches, br_id) for br_id in updated_unmatched_complexities
        ]...,
    )
    for branch_id in related_branches
        _update_complexity_factor_unknown(sc, branch_id)
    end

    updated_unused_complexities = get_new_values(sc.unused_explained_complexities)
    new_branches = get_new_values(sc.branch_is_explained)
    setdiff!(updated_unused_complexities, new_branches)
    related_branches = union(
        Set{UInt64}(),
        [get_connected_to(sc.related_explained_complexity_branches, br_id) for br_id in updated_unused_complexities]...,
    )
    for branch_id in related_branches
        _update_complexity_factor_known(sc, branch_id)
    end

    solution_paths = get_new_paths(sc.incoming_paths, sc.target_branch_id)
    target_var = sc.branch_vars[sc.target_branch_id]
    output_paths = filter(solution_paths) do solution_path
        vars_from_output = Set{UInt64}([target_var])
        vars_to_check = Set{UInt64}([target_var])
        while !isempty(vars_to_check)
            var_id = pop!(vars_to_check)
            block = sc.blocks[solution_path.main_path[var_id]]
            if isa(block, ProgramBlock) && !isa(block.p, FreeVar)
                union!(vars_from_output, block.input_vars)
                union!(vars_to_check, block.input_vars)
            end
        end

        for (v_id, bl_id) in solution_path.main_path
            bl = sc.blocks[bl_id]
            if isa(bl, ProgramBlock) && !isa(bl.p, FreeVar)
                if !in(v_id, vars_from_output)
                    return false
                end
            end
        end
        return true
    end
    return output_paths
end

function update_prev_follow_vars(sc::SolutionContext, block_id::UInt64)
    bl = sc.blocks[block_id]
    _update_prev_follow_vars(sc, bl)
end

function _update_prev_follow_vars(sc::SolutionContext, bl::ProgramBlock)
    if isempty(bl.input_vars)
        return
    end
    inp_prev_vars = union([get_connected_to(sc.previous_vars, inp_var) for inp_var in bl.input_vars]...)
    out_foll_vars = get_connected_from(sc.previous_vars, bl.output_var)
    sc.previous_vars[inp_prev_vars, out_foll_vars] = true
end

function _update_prev_follow_vars(sc, bl::ReverseProgramBlock)
    if isempty(bl.output_vars)
        return
    end
    inp_prev_vars = union([get_connected_to(sc.previous_vars, inp_var) for inp_var in bl.input_vars]...)
    out_foll_vars = union([get_connected_from(sc.previous_vars, out_var) for out_var in bl.output_vars]...)
    sc.previous_vars[inp_prev_vars, out_foll_vars] = true
end

function vars_in_loop(sc::SolutionContext, known_var_id, unknown_var_id)
    prev_known = get_connected_to(sc.previous_vars, known_var_id)
    foll_unknown = get_connected_from(sc.previous_vars, unknown_var_id)
    !isempty(intersect(prev_known, foll_unknown))
end

function is_block_loops(sc::SolutionContext, block::ProgramBlock)
    out_vars = [block.output_var]
    prev_inputs = union(Set{UInt64}(), [get_connected_to(sc.previous_vars, inp_var) for inp_var in block.input_vars]...)
    foll_outputs = union([get_connected_from(sc.previous_vars, out_var) for out_var in out_vars]...)
    return !isempty(intersect(prev_inputs, foll_outputs))
end
