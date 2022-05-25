
using DataStructures

mutable struct SolutionContext
    entries_storage::EntriesStorage
    var_data::Dict{String,EntryBranch}
    known_branches::DefaultDict{Tp,Vector{EntryBranch}}
    unknown_branches::DefaultDict{Tp,Vector{EntryBranch}}
    target_key::String
    created_vars::Int64
    input_keys::Vector{String}
    inserted_options::Set{EntryBranch}
    updated_cost_options::Set{EntryBranch}
    example_count::Int64
    previous_keys::Dict{String,Set{String}}
    following_keys::Dict{String,Set{String}}
    type_weights::Dict{String,Float64}
    total_number_of_enumerated_programs::Int64
    pq_input::PriorityQueue
    pq_output::PriorityQueue
    branch_queues::Dict{EntryBranch,PriorityQueue}
end

function create_starting_context(task::Task, type_weights)::SolutionContext
    argument_types = arguments_of_type(task.task_type)
    input_keys = []
    previous_keys = Dict{String,Set{String}}()
    following_keys = Dict{String,Set{String}}()
    example_count = length(task.train_outputs)
    target_key = "out"
    sc = SolutionContext(
        EntriesStorage(),
        Dict{String,EntryBranch}(),
        DefaultDict{Tp,Vector{EntryBranch}}(() -> []),
        DefaultDict{Tp,Vector{EntryBranch}}(() -> []),
        target_key,
        0,
        input_keys,
        Set(),
        Set(),
        example_count,
        previous_keys,
        following_keys,
        type_weights,
        0,
        PriorityQueue(),
        PriorityQueue(),
        Dict(),
    )
    for (key, t) in argument_types
        values = [inp[key] for inp in task.train_inputs]
        complexity_summary = get_complexity_summary(values, t)
        entry = ValueEntry(t, values, complexity_summary, get_complexity(sc, complexity_summary))
        entry_index = add_entry(sc.entries_storage, entry)
        sc.var_data[key] = EntryBranch(
            entry_index,
            key,
            t,
            Set(),
            Set(),
            Set(),
            [OrderedDict{String,ProgramBlock}()],
            Set(),
            true,
            true,
            0.0,
            entry.complexity,
        )
        push!(sc.input_keys, key)
        push!(sc.known_branches[t], sc.var_data[key])
        sc.previous_keys[key] = Set([key])
        sc.following_keys[key] = Set([key])
    end
    return_type = return_of_type(task.task_type)
    complexity_summary = get_complexity_summary(task.train_outputs, return_type)
    entry = ValueEntry(return_type, task.train_outputs, complexity_summary, get_complexity(sc, complexity_summary))
    entry_index = add_entry(sc.entries_storage, entry)
    sc.var_data[target_key] = EntryBranch(
        entry_index,
        target_key,
        return_type,
        Set(),
        Set(),
        Set(),
        [],
        Set(),
        false,
        false,
        0.0,
        entry.complexity,
    )
    push!(sc.unknown_branches[return_type], sc.var_data[target_key])
    sc.previous_keys[target_key] = Set([target_key])
    sc.following_keys[target_key] = Set([target_key])
    return sc
end

function reset_updated_keys(ctx::SolutionContext)
    ctx.inserted_options = Set()
    ctx.updated_cost_options = Set()
end

function create_next_var(solution_ctx::SolutionContext)
    solution_ctx.created_vars += 1
end

function check_insert_new_branch(sc::SolutionContext, branch::EntryBranch)
    key = branch.key
    is_new_branch = false
    if isempty(branch.parents)
        if !haskey(sc.var_data, key)
            sc.var_data[key] = branch
            sc.previous_keys[key] = Set([key])
            sc.following_keys[key] = Set([key])
            is_new_branch = true
        end
    else
        for parent in branch.parents
            if !in(branch, parent.children)
                push!(parent.children, branch)
                for child in branch.children
                    if in(child, parent.children)
                        delete!(parent.children, child)
                    end
                    if in(parent, child.parents)
                        delete!(child.parents, parent)
                    end
                    if !in(branch, child.parents)
                        push!(child.parents, branch)
                    end
                end
                is_new_branch = true
            end
        end
    end
    if is_new_branch
        if branch.is_known
            push!(sc.known_branches[branch.type], branch)
        else
            push!(sc.unknown_branches[branch.type], branch)
        end
        push!(sc.inserted_options, branch)
    end
    for constraint in branch.constraints
        for (_, br) in constraint.branches
            if !in(constraint, br.constraints)
                push!(br.constraints, constraint)
            end
        end
    end
    return is_new_branch
end

function get_input_paths_for_new_block(bl, input_branches)
    new_block_paths = [OrderedDict{String,ProgramBlock}()]
    for (in_key, _) in bl.input_vars
        inp_branch = input_branches[in_key]
        next_paths = []
        for path in new_block_paths
            for inp_path in inp_branch.incoming_paths
                bad_path = false
                for (k, b) in inp_path
                    if haskey(path, k) && path[k] != b
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

function get_input_paths_for_existing_block(bl, input_branches, new_paths)
    new_block_paths = []
    for l = 1:length(bl.input_vars)
        if !haskey(new_paths, input_branches[bl.input_vars[l][1]])
            continue
        end
        new_block_paths_part = [OrderedDict{String,ProgramBlock}()]
        for (i, (in_key, _)) in enumerate(bl.input_vars)
            inp_branch = input_branches[in_key]
            next_paths = []
            for path in new_block_paths_part
                if i == l
                    inp_paths = new_paths[inp_branch]
                elseif i < l && haskey(new_paths, inp_branch)
                    inp_paths = filter(p -> !in(p, new_paths[inp_branch]), inp_branch.incoming_paths)
                else
                    inp_paths = inp_branch.incoming_paths
                end
                for inp_path in inp_paths
                    bad_path = false
                    for (k, b) in inp_path
                        if haskey(path, k) && path[k] != b
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

function get_new_paths_for_block(sc, bl::ProgramBlock, is_new_block, new_paths, output_branches, input_branches)
    # @info "Getting paths for existing block $bl"
    if is_new_block
        new_block_paths = get_input_paths_for_new_block(bl, input_branches)
    else
        new_block_paths = get_input_paths_for_existing_block(bl, input_branches, new_paths)
    end
    check_path_cost = any(!isnothing(input_branches[ibr_key].min_path_cost) for (ibr_key, _) in bl.input_vars)
    best_cost = Inf
    for path in new_block_paths
        path[bl.output_var[1]] = bl
        if check_path_cost
            cost = sum(b.cost for b in values(path); init = 0.0)
            if cost < best_cost
                best_cost = cost
            end
        end
    end
    output_var = first(br for br in output_branches if br.key == bl.output_var[1])
    append!(output_var.incoming_paths, new_block_paths)
    if check_path_cost && (isnothing(output_var.min_path_cost) || best_cost < output_var.min_path_cost)
        output_var.min_path_cost = best_cost
        push!(sc.updated_cost_options, output_var)
    end
    new_paths[output_var] = new_block_paths
    if output_var.is_meaningful && !isa(bl.p, FreeVar)
        output_var.is_meaningful = true
    end
end

function get_new_paths_for_block(sc, bl::ReverseProgramBlock, is_new_block, new_paths, output_branches, input_branches)
    # @info "Getting paths for new block $bl"
    if is_new_block
        input_paths = get_input_paths_for_new_block(bl, input_branches)
    else
        input_paths = get_input_paths_for_existing_block(bl, input_branches, new_paths)
    end
    check_path_cost = any(!isnothing(input_branches[ibr_key].min_path_cost) for (ibr_key, _) in bl.input_vars)
    best_cost = Inf
    if check_path_cost
        for path in input_paths
            cost = sum(b.cost for b in values(path); init = 0.0) + bl.cost
            if cost < best_cost
                best_cost = cost
            end
        end
    end
    for (out_key, _) in bl.output_vars
        out_branch = first(br for br in output_branches if br.key == out_key)
        new_block_paths = []
        for path in input_paths
            push!(new_block_paths, merge(path, Dict(out_key => bl)))
        end
        append!(out_branch.incoming_paths, new_block_paths)
        if check_path_cost && (isnothing(out_branch.min_path_cost) || best_cost < out_branch.min_path_cost)
            out_branch.min_path_cost = best_cost
            push!(sc.updated_cost_options, out_branch)
        end
        new_paths[out_branch] = new_block_paths
        out_branch.is_meaningful = true
    end
end

function update_prev_follow_keys(sc, key, bl::ProgramBlock)
    union!(sc.following_keys[key], sc.following_keys[bl.output_var[1]])
    union!(sc.previous_keys[bl.output_var[1]], sc.previous_keys[key])
end

function update_prev_follow_keys(sc, key, bl::ReverseProgramBlock)
    for output_var in bl.output_vars
        union!(sc.following_keys[key], sc.following_keys[output_var[1]])
        union!(sc.previous_keys[output_var[1]], sc.previous_keys[key])
    end
end

function update_complexity_factors(sc, bl::ProgramBlock, input_branches, output_branches)
    factors = [
        input_branches[in_key].complexity_factor for
        (in_key, _) in bl.input_vars if !isnothing(input_branches[in_key].complexity_factor)
    ]
    if !isempty(factors)
        complexity_factor = maximum(factors)
    else
        complexity_factor = nothing
    end
    output_var = first(br for br in output_branches if br.key == bl.output_var[1])
    old_factor = output_var.complexity_factor
    if !isnothing(complexity_factor) && (isnothing(old_factor) || complexity_factor < old_factor)
        output_var.complexity_factor = complexity_factor
    end
end

function update_complexity_factors(sc, bl::ReverseProgramBlock, input_branches, output_branches)
    complexity_factor =
        sum(input_branches[k].complexity_factor for (k, _) in bl.input_vars) -
        sum(get_entry(sc.entries_storage, input_branches[k].value_index).complexity for (k, _) in bl.input_vars) + sum(
            get_entry(sc.entries_storage, first(br for br in output_branches if br.key == k).value_index).complexity for
            (k, _) in bl.output_vars
        )

    for (key, _) in bl.output_vars
        branch = first(br for br in output_branches if br.key == key)
        if isnothing(branch.complexity_factor) || complexity_factor < branch.complexity_factor
            branch.complexity_factor = complexity_factor
        end
    end
end

function insert_operation(sc::SolutionContext, updates)
    new_paths = Dict()
    for (bl, new_branches, input_branches) in updates
        # @info "Inserting $bl"
        # @info new_branches
        # @info input_branches
        is_new_block = false
        for new_branch in new_branches
            is_new_block |= check_insert_new_branch(sc, new_branch)
        end
        for (inp_branch_key, _) in bl.input_vars
            check_insert_new_branch(sc, input_branches[inp_branch_key])
            if !in(bl, input_branches[inp_branch_key].outgoing_blocks)
                is_new_block = true
                push!(input_branches[inp_branch_key].outgoing_blocks, bl)
            end
            update_prev_follow_keys(sc, inp_branch_key, bl)
        end

        if all(input_branches[inp_branch_key].is_known for (inp_branch_key, _) in bl.input_vars)
            get_new_paths_for_block(sc, bl, is_new_block, new_paths, new_branches, input_branches)
            update_complexity_factors(sc, bl, input_branches, new_branches)
        end
    end
    new_full_paths = []
    for br in get_known_children(sc.var_data[sc.target_key])
        if haskey(new_paths, br)
            append!(new_full_paths, new_paths[br])
        end
    end
    return new_full_paths
end


keys_in_loop(sc, known_key, unknown_key) =
    !isempty(intersect(sc.previous_keys[known_key], sc.following_keys[unknown_key]))


function assert_context_consistency(sc::SolutionContext)
    function _iter_children(branch)
        return vcat([branch], [_iter_children(child) for child in branch.children]...)
    end
    function _get_roots(branch)
        if isempty(branch.parents)
            return Set([branch])
        else
            roots = union([_get_roots(parent) for parent in branch.parents]...)
            if length(roots) != 1
                error("Multiple roots for branch $branch")
            end
            return roots
        end
    end
    function _validate_branch(branch::EntryBranch)
        if branch.is_known
            if !isempty(branch.children)
                error("Known branch $branch has children")
            end
            if !in(branch, sc.known_branches[branch.type])
                error("Known branch $branch is not in known_branches")
            end
            if in(branch, sc.unknown_branches[branch.type])
                error("Known branch $branch is in unknown_branches")
            end
        else
            if in(branch, sc.known_branches[branch.type])
                error("Unknown branch $branch is in known_branches")
            end
            if !in(branch, sc.unknown_branches[branch.type])
                error("Unnown branch $branch is not in unknown_branches")
            end
        end
        for block in branch.outgoing_blocks
            if isempty(branch.parents)
                if !in((branch.key, branch), block.input_vars)
                    error("Branch $branch is not in inputs of block $block")
                end
            end
            if isa(block, ProgramBlock)
                out_roots = _get_roots(block.output_var[2])
            else
                out_roots = union([_get_roots(br) for (_, br) in block.output_vars]...)
            end
            for out_root in out_roots
                if !haskey(sc.var_data, out_root.key) || sc.var_data[out_root.key] != out_root
                    error("Branch $out_root is not in var_data")
                end
            end
        end
        for parent in branch.parents
            if !in(branch, parent.children)
                error("Branch $branch is not in parent $parent")
            end
        end
        for child in branch.children
            if !in(branch, child.parents)
                error("Branch $branch is not in child $child")
            end
            if !issubset(branch.outgoing_blocks, child.outgoing_blocks)
                error("Branch $branch outgoing blocks are missing from child $child outgoing blocks")
            end
            if branch.key != child.key
                error("Branch $branch key differs from child $child key")
            end
        end
        for constraint in branch.constraints
            if constraint.branches[branch.key] != branch
                error("Branch $branch is not in constraint $constraint")
            end
            for (_, other_branch) in constraint.branches
                for other_root in _get_roots(other_branch)
                    if !haskey(sc.var_data, other_root.key) || sc.var_data[other_root.key] != other_root
                        error("Branch $other_root is not in var_data")
                    end
                end
            end
        end

    end
    for (key, branch) in sc.var_data
        if !isempty(branch.parents)
            error("Root branch $branch has parents")
        end
        for br in _iter_children(branch)
            _validate_branch(br)
        end
    end
end
