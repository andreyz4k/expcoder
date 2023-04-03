
function get_all_parents(sc, branch_id)
    parents = nonzeroinds(sc.branch_children[:, branch_id])
    for parent_id in parents
        parents = union(parents, get_all_parents(sc, parent_id))
    end
    return parents
end

# function is_branch_compatible(key, branch, fixed_branches)
#     for fixed_branch in fixed_branches
#         if haskey(fixed_branch.values, key)
#             return fixed_branch == branch
#         end
#     end
#     return true
# end

function value_updates(
    sc,
    block::ProgramBlock,
    block_id,
    target_output::Dict{UInt64,UInt64},
    new_values,
    fixed_branches::Dict{UInt64,UInt64},
    is_new_block,
    created_paths,
)
    branch_id = target_output[block.output_var]
    entry = sc.entries[sc.branch_entries[branch_id]]
    t_id = push!(sc.types, return_of_type(block.type))
    out_branch_id, is_new_next_block, allow_fails, next_blocks, set_explained, bl_created_paths = updated_branches(
        sc,
        entry,
        new_values,
        block_id,
        is_new_block,
        block.output_var,
        branch_id,
        t_id,
        !isa(block.p, FreeVar),
        fixed_branches,
        created_paths,
    )

    out_branches = Dict{UInt64,UInt64}(block.output_var => out_branch_id)
    block_created_paths = Dict{UInt64,Vector{Any}}(out_branch_id => bl_created_paths)
    if set_explained && !sc.branch_known_from_input[out_branch_id]
        sc.branch_known_from_input[out_branch_id] =
            any(sc.branch_known_from_input[fixed_branches[in_var]] for in_var in block.input_vars)
    end
    return out_branches, is_new_next_block, allow_fails, next_blocks, set_explained, block_created_paths
end

function value_updates(
    sc,
    block::Union{ReverseProgramBlock,WrapEitherBlock},
    block_id,
    target_output::Dict{UInt64,UInt64},
    new_values,
    fixed_branches::Dict{UInt64,UInt64},
    is_new_block,
    created_paths,
)
    out_branches = Dict{UInt64,UInt64}()
    is_new_next_block = false
    allow_fails = false
    set_explained = false
    next_blocks = Set()
    block_created_paths = Dict{UInt64,Vector{Any}}()
    for i in 1:length(block.output_vars)
        out_var = block.output_vars[i]
        values = new_values[i]
        br_id = target_output[out_var]
        entry = sc.entries[sc.branch_entries[br_id]]
        out_branch_id, is_new_nxt_block, all_fails, n_blocks, set_expl, bl_created_paths = updated_branches(
            sc,
            entry,
            values,
            block_id,
            is_new_block,
            out_var,
            br_id,
            entry.type_id,
            true,
            fixed_branches,
            created_paths,
        )
        is_new_next_block |= is_new_nxt_block
        out_branches[out_var] = out_branch_id
        allow_fails |= all_fails
        set_explained |= set_expl
        union!(next_blocks, n_blocks)
        block_created_paths[out_branch_id] = bl_created_paths
    end
    if set_explained
        known_from_input = any(sc.branch_known_from_input[fixed_branches[in_var]] for in_var in block.input_vars)
        for (_, branch_id) in out_branches
            if length(out_branches) > 1
                inds = [b_id for (_, b_id) in out_branches if b_id != branch_id]
                sc.related_explained_complexity_branches[branch_id, inds] = 1
            end
            if !sc.branch_known_from_input[branch_id]
                sc.branch_known_from_input[branch_id] = known_from_input
            end
        end
    end
    return out_branches, is_new_next_block, allow_fails, next_blocks, set_explained, block_created_paths
end

function updated_branches(
    sc,
    entry::ValueEntry,
    @nospecialize(new_values),
    block_id,
    is_new_block,
    var_id::UInt64,
    branch_id::UInt64,
    t_id::UInt64,
    is_meaningful::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)
    if is_meaningful && sc.branch_is_not_copy[branch_id] != true
        sc.branch_is_not_copy[branch_id] = true
    end
    set_explained = false
    if !sc.branch_is_explained[branch_id]
        sc.branch_is_explained[branch_id] = true
        sc.unused_explained_complexities[branch_id] = entry.complexity
        set_explained = true
    end
    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, branch_id, fixed_branches)
    if isempty(block_created_paths)
        allow_fails = false
        next_blocks = Set()
    else
        allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, branch_id, fixed_branches)
    end
    return branch_id, false, allow_fails, next_blocks, set_explained, block_created_paths
end

function find_related_branches(sc, branch_id, new_entry, new_entry_index)::Tuple{Vector{UInt64},Union{UInt64,Nothing}}
    possible_parents = UInt64[]
    for child_id in nonzeroinds(sc.branch_children[branch_id, :])
        if sc.branch_entries[child_id] == new_entry_index
            return UInt64[], child_id
        else
            child_entry = sc.entries[sc.branch_entries[child_id]]
            if match_with_entry(sc, child_entry, new_entry)
                parents, possible_result = find_related_branches(sc, child_id, new_entry, new_entry_index)
                if !isnothing(possible_result)
                    return UInt64[], possible_result
                else
                    append!(possible_parents, parents)
                end
            end
        end
    end
    if isempty(possible_parents)
        return UInt64[branch_id], nothing
    else
        return possible_parents, nothing
    end
end

function updated_branches(
    sc,
    entry::NoDataEntry,
    @nospecialize(new_values),
    block_id,
    is_new_block,
    var_id::UInt64,
    branch_id::UInt64,
    t_id::UInt64,
    is_meaningful::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)
    complexity_summary = get_complexity_summary(new_values, sc.types[t_id])
    new_entry = ValueEntry(t_id, new_values, complexity_summary, get_complexity(sc, complexity_summary))
    new_entry_index = push!(sc.entries, new_entry)
    new_parents, possible_result = find_related_branches(sc, branch_id, new_entry, new_entry_index)
    parent_constraints = nonzeroinds(sc.constrained_branches[branch_id, :])
    if !isnothing(possible_result)
        set_explained = false
        if !sc.branch_is_explained[possible_result]
            sc.branch_is_explained[possible_result] = true
            set_explained = true
        end
        block_created_paths =
            get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, possible_result, fixed_branches)
        if isempty(block_created_paths)
            allow_fails = false
            next_blocks = Set()
        else
            allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, possible_result, fixed_branches)
        end
        return possible_result, false, allow_fails, next_blocks, set_explained, block_created_paths
    end

    new_branch_id = increment!(sc.branches_count)
    sc.branch_entries[new_branch_id] = new_entry_index
    sc.branch_vars[new_branch_id] = var_id
    sc.branch_types[new_branch_id, t_id] = t_id
    sc.branch_is_explained[new_branch_id] = true
    if is_meaningful
        sc.branch_is_not_copy[new_branch_id] = true
    end

    sc.branch_children[new_parents, new_branch_id] = 1
    sc.complexities[new_branch_id] = new_entry.complexity
    sc.unused_explained_complexities[new_branch_id] = new_entry.complexity

    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, new_branch_id, fixed_branches)
    if !isempty(parent_constraints)
        for constraint_id in parent_constraints
            tighten_constraint(sc, constraint_id, new_branch_id, branch_id)
        end
        if isempty(block_created_paths)
            allow_fails = false
            next_blocks = Set()
        else
            allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, new_branch_id, fixed_branches)
        end
    else
        allow_fails, next_blocks = _downstream_blocks_new_branch(sc, var_id, branch_id, new_branch_id, fixed_branches)
    end
    return new_branch_id, true, allow_fails, next_blocks, true, block_created_paths
end

function updated_branches(
    sc,
    entry::EitherEntry,
    @nospecialize(new_values),
    block_id,
    is_new_block,
    var_id::UInt64,
    branch_id::UInt64,
    t_id::UInt64,
    is_meaningful::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)
    complexity_summary = get_complexity_summary(new_values, sc.types[t_id])
    new_entry = ValueEntry(t_id, new_values, complexity_summary, get_complexity(sc, complexity_summary))
    new_entry_index = push!(sc.entries, new_entry)
    new_parents, possible_result = find_related_branches(sc, branch_id, new_entry, new_entry_index)
    parent_constraints = nonzeroinds(sc.constrained_branches[branch_id, :])
    if !isnothing(possible_result)
        set_explained = false
        if !sc.branch_is_explained[possible_result]
            sc.branch_is_explained[possible_result] = true
            set_explained = true
        end
        if is_meaningful && sc.branch_is_not_copy[possible_result] != true
            sc.branch_is_not_copy[possible_result] = true
        end
        block_created_paths =
            get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, possible_result, fixed_branches)
        if isempty(block_created_paths)
            allow_fails = false
            next_blocks = Set()
        else
            allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, possible_result, fixed_branches)
        end
        return possible_result, false, allow_fails, next_blocks, set_explained, block_created_paths
    end

    new_branch_id = increment!(sc.branches_count)
    sc.branch_entries[new_branch_id] = new_entry_index
    sc.branch_vars[new_branch_id] = var_id
    sc.branch_types[new_branch_id, t_id] = t_id
    sc.branch_is_explained[new_branch_id] = true
    if is_meaningful
        sc.branch_is_not_copy[new_branch_id] = true
    end

    sc.branch_children[new_parents, new_branch_id] = 1
    sc.complexities[new_branch_id] = new_entry.complexity
    sc.unused_explained_complexities[new_branch_id] = new_entry.complexity
    sc.unmatched_complexities[new_branch_id] = new_entry.complexity

    if isempty(parent_constraints)
        error("Either branch doesn't have constraints")
    end
    for constraint_id in parent_constraints
        tighten_constraint(sc, constraint_id, new_branch_id, branch_id)
    end
    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, new_branch_id, fixed_branches)
    if isempty(block_created_paths)
        allow_fails = false
        next_blocks = Set()
    else
        allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, new_branch_id, fixed_branches)
    end
    return new_branch_id, false, allow_fails, next_blocks, true, block_created_paths
end

function _downstream_branch_options_known(sc, block_id, block_copy_id, fixed_branches, unfixed_vars)
    inp_branches = nonzeroinds(sc.branch_outgoing_blocks[:, block_copy_id])
    all_inputs = Dict(v => b for (v, b) in zip(sc.branch_vars[inp_branches], inp_branches))
    for (v, b) in all_inputs
        if haskey(fixed_branches, v) && sc.branch_is_explained[b] && fixed_branches[v] != b
            return false, Set(), Set()
        end
    end
    out_branches = nonzeroinds(sc.branch_incoming_blocks[:, block_copy_id])
    target_output = Dict(v => b for (v, b) in zip(sc.branch_vars[out_branches], out_branches))
    if isempty(unfixed_vars)
        return false, Set([(block_id, fixed_branches, target_output)]), Set()
    end
    # @info fixed_branches
    # @info unfixed_vars
    inputs = Dict(v => b for (v, b) in all_inputs if in(v, unfixed_vars))
    new_fixed_branches = merge(fixed_branches, inputs)
    if all(e == true for e in sc.branch_is_explained[collect(values(inputs))])
        return false, Set([(block_id, new_fixed_branches, target_output)]), Set()
    end
    allow_fails = false
    for var_id in unfixed_vars
        br_id = inputs[var_id]
        if !sc.branch_is_explained[br_id] && isa(sc.entries[sc.branch_entries[br_id]], NoDataEntry)
            allow_fails = true
            break
        end
    end
    return allow_fails, Set(), Set([(block_id, new_fixed_branches, UInt64[b_id for (_, b_id) in target_output])])
end

function _downstream_blocks_existing_branch(sc, var_id, out_branch_id, fixed_branches)
    allow_fails = false
    outputs = Set()
    fixed_branches = merge(fixed_branches, Dict(var_id => out_branch_id))
    next_blocks = unique(zip(findnz(sc.branch_outgoing_blocks[out_branch_id, :])...))
    for (b_copy_id, b_id) in next_blocks
        block = sc.blocks[b_id]
        unfixed_vars = [v_id for v_id in block.input_vars if !haskey(fixed_branches, v_id)]
        allow_block_fails, block_options, unfixed_options =
            _downstream_branch_options_known(sc, b_id, b_copy_id, fixed_branches, unfixed_vars)
        allow_fails |= allow_block_fails
        union!(outputs, block_options)
        # union!(unexplained_options, unfixed_options)
    end

    # @info allow_fails
    # @info outputs
    return allow_fails, outputs
end

function _downstream_blocks_new_branch(sc, var_id, target_branch_id, out_branch_id, fixed_branches)
    allow_fails = false
    outputs = Set()
    fixed_branches = merge(fixed_branches, Dict(var_id => out_branch_id))

    next_blocks = unique(zip(findnz(sc.branch_outgoing_blocks[target_branch_id, :])...))
    unexplained_options = Set()
    for (b_copy_id, b_id) in next_blocks
        block = sc.blocks[b_id]
        unfixed_vars = [v_id for v_id in block.input_vars if !haskey(fixed_branches, v_id)]
        allow_block_fails, block_options, unfixed_options =
            _downstream_branch_options_known(sc, b_id, b_copy_id, fixed_branches, unfixed_vars)
        allow_fails |= allow_block_fails
        union!(outputs, block_options)
        union!(unexplained_options, unfixed_options)
    end
    for (b_id, inp_branches, target_branches) in unexplained_options
        _save_block_branch_connections(sc, b_id, sc.blocks[b_id], inp_branches, target_branches)
    end
    # @info allow_fails
    # @info outputs
    return allow_fails, outputs
end

function _save_block_branch_connections(sc, block_id, block, fixed_branches, out_branches)
    input_br_ids = UInt64[fixed_branches[var_id] for var_id in block.input_vars]
    existing_outgoing = DefaultDict{UInt64,Int}(() -> 0)
    for (_, bl_copy_id, bl_id) in zip(findnz(sc.branch_outgoing_blocks[input_br_ids, :])...)
        if bl_id == block_id
            existing_outgoing[bl_copy_id] += 1
        end
    end
    for (bl_copy_id, count) in existing_outgoing
        if count != length(input_br_ids)
            continue
        end
        if Vector{UInt64}(nonzeroinds(sc.branch_incoming_blocks[:, bl_copy_id])) == out_branches
            if sc.verbose
                @info "Block $block_id $block already has connections for inputs $input_br_ids and outputs $out_branches"
            end
            throw(EnumerationException())
        end
    end

    block_copy_id = increment!(sc.block_copies_count)
    sc.branch_outgoing_blocks[input_br_ids, block_copy_id] = block_id
    sc.branch_incoming_blocks[out_branches, block_copy_id] = block_id
    if sc.verbose
        @info "Created new block copy $block_copy_id for block $block_id $block with inputs $input_br_ids and outputs $out_branches"
    end
end
