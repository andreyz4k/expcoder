
function get_all_parents(sc, branch_id)
    parents = get_connected_to(sc.branch_children, branch_id)
    for parent_id in parents
        parents = union(parents, get_all_parents(sc, parent_id))
    end
    return parents
end

function get_root_parent(sc, branch_id)
    parents = get_connected_to(sc.branch_children, branch_id)
    for parent_id in parents
        return get_root_parent(sc, parent_id)
    end
    return branch_id
end

function get_all_children(sc, branch_id)
    children = get_connected_from(sc.branch_children, branch_id)
    for child_id in children
        children = union(children, get_all_children(sc, child_id))
    end
    return children
end

function is_child_branch(sc, branch_id, child_id)
    children = get_connected_from(sc.branch_children, branch_id)
    if in(child_id, children)
        return true
    end
    for child in children
        if is_child_branch(sc, child, child_id)
            return true
        end
    end
    return false
end

function value_updates(
    sc,
    block::ProgramBlock,
    block_id,
    update_type,
    target_output::Dict{UInt64,UInt64},
    new_values,
    fixed_branches::Dict{UInt64,UInt64},
    is_new_block,
    created_paths,
)
    branch_id = target_output[block.output_var]
    entry = sc.entries[sc.branch_entries[branch_id]]
    t_id = push!(sc.types, update_type)
    out_branch_id, is_new_out_branch, is_new_next_block, allow_fails, next_blocks, set_explained, bl_created_paths =
        updated_branches(
            sc,
            entry,
            new_values,
            block_id,
            is_new_block,
            block.output_var,
            branch_id,
            t_id,
            !isa(block.p, FreeVar),
            !isa(block.p, SetConst) &&
            !(isa(block.p, FreeVar) && !sc.branch_is_not_const[fixed_branches[block.input_vars[1]]]),
            fixed_branches,
            created_paths,
        )

    out_branches = Dict{UInt64,UInt64}(block.output_var => out_branch_id)
    block_created_paths = Dict{UInt64,Vector{Any}}(out_branch_id => bl_created_paths)
    if set_explained && !sc.branch_known_from_input[out_branch_id]
        sc.branch_known_from_input[out_branch_id] =
            any(sc.branch_known_from_input[fixed_branches[in_var]] for in_var in block.input_vars)
    end
    return out_branches,
    is_new_out_branch,
    is_new_next_block,
    allow_fails,
    next_blocks,
    set_explained,
    block_created_paths
end

function value_updates(
    sc,
    block::ReverseProgramBlock,
    block_id,
    block_type,
    target_output::Dict{UInt64,UInt64},
    new_values,
    fixed_branches::Dict{UInt64,UInt64},
    is_new_block,
    created_paths,
)
    out_branches = Dict{UInt64,UInt64}()
    is_new_out_branch = false
    is_new_next_block = false
    allow_fails = false
    set_explained = false
    next_blocks = Set()
    block_created_paths = Dict{UInt64,Vector{Any}}()
    out_types = Dict(arguments_of_type(block_type))
    for i in 1:length(block.output_vars)
        out_var = block.output_vars[i]
        values = new_values[i]
        br_id = target_output[out_var]
        entry = sc.entries[sc.branch_entries[br_id]]
        _, out_type = instantiate(out_types[out_var], empty_context)
        t_id = push!(sc.types, out_type)
        out_branch_id, is_new_out_branch_, is_new_nxt_block, all_fails, n_blocks, set_expl, bl_created_paths =
            updated_branches(
                sc,
                entry,
                values,
                block_id,
                is_new_block,
                out_var,
                br_id,
                t_id,
                true,
                true,
                fixed_branches,
                created_paths,
            )
        is_new_out_branch |= is_new_out_branch_
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
                sc.related_explained_complexity_branches[branch_id, inds] = true
            end
            if !sc.branch_known_from_input[branch_id]
                sc.branch_known_from_input[branch_id] = known_from_input
            end
        end
    end
    return out_branches,
    is_new_out_branch,
    is_new_next_block,
    allow_fails,
    next_blocks,
    set_explained,
    block_created_paths
end

function _updates_for_existing_branch(
    sc,
    entry,
    branch_id,
    block_id,
    is_new_block,
    created_paths,
    var_id,
    fixed_branches,
    is_not_copy,
    is_not_const,
)
    set_explained = false
    if !sc.branch_is_explained[branch_id]
        sc.branch_is_explained[branch_id] = true
        sc.unused_explained_complexities[branch_id] = entry.complexity
        set_explained = true
    end
    if is_not_copy && sc.branch_is_not_copy[branch_id] != true
        sc.branch_is_not_copy[branch_id] = true
    end
    if is_not_const && sc.branch_is_not_const[branch_id] != true
        sc.branch_is_not_const[branch_id] = true
    end
    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, branch_id, fixed_branches)
    if isempty(block_created_paths)
        if is_new_block || set_explained
            throw(EnumerationException("No valid paths for new block"))
        else
            allow_fails = false
            next_blocks = Set()
        end
    else
        allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, branch_id, fixed_branches)
    end
    return branch_id, false, false, allow_fails, next_blocks, set_explained, block_created_paths
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
    is_not_copy::Bool,
    is_not_const::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)::Tuple{UInt64,Bool,Bool,Bool,Set{Any},Bool,Vector{Any}}
    return _updates_for_existing_branch(
        sc,
        entry,
        branch_id,
        block_id,
        is_new_block,
        created_paths,
        var_id,
        fixed_branches,
        is_not_copy,
        is_not_const,
    )
end

function find_related_branches(sc, var_id, new_entry, new_entry_id)
    var_branches = get_connected_to(sc.branch_vars, var_id)
    if sc.verbose
        @info "Var branches $var_branches"
    end

    parents = Set{UInt64}()
    skip_parents = Set{UInt64}()
    children = Set{UInt64}()
    skip_children = Set{UInt64}()
    for branch_id in var_branches
        old_entry_id = sc.branch_entries[branch_id]
        if old_entry_id == new_entry_id
            return branch_id, Set()
        end
        old_entry = sc.entries[old_entry_id]

        if is_parent_entry(sc, old_entry, new_entry)
            branch_children = get_connected_from(sc.branch_children, branch_id)
            if any(in(c, parents) for c in branch_children)
                push!(skip_parents, branch_id)
            end
            branch_parents = get_connected_to(sc.branch_children, branch_id)
            for p in parents
                if in(p, branch_parents)
                    push!(skip_parents, p)
                end
            end
            push!(parents, branch_id)
        elseif is_child_entry(sc, old_entry, new_entry)
            branch_parents = get_connected_to(sc.branch_children, branch_id)
            if any(in(p, children) for p in branch_parents)
                push!(skip_children, branch_id)
            end
            branch_children = get_connected_from(sc.branch_children, branch_id)
            for c in children
                if in(c, branch_children)
                    push!(skip_children, c)
                end
            end
            push!(children, branch_id)
        end
    end
    setdiff!(parents, skip_parents)
    setdiff!(children, skip_children)
    parents_children = Set{Tuple{Union{UInt64,Nothing},Vector{UInt64}}}()
    checked_children = Set{UInt64}()
    for p in parents
        all_branch_children = get_connected_from(sc.branch_children, p)
        branch_children = UInt64[]
        for c in children
            if in(c, all_branch_children)
                push!(branch_children, c)
                push!(checked_children, c)
            end
        end
        push!(parents_children, (p, branch_children))
    end
    for c in children
        if !in(c, checked_children)
            push!(parents_children, (nothing, [c]))
        end
    end
    if sc.verbose
        @info "Parents children $parents_children"
    end
    return nothing, parents_children
end

function is_parent_entry(sc, old_entry::NoDataEntry, new_entry::NoDataEntry)
    return is_subtype(sc.types[old_entry.type_id], sc.types[new_entry.type_id])
end

function is_child_entry(sc, old_entry::NoDataEntry, new_entry::NoDataEntry)
    return is_subtype(sc.types[new_entry.type_id], sc.types[old_entry.type_id])
end

function is_parent_entry(sc, old_entry::NoDataEntry, new_entry)
    return is_subtype(sc.types[old_entry.type_id], sc.types[new_entry.type_id])
end

function is_child_entry(sc, old_entry::NoDataEntry, new_entry)
    return false
end

function is_parent_entry(sc, old_entry, new_entry::NoDataEntry)
    return false
end

function is_child_entry(sc, old_entry, new_entry::NoDataEntry)
    return is_subtype(sc.types[new_entry.type_id], sc.types[old_entry.type_id])
end

function is_parent_entry(sc, old_entry::Union{PatternEntry,AbductibleEntry}, new_entry::EitherEntry)
    return is_subtype(sc.types[old_entry.type_id], sc.types[new_entry.type_id]) &&
           all(is_subeither(old_val, new_val) for (new_val, old_val) in zip(new_entry.values, old_entry.values))
end

function is_child_entry(sc, old_entry::Union{PatternEntry,AbductibleEntry}, new_entry::EitherEntry)
    return !is_parent_entry(sc, old_entry, new_entry) &&
           is_subtype(sc.types[new_entry.type_id], sc.types[old_entry.type_id]) &&
           all(is_subeither(new_val, old_val) for (new_val, old_val) in zip(new_entry.values, old_entry.values))
end

function is_parent_entry(sc, old_entry::EitherEntry, new_entry::Union{PatternEntry,AbductibleEntry})
    return !is_child_entry(sc, old_entry, new_entry) &&
           is_subtype(sc.types[old_entry.type_id], sc.types[new_entry.type_id]) &&
           all(is_subeither(old_val, new_val) for (new_val, old_val) in zip(new_entry.values, old_entry.values))
end

function is_child_entry(sc, old_entry::EitherEntry, new_entry::Union{PatternEntry,AbductibleEntry})
    return is_subtype(sc.types[new_entry.type_id], sc.types[new_entry.type_id]) &&
           all(is_subeither(new_val, old_val) for (new_val, old_val) in zip(new_entry.values, old_entry.values))
end

function is_parent_entry(sc, old_entry, new_entry)
    return is_subtype(sc.types[old_entry.type_id], sc.types[new_entry.type_id]) &&
           all(is_subeither(old_val, new_val) for (new_val, old_val) in zip(new_entry.values, old_entry.values))
end

function is_child_entry(sc, old_entry, new_entry)
    return is_subtype(sc.types[new_entry.type_id], sc.types[old_entry.type_id]) &&
           all(is_subeither(new_val, old_val) for (new_val, old_val) in zip(new_entry.values, old_entry.values))
end

function _setup_new_branch(
    sc,
    new_entry,
    new_entry_index,
    var_id,
    t_id,
    is_not_copy,
    is_not_const,
    new_parents_children,
    set_unmatched_complexity = true,
)
    new_branch_id = increment!(sc.branches_count)
    sc.branch_creation_iterations[new_branch_id] = sc.iterations_count
    sc.branch_entries[new_branch_id] = new_entry_index
    sc.branch_vars[new_branch_id] = var_id
    sc.branch_types[new_branch_id] = t_id
    sc.branch_is_explained[new_branch_id] = true
    if is_not_copy
        sc.branch_is_not_copy[new_branch_id] = true
    end
    if is_not_const
        sc.branch_is_not_const[new_branch_id] = true
    end

    for (parent, children) in new_parents_children
        if !isnothing(parent)
            deleteat!(sc.branch_children, [parent], children)
            sc.branch_children[parent, new_branch_id] = true
        end
        sc.branch_children[new_branch_id, children] = true
    end
    sc.complexities[new_branch_id] = new_entry.complexity
    sc.unused_explained_complexities[new_branch_id] = new_entry.complexity
    if set_unmatched_complexity
        sc.unmatched_complexities[new_branch_id] = new_entry.complexity
    end

    has_constrained_parents = false

    for parent_id in get_all_parents(sc, new_branch_id)
        if !isempty(get_connected_from(sc.constrained_branches, parent_id))
            has_constrained_parents = true
            tighten_constraint(sc, new_branch_id, parent_id)
        end
    end

    return new_branch_id, has_constrained_parents
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
    is_not_copy::Bool,
    is_not_const::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)::Tuple{UInt64,Bool,Bool,Bool,Set{Any},Bool,Vector{Any}}
    new_entry, new_entry_index = make_entry(sc, t_id, new_values)
    possible_result, new_parents_children = find_related_branches(sc, var_id, new_entry, new_entry_index)
    if !isnothing(possible_result)
        return _updates_for_existing_branch(
            sc,
            new_entry,
            possible_result,
            block_id,
            is_new_block,
            created_paths,
            var_id,
            fixed_branches,
            is_not_copy,
            is_not_const,
        )
    end

    new_branch_id, has_constrained_parents = _setup_new_branch(
        sc,
        new_entry,
        new_entry_index,
        var_id,
        t_id,
        is_not_copy,
        is_not_const,
        new_parents_children,
        false,
    )

    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, new_branch_id, fixed_branches)
    if isempty(block_created_paths)
        throw(EnumerationException("No valid paths for new block"))
    end
    if has_constrained_parents
        allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, new_branch_id, fixed_branches)
    else
        allow_fails, next_blocks = _downstream_blocks_new_branch(sc, var_id, new_branch_id, fixed_branches)
    end
    return new_branch_id, true, true, allow_fails, next_blocks, true, block_created_paths
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
    is_not_copy::Bool,
    is_not_const::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)::Tuple{UInt64,Bool,Bool,Bool,Set{Any},Bool,Vector{Any}}
    new_entry, new_entry_index = make_entry(sc, t_id, new_values)
    possible_result, new_parents_children = find_related_branches(sc, var_id, new_entry, new_entry_index)
    # @info "Either branch $branch_id"
    # @info "New entry $new_entry"
    # @info "Possible result $possible_result"
    # @info "New parents children $new_parents_children"
    if !isnothing(possible_result)
        return _updates_for_existing_branch(
            sc,
            new_entry,
            possible_result,
            block_id,
            is_new_block,
            created_paths,
            var_id,
            fixed_branches,
            is_not_copy,
            is_not_const,
        )
    end

    new_branch_id, has_constrained_parents =
        _setup_new_branch(sc, new_entry, new_entry_index, var_id, t_id, is_not_copy, is_not_const, new_parents_children)

    if !has_constrained_parents
        error("Either branch doesn't have constraints")
    end

    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, new_branch_id, fixed_branches)
    if isempty(block_created_paths)
        throw(EnumerationException("No valid paths for new block"))
    end

    allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, new_branch_id, fixed_branches)
    return new_branch_id, false, false, allow_fails, next_blocks, true, block_created_paths
end

function updated_branches(
    sc,
    entry::PatternEntry,
    @nospecialize(new_values),
    block_id,
    is_new_block,
    var_id::UInt64,
    branch_id::UInt64,
    t_id::UInt64,
    is_not_copy::Bool,
    is_not_const::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)::Tuple{UInt64,Bool,Bool,Bool,Set{Any},Bool,Vector{Any}}
    new_entry, new_entry_index = make_entry(sc, t_id, new_values)
    possible_result, new_parents_children = find_related_branches(sc, var_id, new_entry, new_entry_index)
    if !isnothing(possible_result)
        return _updates_for_existing_branch(
            sc,
            new_entry,
            possible_result,
            block_id,
            is_new_block,
            created_paths,
            var_id,
            fixed_branches,
            is_not_copy,
            is_not_const,
        )
    end

    new_branch_id, has_constrained_parents =
        _setup_new_branch(sc, new_entry, new_entry_index, var_id, t_id, is_not_copy, is_not_const, new_parents_children)

    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, new_branch_id, fixed_branches)
    if isempty(block_created_paths)
        throw(EnumerationException("No valid paths for new block"))
    end
    if has_constrained_parents
        allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, new_branch_id, fixed_branches)
    else
        allow_fails, next_blocks = _downstream_blocks_new_branch(sc, var_id, new_branch_id, fixed_branches)
    end
    return new_branch_id, true, true, allow_fails, next_blocks, true, block_created_paths
end

function _get_abducted_values(sc, out_block_id, branches)
    out_block = sc.blocks[out_block_id]
    in_entries = Dict(var_id => sc.entries[sc.branch_entries[branches[var_id]]] for var_id in out_block.input_vars)
    out_entry = sc.entries[sc.branch_entries[branches[out_block.output_var]]]

    updated_branches = DefaultDict{UInt64,Vector}(() -> [])
    for i in 1:sc.example_count
        updated_values = try_run_function(
            calculate_dependent_vars,
            [
                out_block.p,
                Dict{UInt64,Any}(
                    var_id => entry.values[i] for
                    (var_id, entry) in in_entries if !isa(entry.values[i], AbductibleValue)
                ),
                out_entry.values[i],
                out_block_id,
            ],
        )
        if isnothing(updated_values)
            throw(EnumerationException())
        end
        for (var_id, entry) in in_entries
            if haskey(updated_values, var_id)
                push!(updated_branches[var_id], updated_values[var_id])
            else
                push!(updated_branches[var_id], entry.values[i])
            end
        end
    end
    # @info "Block: $out_block"
    # @info "In entries: $in_entries"
    # @info "Out entry: $out_entry"
    # @info "Updated branches from block: $updated_branches"
    return updated_branches
end

function _abduct_next_block(sc, out_block_copy_id, out_block_id, new_branch_id, var_id, branch_id)
    branch_ids = vcat(
        collect(keys(get_connected_to(sc.branch_outgoing_blocks, out_block_copy_id))),
        collect(keys(get_connected_to(sc.branch_incoming_blocks, out_block_copy_id))),
    )
    old_branches = Dict{UInt64,UInt64}(sc.branch_vars[b_id] => b_id for b_id in branch_ids)

    old_branches[var_id] = new_branch_id

    updated_values = _get_abducted_values(sc, out_block_id, old_branches)

    new_branches = Dict{UInt64,UInt64}()
    out_branches = Dict{UInt64,UInt64}()

    new_branches[branch_id] = new_branch_id
    out_branches[branch_id] = new_branch_id

    either_branch_ids = UInt64[]

    for (v_id, b_id) in old_branches
        if haskey(updated_values, v_id)
            old_br_entry = sc.entries[sc.branch_entries[b_id]]
            # @info old_br_entry

            new_br_entry, new_entry_index = make_entry(sc, old_br_entry.type_id, updated_values[v_id])
            # @info new_br_entry
            exact_match, parents_children = find_related_branches(sc, v_id, new_br_entry, new_entry_index)
            if !isnothing(exact_match)
                if isa(new_br_entry, EitherEntry)
                    push!(either_branch_ids, exact_match)
                end
                out_branches[b_id] = exact_match
            else
                created_branch_id = increment!(sc.branches_count)
                sc.branch_creation_iterations[created_branch_id] = sc.iterations_count
                sc.branch_entries[created_branch_id] = new_entry_index
                sc.branch_vars[created_branch_id] = v_id
                sc.branch_types[created_branch_id] = new_br_entry.type_id
                if sc.branch_is_unknown[b_id]
                    sc.branch_is_unknown[created_branch_id] = true
                    sc.branch_unknown_from_output[created_branch_id] = sc.branch_unknown_from_output[b_id]
                end

                for (parent, children) in parents_children
                    if !isnothing(parent)
                        deleteat!(sc.branch_children, [parent], children)
                        sc.branch_children[parent, created_branch_id] = true
                    end
                    sc.branch_children[created_branch_id, children] = true
                end

                original_path_cost = sc.unknown_min_path_costs[b_id]
                if !isnothing(original_path_cost)
                    sc.unknown_min_path_costs[created_branch_id] = original_path_cost
                end
                sc.complexities[created_branch_id] = new_br_entry.complexity
                sc.unmatched_complexities[created_branch_id] = new_br_entry.complexity

                if isa(new_br_entry, EitherEntry)
                    push!(either_branch_ids, created_branch_id)
                end
                out_branches[b_id] = created_branch_id
                new_branches[b_id] = created_branch_id
            end
        end
    end

    for (old_br_id, new_br_id) in new_branches
        if sc.branch_is_unknown[new_br_id]
            old_related_branches = get_connected_from(sc.related_unknown_complexity_branches, old_br_id)
            new_related_branches =
                UInt64[(haskey(new_branches, b_id) ? new_branches[b_id] : b_id) for b_id in old_related_branches]
            sc.related_unknown_complexity_branches[new_br_id, new_related_branches] = true
            sc.unknown_complexity_factors[new_br_id] = branch_complexity_factor_unknown(sc, new_br_id)
        end
    end

    unknown_old_branches = UInt64[br_id for (br_id, _) in new_branches]
    next_blocks = merge([get_connected_from(sc.branch_outgoing_blocks, br_id) for br_id in unknown_old_branches]...)
    for (b_copy_id, b_id) in next_blocks
        inp_branches = keys(get_connected_to(sc.branch_outgoing_blocks, b_copy_id))
        inputs = Dict(sc.branch_vars[b] => haskey(out_branches, b) ? out_branches[b] : b for b in inp_branches)
        out_block_branches = keys(get_connected_to(sc.branch_incoming_blocks, b_copy_id))
        target_branches = UInt64[haskey(out_branches, b) ? out_branches[b] : b for b in out_block_branches]

        following_entries = union([get_connected_from(sc.branch_foll_entries, b) for b in target_branches]...)
        union!(following_entries, [sc.branch_entries[b] for b in target_branches])

        if any(in(sc.branch_entries[b], following_entries) for b in values(inputs))
            if sc.verbose
                @info "Fixing constraint leads to a redundant block"
            end
            throw(EnumerationException("Fixing constraint leads to a redundant block"))
        end

        _save_block_branch_connections(sc, b_id, sc.blocks[b_id], inputs, target_branches)
        for target_branch in target_branches
            update_complexity_factors_unknown(sc, inputs, target_branch)
        end
    end

    if !isempty(either_branch_ids)
        constrained_branches =
            union([get_connected_from(sc.constrained_branches, br_id) for br_id in either_branch_ids]...)
        if sc.verbose
            @info "Adding constraint on abduct with new branches $either_branch_ids and old $constrained_branches"
        end
        constrained_branches = union(constrained_branches, either_branch_ids)
        sc.constrained_branches[constrained_branches, constrained_branches] = true
    end
end

function updated_branches(
    sc,
    entry::AbductibleEntry,
    @nospecialize(new_values),
    block_id,
    is_new_block,
    var_id::UInt64,
    branch_id::UInt64,
    t_id::UInt64,
    is_not_copy::Bool,
    is_not_const::Bool,
    fixed_branches::Dict{UInt64,UInt64},
    created_paths,
)::Tuple{UInt64,Bool,Bool,Bool,Set{Any},Bool,Vector{Any}}
    new_entry, new_entry_index = make_entry(sc, t_id, new_values)
    possible_result, new_parents_children = find_related_branches(sc, var_id, new_entry, new_entry_index)
    if !isnothing(possible_result)
        return _updates_for_existing_branch(
            sc,
            new_entry,
            possible_result,
            block_id,
            is_new_block,
            created_paths,
            var_id,
            fixed_branches,
            is_not_copy,
            is_not_const,
        )
    end

    new_branch_id, has_constrained_parents =
        _setup_new_branch(sc, new_entry, new_entry_index, var_id, t_id, is_not_copy, is_not_const, new_parents_children)

    out_blocks = get_connected_from(sc.branch_outgoing_blocks, branch_id)

    for (out_block_copy_id, out_block_id) in out_blocks
        _abduct_next_block(sc, out_block_copy_id, out_block_id, new_branch_id, var_id, branch_id)
    end

    block_created_paths =
        get_new_paths_for_block(sc, block_id, is_new_block, created_paths, var_id, new_branch_id, fixed_branches)
    if isempty(block_created_paths)
        throw(EnumerationException("No valid paths for new block"))
    end

    allow_fails, next_blocks = _downstream_blocks_existing_branch(sc, var_id, new_branch_id, fixed_branches)
    return new_branch_id, true, false, allow_fails, next_blocks, true, block_created_paths
end

function _downstream_branch_options_known(sc, block_id, block_copy_id, fixed_branches, unfixed_vars)
    inp_branches = keys(get_connected_to(sc.branch_outgoing_blocks, block_copy_id))
    all_inputs = Dict(sc.branch_vars[b] => b for b in inp_branches)
    for (v, b) in all_inputs
        if haskey(fixed_branches, v) && sc.branch_is_explained[b] && fixed_branches[v] != b
            return false, Set(), Set()
        end
    end
    out_branches = keys(get_connected_to(sc.branch_incoming_blocks, block_copy_id))
    target_output = Dict{UInt64,UInt64}(sc.branch_vars[b] => b for b in out_branches)
    if isempty(unfixed_vars)
        return false, Set([(block_id, fixed_branches, target_output)]), Set()
    end
    # @info "Fixed branches $fixed_branches"
    # @info unfixed_vars
    inputs = Dict(v => b for (v, b) in all_inputs if in(v, unfixed_vars))
    new_fixed_branches = merge(fixed_branches, inputs)
    # @info "New fixed branches $new_fixed_branches"
    if all(sc.branch_is_explained[br_id] for br_id in values(inputs))
        return false, Set([(block_id, new_fixed_branches, target_output)]), Set()
    end

    block = sc.blocks[block_id]
    block_type = sc.types[block.type_id]
    if is_polymorphic(block_type)
        context, block_type = instantiate(block_type, empty_context)
        if isa(block, ProgramBlock)
            inp_types = Dict{UInt64,Tp}()
            for (var_id, var_tp) in arguments_of_type(block_type)
                context, v_tp = instantiate(sc.types[sc.branch_types[new_fixed_branches[var_id]]], context)
                if haskey(inputs, var_id)
                    inp_types[var_id] = v_tp
                end
                context = unify(context, var_tp, v_tp)
            end
            new_branches = Dict{UInt64,UInt64}()
            for (var_id, br_id) in inputs
                branch_type = sc.types[sc.branch_types[br_id]]
                context, new_branch_type = apply_context(context, inp_types[var_id])
                _, new_branch_type = instantiate(new_branch_type, empty_context)
                if new_branch_type != branch_type
                    entry = sc.entries[sc.branch_entries[br_id]]
                    new_type_id = push!(sc.types, new_branch_type)
                    if isa(entry, NoDataEntry)
                        new_entry = NoDataEntry(new_type_id)
                        new_entry_id = push!(sc.entries, new_entry)
                    else
                        new_entry, new_entry_id = make_entry(sc, new_type_id, entry.values)
                    end

                    exact_match, parents_children = find_related_branches(sc, var_id, new_entry, new_entry_id)
                    if !isnothing(exact_match)
                        inputs[var_id] = exact_match
                    else
                        created_branch_id = increment!(sc.branches_count)
                        sc.branch_creation_iterations[created_branch_id] = sc.iterations_count
                        sc.branch_entries[created_branch_id] = new_entry_id
                        sc.branch_vars[created_branch_id] = var_id
                        sc.branch_types[created_branch_id] = new_type_id

                        for (parent, children) in parents_children
                            if !isnothing(parent)
                                deleteat!(sc.branch_children, parent, children)
                                sc.branch_children[parent, created_branch_id] = true
                            end
                            sc.branch_children[created_branch_id, children] = true
                        end

                        sc.branch_is_unknown[created_branch_id] = true

                        for parent in get_all_parents(sc, created_branch_id)
                            if !isnothing(sc.unknown_min_path_costs[parent])
                                sc.branch_unknown_from_output[created_branch_id] = sc.branch_unknown_from_output[parent]
                                sc.unknown_min_path_costs[created_branch_id] = sc.unknown_min_path_costs[parent]
                                break
                            end
                        end

                        if !isa(new_entry, NoDataEntry)
                            sc.unmatched_complexities[created_branch_id] = new_entry.complexity
                            sc.complexities[created_branch_id] = new_entry.complexity
                        end

                        new_branches[br_id] = created_branch_id
                        inputs[var_id] = created_branch_id
                    end
                end
            end

            new_fixed_branches = merge(fixed_branches, inputs)

            for (old_br_id, new_br_id) in new_branches
                if sc.branch_is_unknown[new_br_id]
                    old_related_branches = get_connected_from(sc.related_unknown_complexity_branches, old_br_id)
                    new_related_branches = UInt64[
                        (haskey(new_branches, b_id) ? new_branches[b_id] : b_id) for b_id in old_related_branches
                    ]
                    sc.related_unknown_complexity_branches[new_br_id, new_related_branches] = true

                    if !isnothing(sc.complexities[new_br_id])
                        sc.unknown_complexity_factors[new_br_id] = branch_complexity_factor_unknown(sc, new_br_id)
                    else
                        sc.unknown_complexity_factors[new_br_id] = sc.unknown_complexity_factors[old_br_id]
                    end
                end
            end
        else
            old_type = sc.types[sc.branch_types[new_fixed_branches[block.input_vars[1]]]]
            context, in_type = instantiate(old_type, context)
            context = unify(context, return_of_type(block_type), in_type)
            _, new_in_type = apply_context(context, in_type)
            _, new_norm_in_type = instantiate(new_in_type, empty_context)
            if new_norm_in_type != old_type
                error("New type $new_norm_in_type does not match old type $old_type")
            end
        end
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
    next_blocks = get_connected_from(sc.branch_outgoing_blocks, out_branch_id)
    # @info "Possible next blocks $next_blocks"
    for (b_copy_id, b_id) in next_blocks
        block = sc.blocks[b_id]
        # @info "Block $b_id $block"
        unfixed_vars = [v_id for v_id in block.input_vars if !haskey(fixed_branches, v_id)]
        # @info "Unfixed vars $unfixed_vars"
        allow_block_fails, block_options, unfixed_options =
            _downstream_branch_options_known(sc, b_id, b_copy_id, fixed_branches, unfixed_vars)
        # @info "Allow block fails $allow_block_fails"
        # @info "Block options $block_options"
        # @info "Unfixed options $unfixed_options"
        allow_fails |= allow_block_fails
        union!(outputs, block_options)
        # union!(unexplained_options, unfixed_options)
    end

    # @info allow_fails
    # @info outputs
    return allow_fails, outputs
end

function _find_unconstrained_parents(sc, branch_id)
    parents = Set{UInt64}()
    for parent_id in get_connected_to(sc.branch_children, branch_id)
        constraints = get_connected_from(sc.constrained_branches, parent_id)
        if isempty(constraints)
            push!(parents, parent_id)
            union!(parents, _find_unconstrained_parents(sc, parent_id))
        end
    end
    return parents
end

function _downstream_blocks_new_branch(sc, var_id, out_branch_id, fixed_branches)
    allow_fails = false
    outputs = Set()
    fixed_branches = merge(fixed_branches, Dict(var_id => out_branch_id))
    unexplained_options = Set()

    for parent_id in _find_unconstrained_parents(sc, out_branch_id)
        next_blocks = get_connected_from(sc.branch_outgoing_blocks, parent_id)
        for (b_copy_id, b_id) in next_blocks
            block = sc.blocks[b_id]
            unfixed_vars = [v_id for v_id in block.input_vars if !haskey(fixed_branches, v_id)]
            allow_block_fails, block_options, unfixed_options =
                _downstream_branch_options_known(sc, b_id, b_copy_id, fixed_branches, unfixed_vars)
            allow_fails |= allow_block_fails
            union!(outputs, block_options)
            union!(unexplained_options, unfixed_options)
        end
    end
    for (b_id, inp_branches, target_branches) in unexplained_options
        _save_block_branch_connections(sc, b_id, sc.blocks[b_id], inp_branches, target_branches)
    end
    # @info allow_fails
    # @info outputs
    return allow_fails, outputs
end

function _save_block_branch_connections(sc, block_id, block, fixed_branches, out_branches)
    input_br_ids = sort(UInt64[fixed_branches[var_id] for var_id in block.input_vars])
    existing_incoming = DefaultDict{UInt64,Int}(() -> 0)
    for out_br_id in out_branches
        for (bl_copy_id, bl_id) in get_connected_from(sc.branch_incoming_blocks, out_br_id)
            if bl_id == block_id
                existing_incoming[bl_copy_id] += 1
            end
        end
    end
    for (bl_copy_id, count) in existing_incoming
        if count != length(out_branches)
            continue
        end
        if sort(collect(keys(get_connected_to(sc.branch_outgoing_blocks, bl_copy_id)))) == input_br_ids
            if sc.verbose
                @info "Block $block_id $block already has connections for inputs $input_br_ids and outputs $out_branches"
            end
            return bl_copy_id
            throw(EnumerationException())
        end
    end

    block_copy_id = increment!(sc.block_copies_count)
    sc.block_creation_iterations[block_copy_id] = sc.iterations_count

    sc.branch_outgoing_blocks[input_br_ids, block_copy_id] = block_id
    sc.branch_incoming_blocks[out_branches, block_copy_id] = block_id

    following_entries = Set{UInt64}()
    following_branches = Set{UInt64}()
    for br_id in out_branches
        union!(following_entries, get_connected_from(sc.branch_foll_entries, br_id))
        push!(following_entries, sc.branch_entries[br_id])
        union!(following_branches, get_connected_from(sc.previous_branches, br_id))
        push!(following_branches, br_id)
    end
    prev_entries = Set{UInt64}()
    prev_branches = Set{UInt64}()
    for br_id in input_br_ids
        union!(prev_entries, get_connected_from(sc.branch_prev_entries, br_id))
        push!(prev_entries, sc.branch_entries[br_id])
        union!(prev_branches, get_connected_to(sc.previous_branches, br_id))
        push!(prev_branches, br_id)
    end

    sc.branch_prev_entries[following_branches, prev_entries] = true
    sc.branch_foll_entries[prev_branches, following_entries] = true
    sc.previous_branches[prev_branches, following_branches] = true

    if sc.verbose
        inputs = [
            (
                br_id,
                sc.branch_entries[br_id],
                sc.types[sc.entries[sc.branch_entries[br_id]].type_id],
                sc.entries[sc.branch_entries[br_id]],
            ) for br_id in input_br_ids
        ]
        outputs = [
            (
                br_id,
                sc.branch_entries[br_id],
                sc.types[sc.entries[sc.branch_entries[br_id]].type_id],
                sc.entries[sc.branch_entries[br_id]],
            ) for br_id in out_branches
        ]

        @info "Created new block copy $block_copy_id for block $block_id $block with inputs $inputs and outputs $outputs"
    end
    return block_copy_id
end
