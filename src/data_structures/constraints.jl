
function tighten_constraint(sc, new_branch_id, old_branch_id)
    old_entry = sc.entries[sc.branch_entries[old_branch_id]]
    constrained_branches =
        Dict(sc.branch_vars[b] => b for b in get_connected_to(sc.constrained_branches, old_branch_id))
    if sc.verbose
        @info "Tightening constraint from $old_branch_id to $new_branch_id"
        @info "Constrained branches $constrained_branches"
    end
    new_constrained_branches =
        _tighten_constraint(sc, constrained_branches, sc.branch_vars[new_branch_id], new_branch_id, old_entry)

    if !isempty(new_constrained_branches)
        if sc.verbose
            @info "Added new constraint on tighten $new_constrained_branches"
        end
        sc.constrained_branches[new_constrained_branches, new_constrained_branches] = true
    end
    return true
end

function _fix_option_hashes(fixed_hashes, values)
    out_values = []
    for (hashes, value) in zip(fixed_hashes, values)
        push!(out_values, fix_option_hashes(hashes, value))
    end
    return out_values
end

function _fix_option_hashes(sc, fixed_hashes, entry::EitherEntry)
    out_values = _fix_option_hashes(fixed_hashes, entry.values)
    return make_entry(sc, entry.type_id, out_values)
end

function get_non_either_parents(sc, branch_id)
    parents = Set{UInt64}()
    for parent_id in get_connected_to(sc.branch_children, branch_id)
        parent_entry = sc.entries[sc.branch_entries[parent_id]]
        if !isa(parent_entry, EitherEntry)
            push!(parents, parent_id)
            union!(parents, get_non_either_parents(sc, parent_id))
        end
    end
    return parents
end

function _tighten_constraint(sc, constrained_branches, new_var_id, new_branch_id, old_entry::EitherEntry)
    out_either_branches = Set{UInt64}()
    out_branches = Dict()
    new_branches = Dict()

    # @info new_branch
    new_entry = sc.entries[sc.branch_entries[new_branch_id]]
    # @info new_entry
    fixed_hashes = [get_fixed_hashes(old_entry.values[j], new_entry.values[j]) for j in 1:sc.example_count]
    # @info fixed_hashes
    if sc.verbose
        @info "Old entry $old_entry"
        @info "New entry $new_entry"
        @info "Fixed hashes $fixed_hashes"
    end

    unknown_old_branches = UInt64[]

    for (var_id, branch_id) in constrained_branches
        if var_id == new_var_id
            push!(unknown_old_branches, branch_id)
            if !isa(new_entry, EitherEntry)
                union!(unknown_old_branches, get_non_either_parents(sc, new_branch_id))
            end
            out_branches[var_id] = new_branch_id
            new_branches[branch_id] = new_branch_id
        else
            old_br_entry = sc.entries[sc.branch_entries[branch_id]]
            # @info old_br_entry
            if !isa(old_br_entry, EitherEntry)
                error("Non-either branch $branch_id $(sc.branch_entries[branch_id]) $old_br_entry in either constraint")
            end
            new_br_entry, new_entry_index = _fix_option_hashes(sc, fixed_hashes, old_br_entry)
            if sc.verbose
                @info "Fixed branch $branch_id $old_br_entry to $new_br_entry"
            end
            # @info new_br_entry
            exact_match, parents_children = find_related_branches(sc, var_id, new_br_entry, new_entry_index)
            if !isnothing(exact_match)
                if isa(new_br_entry, EitherEntry)
                    push!(out_either_branches, exact_match)
                end
                out_branches[var_id] = exact_match
                push!(unknown_old_branches, branch_id)
                if !isa(new_br_entry, EitherEntry)
                    union!(unknown_old_branches, get_non_either_parents(sc, exact_match))
                end
            else
                # @info entry_index

                created_branch_id = increment!(sc.branches_count)
                sc.branch_creation_iterations[created_branch_id] = sc.iterations_count
                sc.branch_entries[created_branch_id] = new_entry_index
                sc.branch_vars[created_branch_id] = var_id
                sc.branch_types[created_branch_id] = new_br_entry.type_id
                if sc.branch_is_unknown[branch_id]
                    sc.branch_is_unknown[created_branch_id] = true
                    sc.branch_unknown_from_output[created_branch_id] = sc.branch_unknown_from_output[branch_id]
                end
                if sc.verbose
                    @info "Inserting new branch from either $((created_branch_id, branch_id))"
                    root_parent = get_root_parent(sc, branch_id)
                    @info "Root children $((root_parent, get_connected_from(sc.branch_children, root_parent)))"
                    for child in get_all_children(sc, root_parent)
                        @info "Child $((child, (get_connected_from(sc.branch_children, child)), (get_connected_to(sc.branch_children, child)))) is parent $(all(
                            is_subeither(child_val, new_val) for (child_val, new_val) in
                            zip(sc.entries[sc.branch_entries[child]].values, new_br_entry.values)
                        )) is child $(all(
                            is_subeither(new_val, child_val) for (child_val, new_val) in
                            zip(sc.entries[sc.branch_entries[child]].values, new_br_entry.values)
                        ))"
                        @info "Child values $(sc.entries[sc.branch_entries[child]].values)"
                        @info "New branch values $(new_br_entry.values)"
                    end
                    @info "Parents and children $parents_children"
                end
                for (parent, children) in parents_children
                    if !isnothing(parent)
                        deleteat!(sc.branch_children, [parent], children)
                        sc.branch_children[parent, created_branch_id] = true
                    end
                    sc.branch_children[created_branch_id, children] = true
                end

                push!(unknown_old_branches, branch_id)
                union!(unknown_old_branches, get_non_either_parents(sc, created_branch_id))

                original_path_cost = sc.unknown_min_path_costs[branch_id]
                if !isnothing(original_path_cost)
                    sc.unknown_min_path_costs[created_branch_id] = original_path_cost
                end
                sc.complexities[created_branch_id] = new_br_entry.complexity
                sc.unmatched_complexities[created_branch_id] = new_br_entry.complexity

                if isa(new_br_entry, EitherEntry)
                    push!(out_either_branches, created_branch_id)
                end
                out_branches[var_id] = created_branch_id
                new_branches[branch_id] = created_branch_id
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

    if sc.verbose
        @info "Unknown old branches $unknown_old_branches"
        @info "Out branches $out_branches"
    end

    visited_b_copy_ids = Set{UInt64}()
    for br_id in unknown_old_branches
        for (b_copy_id, b_id) in get_connected_from(sc.branch_outgoing_blocks, br_id)
            if in(b_copy_id, visited_b_copy_ids)
                continue
            end
            push!(visited_b_copy_ids, b_copy_id)
            inp_branches = keys(get_connected_to(sc.branch_outgoing_blocks, b_copy_id))
            inputs = Dict(
                v => haskey(out_branches, v) && !is_child_branch(sc, out_branches[v], b) ? out_branches[v] : b for
                b in inp_branches for v in get_connected_from(sc.branch_vars, b)
            )
            out_block_branches = keys(get_connected_to(sc.branch_incoming_blocks, b_copy_id))
            target_branches = UInt64[
                haskey(out_branches, v) && !is_child_branch(sc, out_branches[v], b) ? out_branches[v] : b for
                b in out_block_branches for v in get_connected_from(sc.branch_vars, b)
            ]

            input_entries = Set(sc.branch_entries[b] for b in values(inputs))
            if !sc.traced && any(in(sc.branch_entries[b], input_entries) for b in target_branches)
                if sc.verbose
                    @info "Fixing constraint leads to a redundant block"
                end
                # continue
                # TODO: probably shouldn't crash the whole adding of a new block because of one redundant block
                throw(EnumerationException("Fixing constraint leads to a redundant block"))
            end

            if sc.verbose
                @info "Saving block branch connections from $b_copy_id"
            end
            new_b_copy_id = _save_block_branch_connections(sc, b_id, sc.blocks[b_id], inputs, target_branches)
            if any(isa(sc.entries[e], AbductibleEntry) for e in input_entries)
                b = first(b for b in inp_branches if haskey(out_branches, sc.branch_vars[b]))
                _abduct_next_block(sc, new_b_copy_id, b_id, out_branches[sc.branch_vars[b]], sc.branch_vars[b], b)
            end
            for target_branch in target_branches
                update_complexity_factors_unknown(sc, inputs, target_branch)
            end
        end
    end

    return out_either_branches
end
