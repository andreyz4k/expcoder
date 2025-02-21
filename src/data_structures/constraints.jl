
function _find_type_branches_between(sc, old_branch_id, new_branch_id, old_type, new_type)
    if old_type == new_type
        return UInt64[]
    end
    out_branches = UInt64[]
    if is_subtype(old_type, new_type)
        push!(out_branches, old_branch_id)
        for child_id in get_connected_from(sc.branch_children, old_branch_id)
            child_type = sc.types[first(get_connected_from(sc.branch_types, child_id))]
            union!(out_branches, _find_type_branches_between(sc, child_id, new_branch_id, child_type, new_type))
        end
    end
    return out_branches
end

function _tighten_constraint(
    sc,
    constrained_branches,
    constrained_context_id,
    new_var_id,
    new_branch_id,
    old_entry::NoDataEntry,
)
    context = sc.constraint_contexts[constrained_context_id]

    out_branches = Dict()
    new_branches = Dict()
    out_constrained_branches = Dict()

    new_type = sc.types[first(get_connected_from(sc.branch_types, new_branch_id))]
    context, new_type = instantiate(new_type, context)
    context = unify(context, new_type, sc.types[old_entry.type_id])
    if isnothing(context)
        error("Cannot unify types $(sc.types[old_entry.type_id]) and $new_type")
    end

    unknown_old_branches = UInt64[]

    for (var_id, branch_id) in constrained_branches
        if var_id == new_var_id
            union!(
                unknown_old_branches,
                _find_type_branches_between(sc, branch_id, new_branch_id, sc.types[old_entry.type_id], new_type),
            )
            out_branches[var_id] = new_branch_id
            new_branches[branch_id] = new_branch_id
        else
            branch_type = sc.types[first(get_connected_from(sc.branch_types, branch_id))]
            context, new_type = apply_context(context, branch_type)

            new_type_id = push!(sc.types, new_type)
            new_entry = NoDataEntry(new_type_id)
            new_entry_id = push!(sc.entries, new_entry)
            exact_match, parents_children = find_related_branches(sc, var_id, new_entry, new_entry_id)
            if !isnothing(exact_match)
                if is_polymorphic(new_type)
                    out_constrained_branches[var_id] = exact_match
                end
                out_branches[var_id] = exact_match
                union!(unknown_old_branches, get_all_parents(sc, exact_match))
            else
                created_branch_id = increment!(sc.branches_count)
                sc.branch_entries[created_branch_id] = new_entry_id
                sc.branch_vars[created_branch_id, var_id] = true
                sc.branch_types[created_branch_id, new_type_id] = true

                for (parent, children) in parents_children
                    deleteat!(sc.branch_children, parent, children)
                    sc.branch_children[parent, created_branch_id] = true
                    sc.branch_children[created_branch_id, children] = true
                end
                union!(unknown_old_branches, get_all_parents(sc, created_branch_id))

                sc.branch_is_unknown[created_branch_id] = true
                sc.branch_unknown_from_output[created_branch_id] = sc.branch_unknown_from_output[branch_id]
                sc.unknown_min_path_costs[created_branch_id] = sc.unknown_min_path_costs[branch_id]
                sc.unknown_complexity_factors[created_branch_id] = sc.unknown_complexity_factors[branch_id]
                related_branches = get_connected_from(sc.related_unknown_complexity_branches, branch_id)
                sc.related_unknown_complexity_branches[created_branch_id, related_branches] = true

                if is_polymorphic(new_type)
                    out_constrained_branches[var_id] = created_branch_id
                end
                out_branches[var_id] = created_branch_id
                new_branches[branch_id] = created_branch_id
            end
        end
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
                v => haskey(out_branches, v) ? out_branches[v] : b for b in inp_branches for
                v in get_connected_from(sc.branch_vars, b)
            )
            out_block_branches = keys(get_connected_to(sc.branch_incoming_blocks, b_copy_id))
            target_branches = UInt64[
                haskey(out_branches, v) ? out_branches[v] : b for b in out_block_branches for
                v in get_connected_from(sc.branch_vars, b)
            ]
            _save_block_branch_connections(sc, b_id, sc.blocks[b_id], inputs, target_branches)
        end
    end

    if length(out_constrained_branches) > 1
        new_context_id = push!(sc.constraint_contexts, context)
        return out_constrained_branches, new_context_id
    else
        return Dict(), nothing
    end
end

function tighten_constraint(sc, constraint_id, new_branch_id, old_branch_id)
    old_entry = sc.entries[sc.branch_entries[old_branch_id]]
    constrained_branches = Dict(v => b for (b, v) in get_connected_to(sc.constrained_branches, constraint_id))
    constrained_context_id = sc.constrained_contexts[constraint_id]
    new_constrained_branches, new_context_id = _tighten_constraint(
        sc,
        constrained_branches,
        constrained_context_id,
        first(get_connected_from(sc.branch_vars, new_branch_id)),
        new_branch_id,
        old_entry,
    )

    if !isempty(new_constrained_branches)
        new_constraint_id = increment!(sc.constraints_count)
        # @info "Added new constraint on tighten $new_constraint_id from $constraint_id"

        vars = UInt64[]
        branches = UInt64[]
        for (var_id, branch_id) in new_constrained_branches
            push!(vars, var_id)
            push!(branches, branch_id)
        end
        sc.constrained_vars[vars, new_constraint_id] = branches
        sc.constrained_branches[branches, new_constraint_id] = vars
        if !isnothing(new_context_id)
            sc.constrained_contexts[new_constraint_id] = new_context_id
        end
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

function _find_either_branches_between(sc, old_branch_id, new_branch_id, old_entry, new_entry)
    if old_entry == new_entry
        return UInt64[]
    end
    out_branches = UInt64[]
    if all(is_subeither(old_val, new_val) for (old_val, new_val) in zip(old_entry.values, new_entry.values))
        push!(out_branches, old_branch_id)
        for child_id in get_connected_from(sc.branch_children, old_branch_id)
            child_entry = sc.entries[sc.branch_entries[child_id]]
            union!(out_branches, _find_either_branches_between(sc, child_id, new_branch_id, child_entry, new_entry))
        end
    end
    return out_branches
end

function get_either_parents(sc, branch_id)
    parents = get_connected_to(sc.branch_children, branch_id)
    for parent_id in parents
        parent_entry = sc.entries[sc.branch_entries[parent_id]]
        if !isa(parent_entry, EitherEntry)
            parents = union(parents, get_either_parents(sc, parent_id))
        end
    end
    return parents
end

function _tighten_constraint(
    sc,
    constrained_branches,
    constrained_context_id,
    new_var_id,
    new_branch_id,
    old_entry::EitherEntry,
)
    out_either_branches = Dict()
    out_branches = Dict()
    new_branches = Dict()

    # @info new_branch
    new_entry = sc.entries[sc.branch_entries[new_branch_id]]
    # @info new_entry
    fixed_hashes = [get_fixed_hashes(old_entry.values[j], new_entry.values[j]) for j in 1:sc.example_count]
    # @info fixed_hashes

    unknown_old_branches = UInt64[]

    for (var_id, branch_id) in constrained_branches
        if var_id == new_var_id
            union!(
                unknown_old_branches,
                _find_either_branches_between(sc, branch_id, new_branch_id, old_entry, new_entry),
            )
            if !isa(new_entry, EitherEntry)
                union!(unknown_old_branches, get_either_parents(sc, new_branch_id))
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
            # @info new_br_entry
            exact_match, parents_children = find_related_branches(sc, var_id, new_br_entry, new_entry_index)
            if !isnothing(exact_match)
                if isa(new_br_entry, EitherEntry)
                    out_either_branches[var_id] = exact_match
                end
                out_branches[var_id] = exact_match
                union!(
                    unknown_old_branches,
                    _find_either_branches_between(sc, branch_id, exact_match, old_entry, new_br_entry),
                )
                if !isa(new_br_entry, EitherEntry)
                    union!(unknown_old_branches, get_either_parents(sc, exact_match))
                end
            else
                # @info entry_index

                created_branch_id = increment!(sc.branches_count)
                sc.branch_entries[created_branch_id] = new_entry_index
                sc.branch_vars[created_branch_id, var_id] = true
                sc.branch_types[created_branch_id, new_br_entry.type_id] = true
                if sc.branch_is_unknown[branch_id]
                    sc.branch_is_unknown[created_branch_id] = true
                    sc.branch_unknown_from_output[created_branch_id] = sc.branch_unknown_from_output[branch_id]
                end
                # if sc.verbose
                #     @info "Inserting new branch from either $((created_branch_id, branch_id))"
                #     root_parent = get_root_parent(sc, branch_id)
                #     @info "Root children $((root_parent, get_connected_from(sc.branch_children, root_parent)))"
                #     for child in get_all_children(sc, root_parent)
                #         @info "Child $((child, (get_connected_from(sc.branch_children, child)), (get_connected_to(sc.branch_children, child)))) is parent $(all(
                #             is_subeither(child_val, new_val) for (child_val, new_val) in
                #             zip(sc.entries[sc.branch_entries[child]].values, new_br_entry.values)
                #         )) is child $(all(
                #             is_subeither(new_val, child_val) for (child_val, new_val) in
                #             zip(sc.entries[sc.branch_entries[child]].values, new_br_entry.values)
                #         ))"
                #     end
                #     @info "Parents and children $parents_children"
                # end
                for (parent, children) in parents_children
                    if !isnothing(parent)
                        deleteat!(sc.branch_children, [parent], children)
                        sc.branch_children[parent, created_branch_id] = true
                    end
                    sc.branch_children[created_branch_id, children] = true
                end

                union!(
                    unknown_old_branches,
                    _find_either_branches_between(sc, branch_id, created_branch_id, old_entry, new_br_entry),
                )
                union!(unknown_old_branches, get_either_parents(sc, created_branch_id))

                original_path_cost = sc.unknown_min_path_costs[branch_id]
                if !isnothing(original_path_cost)
                    sc.unknown_min_path_costs[created_branch_id] = original_path_cost
                end
                sc.complexities[created_branch_id] = new_br_entry.complexity
                sc.unmatched_complexities[created_branch_id] = new_br_entry.complexity

                if isa(new_br_entry, EitherEntry)
                    out_either_branches[var_id] = created_branch_id
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

    visited_b_copy_ids = Set{UInt64}()
    for br_id in unknown_old_branches
        for (b_copy_id, b_id) in get_connected_from(sc.branch_outgoing_blocks, br_id)
            if in(b_copy_id, visited_b_copy_ids)
                continue
            end
            push!(visited_b_copy_ids, b_copy_id)
            inp_branches = keys(get_connected_to(sc.branch_outgoing_blocks, b_copy_id))
            inputs = Dict(
                v => haskey(out_branches, v) ? out_branches[v] : b for b in inp_branches for
                v in get_connected_from(sc.branch_vars, b)
            )
            out_block_branches = keys(get_connected_to(sc.branch_incoming_blocks, b_copy_id))
            target_branches = UInt64[
                haskey(out_branches, v) ? out_branches[v] : b for b in out_block_branches for
                v in get_connected_from(sc.branch_vars, b)
            ]

            input_entries = Set(sc.branch_entries[b] for b in values(inputs))
            if any(in(sc.branch_entries[b], input_entries) for b in target_branches)
                if sc.verbose
                    @info "Fixing constraint leads to a redundant block"
                end
                throw(EnumerationException("Fixing constraint leads to a redundant block"))
            end

            new_b_copy_id = _save_block_branch_connections(sc, b_id, sc.blocks[b_id], inputs, target_branches)
            if any(isa(sc.entries[e], AbductibleEntry) for e in input_entries)
                b = first(b for b in inp_branches if haskey(out_branches, first(get_connected_from(sc.branch_vars, b))))
                _abduct_next_block(
                    sc,
                    new_b_copy_id,
                    b_id,
                    new_branch_id,
                    first(get_connected_from(sc.branch_vars, b)),
                    b,
                )
            end
            for target_branch in target_branches
                update_complexity_factors_unknown(sc, inputs, target_branch)
            end
        end
    end

    return out_either_branches, constrained_context_id
end
