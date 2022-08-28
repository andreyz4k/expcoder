

function get_all_children(sc, branch_id::Integer)
    union(
        [branch_id],
        [get_all_children(sc, child_id) for child_id in nonzeroinds(sc.branch_children[branch_id, :])]...,
    )
end

function get_known_children(sc, branch_id)
    if !sc.branches_is_unknown[branch_id]
        Set([branch_id])
    else
        children = nonzeroinds(sc.branch_children[branch_id, :])
        if isempty(children)
            Set()
        else
            union([get_known_children(sc, b) for b in children]...)
        end
    end
end

function get_unknown_children(sc, branch_id)
    if !sc.branches_is_unknown[branch_id]
        Set()
    else
        union(
            [branch_id],
            [get_unknown_children(sc, child_id) for child_id in nonzeroinds(sc.branch_children[branch_id, :])]...,
        )
    end
end

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


function value_updates(sc, block::ProgramBlock, branch_id, new_values, active_constraints)
    if isnothing(block.output_var[2])
        error("Block without output variable: $block")
    else
        entry = sc.entries[sc.branch_entries[branch_id]]
        t_id = push!(sc.types, return_of_type(block.type))
        return updated_branches(
            sc,
            entry,
            new_values,
            block,
            branch_id,
            t_id,
            !isa(block.p, FreeVar),
            active_constraints,
        )
    end
end

function value_updates(sc, block::ReverseProgramBlock, branches, new_values, active_constraints)
    out_branches = Dict()
    old_constraints = Set()
    new_constraints = Set()
    has_new_branches = false
    for (br_id, values) in zip(branches, new_values)
        values = collect(values)
        entry = sc.entries[sc.branch_entries[br_id]]
        out_branch_id, old_constr, new_constr, has_new_brs =
            updated_branches(sc, entry, values, block, br_id, entry.type_id, true, active_constraints)
        union!(old_constraints, old_constr)
        setdiff!(new_constraints, old_constr)
        union!(new_constraints, new_constr)
        has_new_branches |= has_new_brs
        out_branches[sc.branch_vars[br_id]] = out_branch_id
    end
    return out_branches, old_constraints, new_constraints, has_new_branches
end


function updated_branches(sc, ::ValueEntry, new_values, block, branch_id, t_id, is_meaningful, active_constraints)
    if !sc.branches_is_unknown[branch_id]
        return branch_id, UInt64[], UInt64[], false
    else
        parent_constraints = nonzeroinds(sc.constrained_branches[branch_id, :])
        var_id = sc.branch_vars[branch_id]
        for child_id in nonzeroinds(sc.branch_children[branch_id, :])
            if sc.branch_entries[child_id] == sc.branch_entries[branch_id] && !sc.branches_is_unknown[child_id]
                if isempty(active_constraints) || is_constrained_var(sc, var_id, active_constraints)
                    return child_id, parent_constraints, nonzeroinds(sc.constrained_branches[child_id, :]), false
                else
                    if isempty(parent_constraints)
                        sc.constrained_branches[child_id, active_constraints] = var_id
                        sc.constrained_vars[var_id, active_constraints] = child_id
                    else
                        error("Not implemented")
                    end
                    return child_id, parent_constraints, UInt64[], false
                end
            end
        end
        new_branch_id = increment!(sc.created_branches)
        sc.branch_entries[new_branch_id] = sc.branch_entries[branch_id]
        sc.branch_vars[new_branch_id] = var_id
        sc.branch_types[new_branch_id, t_id] = t_id
        if sc.branches_is_known[branch_id] || is_meaningful
            sc.branches_is_known[new_branch_id] = true
        end
        sc.branch_children[branch_id, new_branch_id] = 1
        sc.branch_outgoing_blocks[new_branch_id, :] = sc.branch_outgoing_blocks[branch_id, :]
        sc.complexities[new_branch_id] = sc.complexities[branch_id]
        sc.best_complexities[new_branch_id] = sc.complexities[branch_id]
        sc.unmatched_complexities[new_branch_id] = 0.0

        child_constraints = UInt64[increment!(sc.constraints_count) for _ = 1:length(parent_constraints)]

        if isempty(active_constraints) || is_constrained_var(sc, var_id, active_constraints)
            if !isempty(parent_constraints)
                constr_branches = sc.constrained_branches[:, parent_constraints]

                select!(!=, constr_branches, var_id)
                constr_branches[new_branch_id, :] = var_id
                sc.constrained_branches[:, child_constraints] = constr_branches

                constr_vars = sc.constrained_vars[:, parent_constraints]
                constr_vars[var_id, :] = new_branch_id
                sc.constrained_vars[:, child_constraints] = constr_vars

                sc.constrained_contexts[:, child_constraints] = sc.constrained_contexts[:, parent_constraints]
            end
        else
            if isempty(parent_constraints)
                sc.constrained_branches[new_branch_id, active_constraints] = var_id
                sc.constrained_vars[var_id, active_constraints] = new_branch_id
            else
                error("Not implemented")
            end
        end

        return new_branch_id, parent_constraints, child_constraints, true
    end
end


function find_related_branches(sc, branch_id, new_entry, new_entry_index)
    possible_parents = UInt64[]
    for child_id in nonzeroinds(sc.branch_children[branch_id, :])
        if !sc.branches_is_unknown[child_id]
            if sc.branch_entries[child_id] == new_entry_index
                return UInt64[], child_id
            end
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


function updated_branches(sc, entry, new_values, block, branch_id, t_id, is_meaningful, active_constraints)
    complexity_summary = get_complexity_summary(new_values, sc.types[t_id])
    new_entry = ValueEntry(t_id, new_values, complexity_summary, get_complexity(sc, complexity_summary))
    new_entry_index = push!(sc.entries, new_entry)
    new_parents, possible_result = find_related_branches(sc, branch_id, new_entry, new_entry_index)
    parent_constraints = nonzeroinds(sc.constrained_branches[branch_id, :])
    var_id = sc.branch_vars[branch_id]
    if !isnothing(possible_result)
        if isempty(active_constraints) || is_constrained_var(sc, var_id, active_constraints)
            return possible_result,
            parent_constraints,
            nonzeroinds(sc.constrained_branches[possible_result, :]),
            false
        else
            if isempty(parent_constraints)
                sc.constrained_branches[possible_result, active_constraints] = var_id
                sc.constrained_vars[var_id, active_constraints] = possible_result
            else
                error("Not implemented")
            end
            return possible_result, parent_constraints, UInt64[], false
        end
    end

    new_branch_id = increment!(sc.created_branches)
    sc.branch_entries[new_branch_id] = new_entry_index
    sc.branch_vars[new_branch_id] = var_id
    sc.branch_types[new_branch_id, t_id] = t_id
    if sc.branches_is_known[branch_id] || is_meaningful
        sc.branches_is_known[new_branch_id] = true
    end
    sc.branch_children[new_parents, new_branch_id] = 1
    sc.branch_outgoing_blocks[new_branch_id, :] = sc.branch_outgoing_blocks[branch_id, :]
    sc.complexities[new_branch_id] = new_entry.complexity
    sc.best_complexities[new_branch_id] = new_entry.complexity
    sc.unmatched_complexities[new_branch_id] = 0.0

    if isempty(active_constraints) || is_constrained_var(sc, var_id, active_constraints)
        child_constraints = UInt64[
            tighten_constraint(sc, constraint_id, new_branch_id, branch_id) for constraint_id in parent_constraints
        ]
    else
        if isempty(parent_constraints)
            sc.constrained_branches[new_branch_id, active_constraints] = var_id
            sc.constrained_vars[var_id, active_constraints] = new_branch_id
        else
            error("Not implemented")
        end
        child_constraints = UInt64[]
    end

    return new_branch_id, parent_constraints, child_constraints, true
end

function _is_ancestor(sc, br_a, br_b)
    if br_a == br_b
        return true
    end
    return any(_is_ancestor(sc, parent_a, br_b) for parent_a in nonzeroinds(sc.branch_children[:, br_a]))
end

function intersect_branches(sc, br_a, br_b)
    if _is_ancestor(sc, br_a, br_b)
        return br_b
    end
    if _is_ancestor(sc, br_b, br_a)
        return br_a
    end
    error("Not implemented")
    return nothing
end

function is_constrained_var(sc, var_id, constraints)
    return nnz(sc.constrained_vars[var_id, constraints]) > 0
end

function get_branch_with_constraints(sc, var_id, constraints, min_root_branch_id)::Int
    options = unique(nonzeros(sc.constrained_vars[var_id, constraints]))
    if length(options) > 1
        error("Constraints are not compatible: $constraints for $var_id with options $options")
    end
    if length(options) == 1
        return first(options)
    end
    return min_root_branch_id
end

function get_branches_with_constraints(sc, var_id, constraints, min_root_branch_id)
    branch_options = DefaultDict(() -> [])
    common_constraints = UInt64[]
    constrained_branches = sc.constrained_vars[var_id, constraints]
    for (constraint_id, branch_id) in zip(constraints, constrained_branches)
        if isnothing(branch_id)
            push!(common_constraints, constraint_id)
        else
            push!(branch_options[branch_id], constraint_id)
        end
    end
    if isempty(branch_options)
        branch_options[min_root_branch_id] = nonzeroinds(sc.constrained_branches[min_root_branch_id, :])
    end
    return common_constraints, branch_options
end

function _get_constrained_branch_options_known(
    sc,
    block,
    fixed_branches,
    active_constraints::Vector,
    unfixed_vars,
)
    if isempty(unfixed_vars)
        return false, Set([(fixed_branches, active_constraints)])
    end
    var_id = unfixed_vars[1]
    common_constraints, branch_options =
        get_branches_with_constraints(sc, var_id, active_constraints, block.input_vars[var_id])
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
                br_constraints = nonzeroinds(sc.constrained_branches[br_id, :])
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
        tail_have_unknowns, tail_results = _get_constrained_branch_options_known(
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

function get_constrained_branch_options_known(sc, block_id, fixed_branches, active_constraints)
    block = sc.blocks[block_id]
    unfixed_vars = [var_id for (var_id, _) in block.input_vars if !haskey(fixed_branches, var_id)]
    return _get_constrained_branch_options_known(sc, block, fixed_branches, active_constraints, unfixed_vars)
end


function _get_constrained_branch_options_unknown(
    sc,
    block,
    fixed_branches,
    active_constraints::Vector,
    unfixed_vars,
)
    if isempty(unfixed_vars)
        return Set([(fixed_branches, active_constraints)])
    end
    var_id = unfixed_vars[1]
    branch_options = DefaultDict(() -> [])
    if is_constrained_var(sc, var_id, active_constraints)
        common_constraints = UInt64[]
        constrained_branches = sc.constrained_vars[var_id, active_constraints]
        for (constraint_id, branch_id) in zip(active_constraints, constrained_branches)
            if isnothing(branch_id)
                push!(common_constraints, constraint_id)
            elseif sc.branches_is_unknown[branch_id]
                push!(branch_options[branch_id], constraint_id)
            end
        end
    else
        common_constraints = active_constraints
        for br_id in get_unknown_children(sc, block.input_vars[var_id])
            br_constraints = nonzeroinds(sc.constrained_branches[br_id, :])
            branch_options[br_id] = br_constraints
        end
    end

    results = Set()
    for (option, constraint_ids) in branch_options
        tail_results = _get_constrained_branch_options_unknown(
            sc,
            block,
            merge(fixed_branches, Dict(var_id => option)),
            union(common_constraints, constraint_ids),
            unfixed_vars[2:end],
        )
        results = union(results, tail_results)
    end
    results
end

function get_constrained_branch_options_unknown(sc, block_id, fixed_branches, active_constraints)
    block = sc.blocks[block_id]
    unfixed_vars = [var_id for (var_id, _) in block.input_vars if !haskey(fixed_branches, var_id)]
    return _get_constrained_branch_options_unknown(sc, block, fixed_branches, active_constraints, unfixed_vars)
end
