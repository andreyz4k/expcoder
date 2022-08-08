

function _find_relatives_for_type(sc, t, branch_id, branch_type)
    if branch_type == t && sc.branches_is_unknown[branch_id]
        return branch_id, Int[], Int[]
    end
    if !sc.branches_is_unknown[branch_id] && is_subtype(t, branch_type)
        return nothing, nonzeroinds(sc.branch_children[:, branch_id])[1], Int[branch_id]
    end
    parents = Int[]
    children = Int[]
    for child_id in nonzeroinds(sc.branch_children[branch_id, :])[2]
        child_type = sc.types[reduce(any, sc.branch_types[child_id, :])]
        if is_subtype(child_type, t)
            exact_match, parents_, children_ = _find_relatives_for_type(sc, t, child_id, child_type)
            if !isnothing(exact_match)
                return exact_match, Int[], Int[]
            end
            union!(parents, parents_)
            union!(children, children_)
        elseif is_subtype(t, child_type)
            push!(children, child_id)
        end
    end
    if isempty(parents)
        push!(parents, branch_id)
    end
    return nothing, parents, children
end

function _tighten_constraint(
    sc,
    constrained_branches,
    constrained_contexts,
    new_var_id,
    new_branch_id,
    old_entry::NoDataEntry,
)
    out_branches = Dict()

    context_id = constrained_contexts[new_var_id]
    context = sc.constraint_contexts[context_id]

    out_contexts = Dict()

    new_type = sc.types[reduce(any, sc.branch_types[new_branch_id, :])]
    context = unify(context, new_type, sc.types[old_entry.type_id])
    new_affected_vars = Int[]
    if is_polymorphic(new_type)
        push!(new_affected_vars, new_var_id)
    end
    for (var_id, branch_id) in constrained_branches
        if var_id == new_var_id
            out_branches[var_id] = new_branch_id
        elseif !haskey(constrained_contexts, var_id)
            out_branches[var_id] = branch_id
        elseif constrained_contexts[var_id] != context_id
            out_branches[var_id] = branch_id
            out_contexts[var_id] = constrained_contexts[var_id]
        else
            branch_type = sc.types[reduce(any, sc.branch_types[branch_id, :])]
            context, new_type = apply_context(context, branch_type)
            if is_polymorphic(new_type)
                push!(new_affected_vars, var_id)
            end
            exact_match, parents, children = _find_relatives_for_type(sc, new_type, branch_id, branch_type)
            if !isnothing(exact_match)
                push!(out_branches, exact_match)
            else
                new_type_id = push!(sc.types, new_type)
                new_entry = NoDataEntry(new_type_id)
                entry_id = push!(sc.entries, new_entry)
                created_branch_id = increment!(sc.created_branches)
                sc.branch_entries[created_branch_id] = entry_id
                sc.branch_vars[created_branch_id] = var_id
                sc.branch_types[created_branch_id, new_type_id] = new_type_id
                deleteat!(sc.branch_children, parents, children)
                sc.branch_children[parents, created_branch_id] = 1
                sc.branch_children[created_branch_id, children] = 1

                sc.branches_is_unknown[created_branch_id] = true
                sc.branch_outgoing_blocks[created_branch_id, :] = sc.branch_outgoing_blocks[branch_id, :]
                sc.min_path_costs[created_branch_id] = sc.min_path_costs[branch_id]
                sc.added_upstream_complexities[created_branch_id] = sc.added_upstream_complexities[branch_id]
                sc.complexity_factors[created_branch_id] = sc.complexity_factors[branch_id]
                sc.related_complexity_branches[created_branch_id, :] = sc.related_complexity_branches[branch_id, :]

                push!(out_branches, created_branch_id)
            end
        end
    end
    new_context_id = push!(sc.constraint_contexts, context)
    for var_id in new_affected_vars
        out_contexts[var_id] = new_context_id
    end

    return out_branches, out_contexts
end

function tighten_constraint(sc, constraint_id, new_branch_id, old_branch_id)
    old_entry = sc.entries[sc.branch_entries[old_branch_id]]
    constrained_branches = Dict(v => b for (b, _, v) in zip(findnz(sc.constrained_branches[:, constraint_id])...))
    constrained_contexts = Dict(v => c for (v, _, c) in zip(findnz(sc.constrained_contexts[:, constraint_id])...))
    new_branches, new_contexts = _tighten_constraint(
        sc,
        constrained_branches,
        constrained_contexts,
        sc.branch_vars[new_branch_id],
        new_branch_id,
        old_entry,
    )

    new_constraint_id = increment!(sc.constraints_count)

    vars = Int[]
    branches = Int[]
    cont_vars = Int[]
    contexts = Int[]
    for (var_id, branch_id) in new_branches
        push!(vars, var_id)
        push!(branches, branch_id)
        if haskey(new_contexts, var_id)
            push!(cont_vars, var_id)
            push!(contexts, new_contexts[var_id])
        end
    end
    sc.constrained_vars[vars, new_constraint_id] = branches
    sc.constrained_branches[branches, new_constraint_id] = vars
    sc.constrained_contexts[cont_vars, new_constraint_id] = contexts
    return new_constraint_id
end


function _get_fixed_hashes(options::EitherOptions, value)
    out_hashes = Set()
    for (h, option) in options.options
        found, hashes = _get_fixed_hashes(option, value)
        if found
            union!(out_hashes, hashes)
            push!(out_hashes, h)
        end
    end
    return !isempty(out_hashes), out_hashes
end

function _get_fixed_hashes(options, value)
    options == value, Set()
end

function __fix_option_hashes(fixed_hashes, value::EitherOptions)
    filter_level = any(haskey(value.options, h) for h in fixed_hashes)
    out_options = Dict()
    for (h, option) in value.options
        if filter_level && !in(h, fixed_hashes)
            continue
        end
        out_options[h] = __fix_option_hashes(fixed_hashes, option)
    end
    if isempty(out_options)
        error("No options left after filtering")
    elseif length(out_options) == 1
        return first(out_options)[2]
    else
        return EitherOptions(out_options)
    end
end

function __fix_option_hashes(fixed_hashes, value)
    return value
end

function _fix_option_hashes(sc, fixed_hashes, entry::EitherEntry)
    out_values = []
    for ((found, hashes), value) in zip(fixed_hashes, entry.values)
        if !found
            error("Inconsistent match")
        end
        push!(out_values, __fix_option_hashes(hashes, value))
    end
    complexity_summary = get_complexity_summary(out_values, sc.types[entry.type_id])
    if any(isa(v, EitherOptions) for v in out_values)
        return EitherEntry(entry.type_id, out_values, complexity_summary, get_complexity(sc, complexity_summary))
    else
        return ValueEntry(entry.type_id, out_values, complexity_summary, get_complexity(sc, complexity_summary))
    end
end

function _find_relatives_for_either(sc, new_entry, branch_id)
    entry = sc.entries[sc.branch_entries[branch_id]]
    if entry == new_entry && sc.branches_is_unknown[branch_id]
        return branch_id, Int[], Int[]
    end
    if !sc.branches_is_unknown[branch_id] && is_subeither(new_entry.values, entry.values)
        return nothing, nonzeroinds(sc.branch_children[:, branch_id])[1], [branch_id]
    end
    parents = Int[]
    children = Int[]
    for child_id in nonzeroinds(sc.branch_children[branch_id, :])[2]
        child_entry = sc.entries[sc.branch_entries[child_id]]
        if is_subeither(child_entry.values, new_entry.values)
            exact_match, parents_, children_ = _find_relatives_for_either(sc, new_entry, child_id)
            if !isnothing(exact_match)
                return exact_match, Int[], Int[]
            end
            union!(parents, parents_)
            union!(children, children_)
        elseif is_subeither(new_entry.values, child_entry.values)
            push!(children, child_id)
        end
    end
    if isempty(parents)
        push!(parents, branch_id)
    end
    return nothing, parents, children
end

function _tighten_constraint(
    sc,
    constrained_branches,
    constrained_contexts,
    new_var_id,
    new_branch_id,
    old_entry::EitherEntry,
)
    out_branches = Dict()
    new_branches = Dict()

    # @info new_branch
    new_entry = sc.entries[sc.branch_entries[new_branch_id]]
    # @info new_entry
    fixed_hashes = [_get_fixed_hashes(options, value) for (options, value) in zip(old_entry.values, new_entry.values)]
    # @info fixed_hashes

    for (var_id, branch_id) in constrained_branches
        if var_id == new_var_id
            out_branches[var_id] = new_branch_id
            new_branches[branch_id] = new_branch_id
        else
            old_br_entry = sc.entries[sc.branch_entries[branch_id]]
            # @info old_br_entry
            if !isa(old_br_entry, EitherEntry)
                out_branches[var_id] = branch_id
            else
                new_br_entry = _fix_option_hashes(sc, fixed_hashes, old_br_entry)
                # @info new_br_entry
                exact_match, parents, children = _find_relatives_for_either(sc, new_br_entry, branch_id)
                if !isnothing(exact_match)
                    out_branches[var_id] = exact_match
                else
                    entry_index = push!(sc.entries, new_br_entry)
                    # @info entry_index

                    created_branch_id = increment!(sc.created_branches)
                    sc.branch_entries[created_branch_id] = entry_index
                    sc.branch_vars[created_branch_id] = var_id
                    sc.branch_types[created_branch_id, new_br_entry.type_id] = new_br_entry.type_id
                    sc.branches_is_unknown[created_branch_id] = true
                    deleteat!(sc.branch_children, parents, children)
                    sc.branch_children[parents, created_branch_id] = 1
                    sc.branch_children[created_branch_id, children] = 1

                    sc.branch_outgoing_blocks[created_branch_id, :] = sc.branch_outgoing_blocks[branch_id, :]
                    sc.min_path_costs[created_branch_id] = sc.min_path_costs[branch_id]
                    sc.complexities[created_branch_id] = new_br_entry.complexity
                    sc.added_upstream_complexities[created_branch_id] = sc.added_upstream_complexities[branch_id]
                    sc.best_complexities[created_branch_id] = new_br_entry.complexity
                    sc.unmatched_complexities[created_branch_id] = new_br_entry.complexity

                    out_branches[var_id] = created_branch_id
                    new_branches[branch_id] = created_branch_id
                end
            end
        end
    end
    for (old_br_id, new_br_id) in new_branches
        if sc.branches_is_unknown[new_br_id]
            old_related_branches = nonzeroinds(sc.related_complexity_branches[old_br_id, :])[2]
            new_related_branches =
                UInt64[(haskey(new_branches, b_id) ? new_branches[b_id] : b_id) for b_id in old_related_branches]
            sc.related_complexity_branches[new_br_id, new_related_branches] = 1
            sc.complexity_factors[new_br_id] = branch_complexity_factor(sc, new_br_id)
        end
    end
    return out_branches, constrained_contexts
end

function _tighten_constraint(
    sc,
    constrained_branches,
    constrained_contexts,
    new_var_id,
    new_branch_id,
    old_entry::ValueEntry,
)
    return Dict(v => (v == new_var_id ? new_branch_id : b) for (v, b) in constrained_branches), constrained_contexts
end

function _finished_merge(constr_a_branches, constr_b_branches, common_vars)
    return all(constr_a_branches[var_id] == constr_b_branches[var_id] for var_id in common_vars)
end

function _lift_known_vars(sc, known_vars, source_branches, target_branches, target_contexts)
    for known_var in known_vars
        known_branch_source = source_branches[known_var]
        if haskey(target_branches, known_var) && target_branches[known_var] != known_branch_source
            target_entry = sc.entries[sc.branch_entries[target_branches[known_var]]]
            source_entry = sc.entries[sc.branch_entries[known_branch_source]]
            if !match_with_entry(sc, target_entry, source_entry)
                return Dict(), Dict()
            end
            target_branches, target_contexts =
                _tighten_constraint(sc, target_branches, target_contexts, known_var, known_branch_source, target_entry)
        end
    end
    return target_branches, target_contexts
end

function merge_constraints(sc, constr_a, constr_b)
    if constr_a == constr_b
        return constr_a
    end

    constr_a_branches = Dict(v => b for (v, _, b) in zip(findnz(sc.constrained_vars[:, constr_a])...))
    constr_a_contexts = Dict(v => c for (v, _, c) in zip(findnz(sc.constrained_contexts[:, constr_a])...))
    constr_a_known_vars = nonzeros(
        apply(
            identity,
            sc.constrained_branches[:, constr_a],
            mask = sc.branches_is_unknown[:],
            desc = Descriptor(complement_mask = true),
        ),
    )

    constr_b_branches = Dict(v => b for (v, _, b) in zip(findnz(sc.constrained_vars[:, constr_b])...))
    constr_b_contexts = Dict(v => c for (v, _, c) in zip(findnz(sc.constrained_contexts[:, constr_b])...))

    constr_b_branches, constr_b_contexts =
        _lift_known_vars(sc, constr_a_known_vars, constr_a_branches, constr_b_branches, constr_b_contexts)
    if isempty(constr_b_branches)
        return nothing
    end

    common_vars = intersect(keys(constr_a_branches), keys(constr_b_branches))

    if !_finished_merge(constr_a_branches, constr_b_branches, common_vars)
        constr_b_known_vars = nonzeros(
            apply(
                identity,
                sc.constrained_branches[:, constr_b],
                mask = sc.branches_is_unknown[:],
                desc = Descriptor(complement_mask = true),
            ),
        )
        constr_a_branches, constr_a_contexts =
            _lift_known_vars(sc, constr_b_known_vars, constr_b_branches, constr_a_branches, constr_a_contexts)
        if isempty(constr_a_branches)
            return nothing
        end
    end

    while !_finished_merge(constr_a_branches, constr_b_branches, common_vars)
        for var_id in common_vars
            if constr_a_branches[var_id] != constr_b_branches[var_id]
                intersection = intersect_branches(sc, constr_a_branches[var_id], constr_b_branches[var_id])
                if isnothing(intersection)
                    return nothing
                end
                constr_a_branches, constr_a_contexts = _tighten_constraint(
                    sc,
                    constr_a_branches,
                    constr_a_contexts,
                    var_id,
                    intersection,
                    sc.entries[sc.branch_entries[constr_a_branches[var_id]]],
                )
                constr_b_branches, constr_b_contexts = _tighten_constraint(
                    sc,
                    constr_b_branches,
                    constr_b_contexts,
                    var_id,
                    intersection,
                    sc.entries[sc.branch_entries[constr_b_branches[var_id]]],
                )
            end
        end
    end

    out_vars = Int[]
    out_branches = Int[]

    for (var_id, branch_id) in constr_a_branches
        push!(out_vars, var_id)
        push!(out_branches, branch_id)
    end

    for (var_id, branch_id) in constr_b_branches
        if !haskey(constr_a_branches, var_id)
            push!(out_vars, var_id)
            push!(out_branches, branch_id)
            if haskey(constr_b_contexts, var_id)
                constr_a_contexts[var_id] = constr_b_contexts[var_id]
            end
        end
    end

    out_branches_vec = GBMatrix{Int}(MAX_GRAPH_SIZE, 1)
    out_branches_vec[out_branches] = out_vars

    matching_constraints = *(+, SuiteSparseGraphBLAS.pair)(sc.constrained_branches[:, :]', out_branches_vec)
    select!(==, matching_constraints, length(out_branches))
    if nnz(matching_constraints) == 1
        return nonzeroinds(matching_constraints)[1][1]
    elseif nnz(matching_constraints) > 1
        error("More than one matching constraint")
    end

    new_constraint_id = increment!(sc.constraints_count)

    cont_vars = Int[]
    contexts = Int[]
    for (var_id, cont_id) in constr_a_contexts
        push!(cont_vars, var_id)
        push!(contexts, cont_id)
    end
    sc.constrained_vars[out_vars, new_constraint_id] = out_branches
    sc.constrained_branches[:, new_constraint_id] = out_branches_vec
    sc.constrained_contexts[cont_vars, new_constraint_id] = contexts
    return new_constraint_id
end
