


struct Constraint
    branches::Dict{String,EntryBranch}
    contexts::Dict{String,Context}
    rev_contexts::Dict{Context,Set{String}}
end

Base.hash(tc::Constraint, h::UInt64) = hash(tc.branches, h) + hash(tc.contexts, h)
Base.:(==)(lhs::Constraint, rhs::Constraint) = lhs.branches == rhs.branches && lhs.contexts == rhs.contexts

Base.show(io::IO, tc::Constraint) =
    print(io, "Constraint(", Dict(k => "$(hash(b))" for (k, b) in tc.branches), ", ", tc.contexts, ")")

function create_constraint(branches, contexts)
    constrained_branches = Dict(b.key => b for b in branches)
    if length(constrained_branches) >= 2
        rev_contexts = DefaultDict(() -> Set{String}())
        for (k, c) in contexts
            push!(rev_contexts[c], k)
        end
        constraint = Constraint(constrained_branches, contexts, rev_contexts)
        for (_, b) in constrained_branches
            push!(b.constraints, constraint)
        end
    end
end

constraints_key(constraint::Constraint, key) = haskey(constraint.branches, key)

function _find_relatives_for_type(t, branch)
    if branch.type == t && !branch.is_known
        return branch, Set(), Set()
    end
    if branch.is_known && is_subtype(t, branch.type)
        return nothing, copy(branch.parents), Set([branch])
    end
    parents = Set()
    children = Set()
    for child in branch.children
        if is_subtype(child.type, t)
            exact_match, parents_, children_ = _find_relatives_for_type(t, child)
            if !isnothing(exact_match)
                return exact_match, Set(), Set()
            end
            union!(parents, parents_)
            union!(children, children_)
        elseif is_subtype(t, child.type)
            push!(children, child)
        end
    end
    if isempty(parents)
        push!(parents, branch)
    end
    return nothing, parents, children
end

function _tighten_constraint(
    sc,
    constraint::Constraint,
    old_entry::NoDataEntry,
    new_branch::EntryBranch,
    new_created_branches,
)
    new_branches = Dict()
    created_branches = []
    context = constraint.contexts[new_branch.key]
    affected_keys = constraint.rev_contexts[context]
    contexts = Dict(k => c for (k, c) in constraint.contexts if !in(k, affected_keys))
    rev_contexts = Dict(c => ks for (c, ks) in constraint.rev_contexts if c != context)

    context = unify(context, new_branch.type, old_entry.type)
    new_affected_keys = Set()
    for (key, branch) in constraint.branches
        if key == new_branch.key
            new_branches[key] = new_branch
        elseif !in(key, affected_keys)
            new_branches[key] = branch
        else
            context, new_type = apply_context(context, branch.type)
            if is_polymorphic(new_type)
                push!(new_affected_keys, key)
            end
            exact_match, parents, children = _find_relatives_for_type(new_type, branch)
            if !isnothing(exact_match)
                new_branches[key] = exact_match
            else
                found = false
                for br in new_created_branches
                    if br.key == key && br.parents == parents && br.type == new_type
                        union!(br.children, children)
                        new_branches[key] = br
                        found = true
                        break
                    end
                end
                if !found
                    new_entry = NoDataEntry(new_type)
                    entry_index = add_entry(sc.entries_storage, new_entry)
                    new_branches[key] = EntryBranch(
                        entry_index,
                        branch.key,
                        new_type,
                        parents,
                        children,
                        Set(),
                        [],
                        Set(),
                        copy(branch.outgoing_blocks),
                        false,
                        false,
                        branch.min_path_cost,
                        branch.complexity_factor,
                        nothing,
                        branch.added_upstream_complexity,
                        nothing,
                        nothing,
                        copy(branch.related_complexity_branches),
                    )
                    push!(created_branches, new_branches[key])
                end
            end
        end
    end
    for k in new_affected_keys
        contexts[k] = context
    end
    rev_contexts[context] = new_affected_keys
    return new_branches, created_branches, contexts, rev_contexts
end

function tighten_constraint(sc, constraint::Constraint, new_branch::EntryBranch, new_created_branches)
    new_entry = get_entry(sc.entries_storage, new_branch.value_index)
    old_entry = get_entry(sc.entries_storage, constraint.branches[new_branch.key].value_index)
    new_branches, created_branches, contexts, rev_contexts =
        _tighten_constraint(sc, constraint, old_entry, new_branch, new_created_branches)

    new_constraint = Constraint(new_branches, contexts, rev_contexts)
    push!(new_branch.constraints, new_constraint)
    return created_branches
end

get_matching_branches(constraint::Constraint, key) = get_all_children(constraint.branches[key])
get_constrained_branch(constraint::Constraint, key) = constraint.branches[key]


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
    complexity_summary = get_complexity_summary(out_values, entry.type)
    if any(isa(v, EitherOptions) for v in out_values)
        return EitherEntry(entry.type, out_values, complexity_summary, get_complexity(sc, complexity_summary))
    else
        return ValueEntry(entry.type, out_values, complexity_summary, get_complexity(sc, complexity_summary))
    end
end

function _find_relatives_for_either(sc, new_entry, branch)
    entry = get_entry(sc.entries_storage, branch.value_index)
    if entry == new_entry && !branch.is_known
        return branch, Set(), Set()
    end
    if branch.is_known && is_subeither(new_entry.values, entry.values)
        return nothing, copy(branch.parents), Set([branch])
    end
    parents = Set()
    children = Set()
    for child in branch.children
        child_entry = get_entry(sc.entries_storage, child.value_index)
        if is_subeither(child_entry.values, new_entry.values)
            exact_match, parents_, children_ = _find_relatives_for_either(sc, new_entry, child)
            if !isnothing(exact_match)
                return exact_match, Set(), Set()
            end
            union!(parents, parents_)
            union!(children, children_)
        elseif is_subeither(new_entry.values, child_entry.values)
            push!(children, child)
        end
    end
    if isempty(parents)
        push!(parents, branch)
    end
    return nothing, parents, children
end

function _tighten_constraint(
    sc,
    constraint::Constraint,
    old_entry::EitherEntry,
    new_branch::EntryBranch,
    new_created_branches,
)
    new_branches = Dict()
    created_branches = []
    # @info constraint
    # for (k, br) in constraint.branches
    #     e = get_entry(sc.entries_storage, br.value_index)
    #     # @info "$k $e"
    # end
    # @info new_branch
    new_entry = get_entry(sc.entries_storage, new_branch.value_index)
    # @info new_entry
    fixed_hashes = [_get_fixed_hashes(options, value) for (options, value) in zip(old_entry.values, new_entry.values)]
    # @info fixed_hashes

    for (key, branch) in constraint.branches
        if key == new_branch.key
            new_branches[key] = new_branch
        else
            old_br_entry = get_entry(sc.entries_storage, branch.value_index)
            # @info old_br_entry
            if !isa(old_br_entry, EitherEntry)
                new_branches[key] = branch
            else
                new_br_entry = _fix_option_hashes(sc, fixed_hashes, old_br_entry)
                # @info new_br_entry
                exact_match, parents, children = _find_relatives_for_either(sc, new_br_entry, branch)
                if !isnothing(exact_match)
                    new_branches[key] = exact_match
                else
                    found = false
                    entry_index = add_entry(sc.entries_storage, new_br_entry)
                    # @info entry_index
                    for br in new_created_branches
                        if br.key == key && br.parents == parents && br.value_index == entry_index
                            union!(br.children, children)
                            new_branches[key] = br
                            found = true
                            break
                        end
                    end
                    if !found
                        new_branches[key] = EntryBranch(
                            entry_index,
                            branch.key,
                            branch.type,
                            parents,
                            children,
                            Set(),
                            [],
                            Set(),
                            copy(branch.outgoing_blocks),
                            false,
                            false,
                            branch.min_path_cost,
                            nothing,
                            new_br_entry.complexity,
                            branch.added_upstream_complexity,
                            new_br_entry.complexity,
                            new_br_entry.complexity,
                            branch.related_complexity_branches,
                        )
                        push!(created_branches, new_branches[key])
                    end
                end
            end
        end
    end
    for (_, branch) in new_branches
        if !branch.is_known
            branch.related_complexity_branches =
                Set((haskey(new_branches, b.key) ? new_branches[b.key] : b) for b in branch.related_complexity_branches)
            branch.complexity_factor =
                branch.complexity +
                branch.added_upstream_complexity +
                sum(
                    (b.is_known == branch.is_known ? b.best_complexity : b.complexity) for
                    b in branch.related_complexity_branches
                )
        end
    end
    return new_branches, created_branches, constraint.contexts, constraint.rev_contexts
end


function add_branch_to_constraint(constraint, branch)
    if haskey(constraint.branches, branch.key)
        error("Branch already exists")
    end
    constraint.branches[branch.key] = branch
    push!(branch.constraints, constraint)
end


# function merge_constraints(constr_a::Constraint, constr_b::Constraint)
#     if constr_a == constr_b
#         return constr_a
#     end
#     new_branches = Dict()
#     new_contexts = Dict()
#     new_rev_contexts = Dict()
#     for key in union(keys(constr_a.branches), keys(constr_b.branches))
#         if !haskey(constr_a.branches, key)
#             new_branches[key] = constr_b.branches[key]
#             if haskey(constr_b.contexts, key)
#                 new_contexts[key] = constr_b.contexts[key]
#             end
#         elseif !haskey(constr_b.branches, key)
#             new_branches[key] = constr_a.branches[key]
#         else
#             intersection = intersect_branches(constr_a.branches[key], constr_b.branches[key])
#             if isnothing(intersection)
#                 return nothing
#             end
#             new_branches[key] = intersection
#         end
#     end
# end
