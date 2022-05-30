


struct TypeConstraint <: Constraint
    branches::Dict{String,EntryBranch}
    context::Context
end

Base.hash(tc::TypeConstraint, h::UInt64) =
    hash(tc.branches, h) + hash(tc.context, h)
Base.:(==)(lhs::TypeConstraint, rhs::TypeConstraint) =
    lhs.branches == rhs.branches && lhs.context == rhs.context

function create_type_constraint(branches, context)
    constrained_branches = Dict(k => b for (k, b, t) in branches if is_polymorphic(t))
    if length(constrained_branches) >= 2
        constraint = TypeConstraint(constrained_branches, context)
        for (_, b) in constrained_branches
            push!(b.constraints, constraint)
        end
    end
end

constraints_key(constraint::TypeConstraint, key) = haskey(constraint.branches, key)

function _find_parents_childs_for_type(t, branch)
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
            exact_match, parents_, children_ = _find_parents_childs_for_type(t, child)
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

function tighten_constraint(sc, constraint::TypeConstraint, new_branch::EntryBranch, new_created_branches)
    context = constraint.context
    context = unify(context, new_branch.type, constraint.branches[new_branch.key].type)
    new_branches = Dict()
    created_branches = []
    for (key, branch) in constraint.branches
        if key == new_branch.key
            new_branches[key] = new_branch
        else
            context, new_type = apply_context(context, branch.type)
            exact_match, parents, children = _find_parents_childs_for_type(new_type, branch)
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
                        copy(branch.outgoing_blocks),
                        false,
                        false,
                        branch.min_path_cost,
                        branch.complexity_factor,
                    )
                    push!(created_branches, new_branches[key])
                end
            end
        end
    end
    new_constraint = TypeConstraint(new_branches, context)
    push!(new_branch.constraints, new_constraint)
    return created_branches
end

get_matching_branches(constraint::TypeConstraint, key) = get_all_children(constraint.branches[key])


struct EitherConstraint <: Constraint
    branches::Dict{String,EntryBranch}
end
