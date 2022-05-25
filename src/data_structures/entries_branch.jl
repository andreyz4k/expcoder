
using DataStructures: OrderedDict

abstract type Constraint end

mutable struct EntryBranch
    value_index::Int
    key::String
    type::Tp
    parents::Set{EntryBranch}
    children::Set{EntryBranch}
    constraints::Set{Constraint}
    incoming_paths::Vector{OrderedDict{String,AbstractProgramBlock}}
    outgoing_blocks::Set{AbstractProgramBlock}
    is_known::Bool
    is_meaningful::Bool
    min_path_cost::Union{Float64,Nothing}
    complexity_factor::Union{Float64,Nothing}
end

Base.show(io::IO, branch::EntryBranch) =
    print(io, "EntryBranch(",
        hash(branch),
        ", ",
        branch.value_index,
        ", ",
        branch.key,
        ", ",
        branch.type,
        ", ",
        ["($(br.key), $(hash(br)))" for br in branch.parents],
        ", ",
        ["($(br.key), $(hash(br)))" for br in branch.children],
        ", ",
        branch.constraints,
        ", ",
        branch.incoming_paths,
        ", ",
        branch.outgoing_blocks,
        ", ",
        branch.is_known,
        ", ",
        branch.is_meaningful,
        ", ",
        branch.min_path_cost,
        ", ",
        branch.complexity_factor,
        ")"
    )

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

get_all_children(branch::EntryBranch) = union([branch], [get_all_children(child) for child in branch.children]...)

function get_known_children(branch::EntryBranch)
    if branch.is_known
        Set([branch])
    elseif isempty(branch.children)
        Set()
    else
        union([get_known_children(b) for b in branch.children]...)
    end
end

# function is_branch_compatible(key, branch, fixed_branches)
#     for fixed_branch in fixed_branches
#         if haskey(fixed_branch.values, key)
#             return fixed_branch == branch
#         end
#     end
#     return true
# end


function value_updates(sc, block::ProgramBlock, new_values)
    if isnothing(block.output_var[2])
        return_type = return_of_type(block.type)
        if is_polymorphic(return_type)
            error("returning polymorphic type from $block")
        end
        complexity_summary = get_complexity_summary(new_values, return_type)
        entry = ValueEntry(return_type, new_values, complexity_summary, get_complexity(sc, complexity_summary))
        entry_index = add_entry(sc.entries_storage, entry)
        new_branch = EntryBranch(
            entry_index,
            block.output_var[1],
            return_type,
            Set(),
            Set(),
            Set(),
            [],
            Set(),
            true,
            !isa(block.p, FreeVar),
            nothing,
            nothing,
        )
        return [new_branch], Set()
    else
        entry = get_entry(sc.entries_storage, block.output_var[2].value_index)
        return updated_branches(sc, entry, new_values, block)
    end
end


function updated_branches(sc, ::ValueEntry, new_values, block::ProgramBlock)
    branch = block.output_var[2]
    if branch.is_known
        return [branch], branch.outgoing_blocks
    else
        for child in branch.children
            if child.value_index == branch.value_index && child.is_known
                return [child], child.outgoing_blocks
            end
        end
        new_branch = EntryBranch(
            branch.value_index,
            branch.key,
            branch.type,
            Set([branch]),
            Set(),
            Set(),
            [],
            copy(branch.outgoing_blocks),
            true,
            branch.is_meaningful || !isa(block.p, FreeVar),
            nothing,
            nothing,
        )
        return [new_branch], branch.outgoing_blocks
    end
end


function find_related_branches(branch::EntryBranch, t, entry_index)
    possible_parents = []
    for child in branch.children
        if child.is_known
            if child.value_index == entry_index
                return [], child
            end
        else
            if might_unify(child.type, t)
                parents, possible_result = find_related_branches(child, t, values)
                if !isnothing(possible_result)
                    return [], possible_result
                else
                    append!(possible_parents, parents)
                end
            end
        end
    end
    if isempty(possible_parents)
        return [branch], nothing
    else
        return possible_parents, nothing
    end
end


function updated_branches(sc, entry::NoDataEntry, new_values, block)
    branch = block.output_var[2]
    t = return_of_type(block.type)
    complexity_summary = get_complexity_summary(new_values, t)
    new_entry = ValueEntry(t, new_values, complexity_summary, get_complexity(sc, complexity_summary))
    entry_index = add_entry(sc.entries_storage, new_entry)
    new_parents, possible_result = find_related_branches(branch, t, entry_index)
    if !isnothing(possible_result)
        return [possible_result], possible_result.outgoing_blocks
    end

    new_branch = EntryBranch(
        entry_index,
        branch.key,
        t,
        Set(new_parents),
        Set(),
        Set(),
        [],
        copy(branch.outgoing_blocks),
        true,
        branch.is_meaningful || !isa(block.p, FreeVar),
        nothing,
        nothing,
    )
    new_branches = [new_branch]

    for constraint in branch.constraints
        created_branches = tighten_constraint(sc, constraint, new_branch, new_branches)
        append!(new_branches, created_branches)
    end

    return new_branches, new_branch.outgoing_blocks
end
