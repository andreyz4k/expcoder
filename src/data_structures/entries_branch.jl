
using DataStructures: OrderedDict


mutable struct EntryBranch
    value_index::Int
    key::String
    type::Tp
    parents::Set{EntryBranch}
    children::Set{EntryBranch}
    constraints::Set  # Each constraint represents a distinct solution branch
    incoming_paths::Vector{OrderedDict{String,AbstractProgramBlock}}
    incoming_blocks::Set{AbstractProgramBlock}
    outgoing_blocks::Set{AbstractProgramBlock}
    is_known::Bool
    is_meaningful::Bool
    min_path_cost::Union{Float64,Nothing}
    complexity_factor::Union{Float64,Nothing}
    complexity::Union{Float64,Nothing}
    added_upstream_complexity::Union{Float64,Nothing}
    best_complexity::Union{Float64,Nothing}
    unmatched_complexity::Union{Float64,Nothing}
    related_complexity_branches::Set{EntryBranch}
end

Base.show(io::IO, branch::EntryBranch) = print(
    io,
    "EntryBranch(",
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
    branch.incoming_blocks,
    ", ",
    branch.outgoing_blocks,
    ", ",
    branch.related_complexity_branches,
    ", ",
    branch.is_known,
    ", ",
    branch.is_meaningful,
    ", ",
    branch.min_path_cost,
    ", ",
    branch.complexity_factor,
    ", ",
    branch.complexity,
    ", ",
    branch.added_upstream_complexity,
    ", ",
    branch.best_complexity,
    ", ",
    branch.unmatched_complexity,
    ")",
)

Base.:(==)(a::EntryBranch, b::EntryBranch) =
    a.value_index == b.value_index &&
    a.key == b.key &&
    a.type == b.type &&
    a.parents == b.parents &&
    a.children == b.children &&
    a.constraints == b.constraints &&
    a.incoming_paths == b.incoming_paths &&
    a.incoming_blocks == b.incoming_blocks &&
    a.outgoing_blocks == b.outgoing_blocks &&
    a.related_complexity_branches == b.related_complexity_branches &&
    a.is_known == b.is_known &&
    a.is_meaningful == b.is_meaningful &&
    a.min_path_cost == b.min_path_cost &&
    a.complexity_factor == b.complexity_factor &&
    a.complexity == b.complexity &&
    a.added_upstream_complexity == b.added_upstream_complexity &&
    a.best_complexity == b.best_complexity &&
    a.unmatched_complexity == b.unmatched_complexity

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


function value_updates(sc, block::ProgramBlock, branch, new_values)
    if isnothing(block.output_var[2])
        error("Block without output variable: $block")
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
            Set([block]),
            Set(),
            true,
            !isa(block.p, FreeVar),
            nothing,
            nothing,
            nothing,
            nothing,
            nothing,
            nothing,
            Set(),
        )
        return [new_branch], Set()
    else
        entry = get_entry(sc.entries_storage, branch.value_index)
        return updated_branches(
            sc,
            entry,
            new_values,
            block,
            branch,
            return_of_type(block.type),
            !isa(block.p, FreeVar),
        )
    end
end

function value_updates(sc, block::ReverseProgramBlock, branches, new_values)
    out_new_branches = []
    old_constraints = Set()
    new_constraints = Set()
    out_next_blocks = Set()
    for (br, values) in zip(branches, new_values)
        values = collect(values)
        entry = get_entry(sc.entries_storage, br.value_index)
        new_branches, old_constr, new_constr, next_blocks =
            updated_branches(sc, entry, values, block, br, br.type, true)
        union!(old_constraints, old_constr)
        setdiff!(new_constraints, old_constr)
        union!(new_constraints, new_constr)
        append!(out_new_branches, new_branches)
        union!(out_next_blocks, next_blocks)
    end
    return out_new_branches, old_constraints, new_constraints, out_next_blocks
end


function updated_branches(sc, ::ValueEntry, new_values, block, branch, t, is_meaningful)
    if branch.is_known
        return [branch], Set(), Set(), branch.outgoing_blocks
    else
        for child in branch.children
            if child.value_index == branch.value_index && child.is_known
                return [child], branch.constraints, child.constraints, child.outgoing_blocks
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
            Set([block]),
            copy(branch.outgoing_blocks),
            true,
            branch.is_meaningful || is_meaningful,
            nothing,
            nothing,
            branch.complexity,
            nothing,
            branch.complexity,
            0.0,
            Set(),
        )
        for constraint in branch.constraints
            new_constraint = Constraint(copy(constraint.branches), copy(constraint.contexts), copy(constraint.rev_contexts))
            new_constraint.branches[branch.key] = new_branch
            push!(new_branch.constraints, new_constraint)
        end
        return [new_branch], branch.constraints, new_branch.constraints, branch.outgoing_blocks
    end
end


function find_related_branches(sc, branch::EntryBranch, new_entry, new_entry_index)
    possible_parents = []
    for child in branch.children
        if child.is_known
            if child.value_index == new_entry_index
                return [], child
            end
        else
            child_entry = get_entry(sc.entries_storage, child.value_index)
            if match_with_entry(child_entry, new_entry)
                parents, possible_result = find_related_branches(sc, child, new_entry, new_entry_index)
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


function updated_branches(sc, entry, new_values, block, branch, t, is_meaningful)
    complexity_summary = get_complexity_summary(new_values, t)
    new_entry = ValueEntry(t, new_values, complexity_summary, get_complexity(sc, complexity_summary))
    new_entry_index = add_entry(sc.entries_storage, new_entry)
    new_parents, possible_result = find_related_branches(sc, branch, new_entry, new_entry_index)
    if !isnothing(possible_result)
        return [possible_result], branch.constraints, possible_result.constraints, possible_result.outgoing_blocks
    end

    new_branch = EntryBranch(
        new_entry_index,
        branch.key,
        t,
        Set(new_parents),
        Set(),
        Set(),
        [],
        Set([block]),
        copy(branch.outgoing_blocks),
        true,
        branch.is_meaningful || is_meaningful,
        nothing,
        nothing,
        new_entry.complexity,
        nothing,
        new_entry.complexity,
        0.0,
        Set(),
    )
    new_branches = [new_branch]

    for constraint in branch.constraints
        created_branches = tighten_constraint(sc, constraint, new_branch, new_branches)
        append!(new_branches, created_branches)
    end

    return new_branches, branch.constraints, new_branch.constraints, new_branch.outgoing_blocks
end

function _is_ancestor(br_a, br_b)
    if br_a == br_b
        return true
    end
    return any(_is_ancestor(parent_a, br_b) for parent_a in br_a.parents)
end

function intersect_branches(br_a::EntryBranch, br_b::EntryBranch)
    if _is_ancestor(br_a, br_b)
        return br_b
    end
    if _is_ancestor(br_b, br_a)
        return br_a
    end
    return nothing
end

intersect_branches(br, ::Nothing) = br
intersect_branches(::Nothing, br) = br

function get_branch_with_constraints(sc, key, constraints, min_root)
    candidate = nothing
    for constraint in constraints
        if constraints_key(constraint, key)
            cand = get_constrained_branch(constraint, key)
            if isnothing(candidate)
                candidate = cand
            else
                if cand != candidate
                    error("Constraints are not compatible: $candidate, $cand")
                end
            end
        end
    end
    if isnothing(candidate)
        candidate = min_root
    end
    return candidate
end
