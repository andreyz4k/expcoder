
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
    branch.outgoing_blocks,
    ", ",
    branch.is_known,
    ", ",
    branch.is_meaningful,
    ", ",
    branch.min_path_cost,
    ", ",
    branch.complexity_factor,
    ")",
)

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
        return updated_branches(
            sc,
            entry,
            new_values,
            block.output_var[2],
            return_of_type(block.type),
            !isa(block.p, FreeVar),
        )
    end
end

function value_updates(sc, block::ReverseProgramBlock, new_values)
    out_new_branches = []
    out_next_blocks = Set()
    for ((_, br), values) in zip(block.output_vars, new_values)
        values = collect(values)
        entry = get_entry(sc.entries_storage, br.value_index)
        new_branches, next_blocks = updated_branches(sc, entry, values, br, br.type, true)
        append!(out_new_branches, new_branches)
        union!(out_next_blocks, next_blocks)
    end
    return out_new_branches, out_next_blocks
end


function updated_branches(sc, ::ValueEntry, new_values, branch, t, is_meaningful)
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
            branch.is_meaningful || is_meaningful,
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


function updated_branches(sc, entry::NoDataEntry, new_values, branch, t, is_meaningful)
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
        branch.is_meaningful || is_meaningful,
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
