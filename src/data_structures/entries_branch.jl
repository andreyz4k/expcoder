
using DataStructures: OrderedDict

mutable struct EntryBranchItem
    value::Entry
    incoming_paths::Vector{OrderedDict{String,AbstractProgramBlock}}
    outgoing_blocks::Set{AbstractProgramBlock}
    is_known::Bool
    is_meaningful::Bool
    min_path_cost::Union{Float64,Nothing}
    complexity_factor::Union{Float64,Nothing}
end


struct EntriesBranch
    values::Dict{String,EntryBranchItem}
    parent::Union{Nothing,EntriesBranch}
    children::Set{EntriesBranch}
end

function iter_options(branch::EntriesBranch, key)
    result = Any[[(branch, branch.values[key])]]
    for child in branch.children
        if haskey(child.values, key)
            push!(result, iter_options(child, key))
        end
    end
    flatten(result)
end

function is_branch_compatible(key, branch, fixed_branches)
    for fixed_branch in fixed_branches
        if haskey(fixed_branch.values, key)
            return fixed_branch == branch
        end
    end
    return true
end

isknown(branch::EntriesBranch, key) = branch.values[key].is_known

function value_updates(sc, block::ProgramBlock, new_values)
    branch = block.output_var[2]
    key = block.output_var[1]
    if isnothing(branch)
        return_type = return_of_type(block.type)
        if is_polymorphic(return_type)
            error("returning polymorphic type from $block")
        end
        entry = ValueEntry(return_type, new_values, get_complexity(sc, new_values, return_type))
        new_branch = EntriesBranch(
            Dict(key => EntryBranchItem(entry, [], Set(), true, !isa(block.p, FreeVar), nothing, nothing)),
            nothing,
            Set(),
        )
        return new_branch, Set()
    else
        return updated_branch(sc, branch, key, branch.values[key].value, new_values, block)
    end
end

function child_outgoing_blocks(branch, new_branch, item)
    result = Set()
    for block in item.outgoing_blocks
        new_inputs = []
        for (k, br) in block.input_vars
            if br == branch && haskey(new_branch.values, k)
                push!(new_inputs, (k, new_branch))
            else
                push!(new_inputs, (k, br))
            end
        end
        push!(result, ProgramBlock(block.p, block.type, block.cost, new_inputs, block.output_var))
    end
    return result
end

function updated_branch(sc, branch::EntriesBranch, key, entry::ValueEntry, new_values, block)
    if branch.values[key].is_known
        return branch, branch.values[key].outgoing_blocks
    else
        for child in branch.children
            if child.values[key].value == entry && child.values[key].is_known
                return child, child.values[key].outgoing_blocks
            end
        end
        new_branch = EntriesBranch(Dict(), branch, Set())
        has_unknowns = false
        for (k, item) in branch.values
            if k == key
                new_branch.values[k] = EntryBranchItem(
                    entry,
                    [],
                    Set(),
                    true,
                    item.is_meaningful || !isa(block.p, FreeVar),
                    nothing,
                    nothing,
                )
            elseif !item.is_known
                has_unknowns = true
                new_branch.values[k] = EntryBranchItem(
                    item.value,
                    [],
                    Set(),
                    item.is_known,
                    item.is_meaningful,
                    item.min_path_cost,
                    item.complexity_factor,
                )
            end
        end
        if has_unknowns
            for (k, item) in new_branch.values
                item.outgoing_blocks = child_outgoing_blocks(branch, new_branch, branch.values[k])
            end
        end
        return new_branch, branch.values[key].outgoing_blocks
    end
end


function updated_branch(sc, branch::EntriesBranch, key, entry::NoDataEntry, new_values, block)
    for child in branch.children
        if child.values[key].is_known && child.values[key].value.values == new_values
            return child, child.values[key].outgoing_blocks
        end
    end
    new_branch = EntriesBranch(Dict(), branch, Set())
    has_unknowns = false
    for (k, item) in branch.values
        if k == key
            t = return_of_type(block.type)
            entry = ValueEntry(t, new_values, get_complexity(sc, new_values, t))
            new_branch.values[k] =
                EntryBranchItem(entry, [], Set(), true, item.is_meaningful || !isa(block.p, FreeVar), nothing, nothing)
        elseif !item.is_known
            has_unknowns = true
            new_branch.values[k] = EntryBranchItem(
                item.value,
                [],
                Set(),
                item.is_known,
                item.is_meaningful,
                item.min_path_cost,
                item.complexity_factor,
            )
        end
    end
    if has_unknowns
        for (k, item) in new_branch.values
            item.outgoing_blocks = child_outgoing_blocks(branch, new_branch, branch.values[k])
        end
    end
    for op in branch.values[key].outgoing_blocks
        i = findfirst(kv -> kv[1] == key, op.input_vars)
        arg_type = arguments_of_type(op.type)[i]
        if is_polymorphic(arg_type)
            context = empty_context
            context, op_type = instantiate(op.type, context)
            for ((k, _), arg_type) in zip(op.input_vars, arguments_of_type(op_type))
                if haskey(new_branch.values, k) && isknown(new_branch, k)
                    context = unify(context, arg_type, new_branch.values[k].value.type)
                end
            end
            context, new_op_type = apply_context(context, op_type)
            for ((k, _), old_type, new_type) in
                zip(op.input_vars, arguments_of_type(op_type), arguments_of_type(new_op_type))
                if k != key && haskey(new_branch.values, k) && !isknown(new_branch, k) && old_type != new_type
                    new_branch.values[k].value = NoDataEntry(new_type)
                end
            end
            new_return = return_of_type(new_op_type)
            if is_polymorphic(new_return)
                error("Return type happened to be polimorphic")
            end
        end
    end
    return new_branch, branch.values[key].outgoing_blocks
end
