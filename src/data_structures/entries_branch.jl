
struct EntryBranchItem
    value::Entry
    incoming_blocks::Dict{ProgramBlock,Int64}
    outgoing_blocks::Vector{ProgramBlock}
    is_known::Bool
end

struct EntriesBranch
    values::Dict{String,EntryBranchItem}
    parent::Union{Nothing,EntriesBranch}
    children::Vector{EntriesBranch}
end

function iter_options(branch::EntriesBranch, key)
    result = [[(branch, branch.values[key])]]
    for child in branch.children
        push!(result, iter_options(child, key))
    end
    flatten(result)
end

function is_branch_compatible(key, branch, fixed_vars)
    for fixed_branch in unique(values(fixed_vars))
        if haskey(fixed_branch.values, key)
            return fixed_branch == branch
        end
    end
    return true
end

isknown(branch, key) = !isnothing(branch) && branch.values[key].is_known

function value_updates(block::ProgramBlock, new_values)
    branch = block.output_var[2]
    key = block.output_var[1]
    if isnothing(branch)
        return_type = return_of_type(block.type)
        if is_polymorphic(return_type)
            error("returning polymorphic type from $block")
        end
        return EntriesBranch(
            Dict(
                key => EntryBranchItem(
                    ValueEntry(return_type, new_values),
                    Dict(),
                    [],
                    true,
                )
            ),
            nothing,
            [],
        )
    else
        return_type = return_of_type(block.type)
        return updated_branch(branch, key, branch.values[key], new_values, return_type)
    end
end

function updated_branch(branch::EntriesBranch, key, entry::ValueEntry, new_values, t)
    if branch.values[key].is_known
        return branch
    else
        for child in branch.children
            if child.values[key].value == entry && child.values[key].is_known
                return child
            end
        end
        new_branch = EntriesBranch(
            Dict(),
            branch,
            []
        )
        for (k, item) in branch.values
            if k == key
                new_branch.values[k] = EntryBranchItem(
                    entry,
                    copy(item.incoming_blocks),
                    copy(item.outgoing_blocks),
                    true,
                )
            else
                new_branch.values[k] = EntryBranchItem(
                    item.value,
                    copy(item.incoming_blocks),
                    copy(item.outgoing_blocks),
                    item.is_known
                )
            end
        end
        return new_branch
    end
end

function updated_branch(branch::EntriesBranch, key, entry::NoDataEntry, new_values, t)
    for child in branch.children
        if child.values[key].is_known && child.values[key].value.values == new_values
            return child
        end
    end
    new_branch = EntriesBranch(
        Dict(),
        branch,
        [],
    )
    for (k, item) in branch.values
        if k == key
            new_branch.values[k] = EntryBranchItem(
                ValueEntry(t, new_values),
                copy(item.incoming_blocks),
                copy(item.outgoing_blocks),
                true,
            )
        else
            new_branch.values[k] = EntryBranchItem(
                item.value,
                copy(item.incoming_blocks),
                copy(item.outgoing_blocks),
                item.is_known
            )
        end
    end
    for op in branch.values[key].outgoing_blocks
        i = findfirst(k -> k == key, op.input_vars)
        arg_type = arguments_of_type(op.type)[i]
        if is_polymorphic(arg_type)
            context = empty_context
            context, op_type = instantiate(op.type, context)
            for (k, arg_type) in zip(op.input_vars, arguments_of_type(op_type))
                if haskey(new_branch.values, k) && isknown(new_branch, k)
                    context = unify(context, arg_type, new_branch.values[k].value.type)
                end
            end
            context, new_op_type = apply_context(context, op_type)
            for (k, old_type, new_type) in zip(op.input_vars, arguments_of_type(op_type), arguments_of_type(new_op_type))
                if k != key && haskey(new_branch, k) && !isknown(new_branch, k) && old_type != new_type
                    new_branch.values[k] = EntryBranchItem(
                        NoDataEntry(new_type),
                        new_branch.values[k].incoming_blocks,
                        new_branch.values[k].outgoing_blocks,
                        new_branch.values[k].is_known
                    )
                end
            end
            new_return = return_of_type(new_op_type)
            if is_polymorphic(new_return)
                error("Return type happened to be polimorphic")
            end
        end
    end
    return new_branch
end
