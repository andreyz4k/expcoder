
mutable struct SolutionContext
    var_data::Dict{String,EntriesBranch}
    target_key::String
    created_vars::Int64
    input_keys::Vector{String}
    updated_options::Set{Tuple{String,EntriesBranch}}
    example_count::Int64
end

function create_starting_context(task::Task)::SolutionContext
    var_data = Dict{String,EntriesBranch}()
    argument_types = arguments_of_type(task.task_type)
    input_keys = []
    for (i, (t, values)) in enumerate(zip(argument_types, zip(task.train_inputs...)))
        key = "\$i$i"
        entry = ValueEntry(t, collect(values))
        var_data[key] = EntriesBranch(Dict(key => EntryBranchItem(entry, Dict(), [], true)), nothing, [])
        push!(input_keys, key)
    end
    target_key = "out"
    entry = ValueEntry(return_of_type(task.task_type), task.train_outputs)
    var_data[target_key] = EntriesBranch(Dict(target_key => EntryBranchItem(entry, Dict(), [], false)), nothing, [])
    example_count = length(task.train_outputs)
    return SolutionContext(var_data, target_key, 0, input_keys, Set(), example_count)
end

function reset_updated_keys(ctx::SolutionContext)
    ctx.updated_options = Set()
end

function create_next_var(solution_ctx::SolutionContext)
    solution_ctx.created_vars += 1
    solution_ctx.created_vars
end

# function isknown(ctx::SolutionContext, key)
#     any(option.is_known for (_, option) in ctx.var_data[key].options)
# end

function isknown(ctx::SolutionContext, key, entry_hash)
    ctx.var_data[key].options[entry_hash].is_known
end

function set_unknown(ctx::SolutionContext, key, entry)
    if !haskey(ctx.var_data, key)
        ctx.var_data[key] = VarData(Dict())
    end
    if !haskey(ctx.var_data[key].options, entry)
        ctx.var_data[key].options[hash(entry)] = Option(entry, nothing, [], Dict(), [], true, false)
        push!(ctx.updated_options, (key, hash(entry)))
    end
end

function insert_operation_no_updates(sc::SolutionContext, block)
    sc.var_data[block.output[1]].options[block.output[2]].incoming_blocks[block] = 0
    for key in block.inputs
        for (_, option) in sc.var_data[key].options
            push!(option.outgoing_blocks, block)
        end
    end
end

using IterTools:imap

function iter_known_vars(sc::SolutionContext)
    flatten(imap(sc.var_data) do (key, var_data)
        ((key, entry_hash, option) for (entry_hash, option) in var_data.options if option.is_known)
    end)
end


function iter_unknown_vars(sc::SolutionContext)
    flatten(imap(sc.var_data) do (key, var_data)
        ((key, entry_hash, option) for (entry_hash, option) in var_data.options if !option.is_known)
    end)
end
