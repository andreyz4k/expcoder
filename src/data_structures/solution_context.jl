
mutable struct SolutionContext
    var_data::Dict{String,EntriesBranch}
    target_key::String
    created_vars::Int64
    input_keys::Vector{String}
    updated_options::Set{Tuple{String,EntriesBranch}}
    example_count::Int64
    previous_keys::Dict{String,Set{String}}
end

function create_starting_context(task::Task)::SolutionContext
    var_data = Dict{String,EntriesBranch}()
    argument_types = arguments_of_type(task.task_type)
    input_keys = []
    previous_keys = Dict{String,Set{String}}()
    for (i, (t, values)) in enumerate(zip(argument_types, zip(task.train_inputs...)))
        key = "\$i$i"
        entry = ValueEntry(t, collect(values))
        var_data[key] = EntriesBranch(Dict(key => EntryBranchItem(entry, Dict(), [], true)), nothing, [])
        push!(input_keys, key)
        previous_keys[key] = Set([key])
    end
    target_key = "out"
    entry = ValueEntry(return_of_type(task.task_type), task.train_outputs)
    var_data[target_key] = EntriesBranch(Dict(target_key => EntryBranchItem(entry, Dict(), [], false)), nothing, [])
    previous_keys[target_key] = Set([target_key])
    example_count = length(task.train_outputs)
    return SolutionContext(var_data, target_key, 0, input_keys, Set(), example_count, previous_keys)
end

function reset_updated_keys(ctx::SolutionContext)
    ctx.updated_options = Set()
end

function create_next_var(solution_ctx::SolutionContext)
    solution_ctx.created_vars += 1
end

function insert_operation(sc::SolutionContext, updates)
    for (key, (bl, branch, input_branches)) in updates
        if bl.output_var[2] != branch
            bl = ProgramBlock(
                bl.p,
                bl.type,
                bl.input_vars,
                (bl.output_var[1], branch)
            )
            for k in keys(branch.values)
                push!(sc.updated_options, (k, branch))
            end
        end
        if isnothing(branch.parent)
            sc.var_data[key] = branch
        else
            push!(branch.parent.children, branch)
        end
        for inp_branch in input_branches
            for k in keys(inp_branch.values)
                if !haskey(sc.var_data, k)
                    sc.var_data[k] = inp_branch
                    push!(sc.updated_options, (k, inp_branch))
                end
            end
        end
        if !haskey(sc.previous_keys, key)
            sc.previous_keys[key] = Set([key])
        end
        paths_count = 1
        for k in bl.input_vars
            for inp_branch in input_branches
                if haskey(inp_branch.values, k)
                    item = inp_branch.values[k]
                    push!(item.outgoing_blocks, bl)
                    if !isempty(item.incoming_blocks)
                        paths_count *= sum(values(item.incoming_blocks))
                    end
                    break
                end
            end
            if !haskey(sc.previous_keys, k)
                sc.previous_keys[k] = Set([k])
            end
            union!(sc.previous_keys[key], sc.previous_keys[k])
        end
        branch.values[key].incoming_blocks[bl] = paths_count
    end
end

using IterTools:imap

function iter_known_vars(sc::SolutionContext)
    flatten(imap(sc.var_data) do (key, entries_branch)
        ((key, branch, option) for (branch, option) in iter_options(entries_branch, key) if option.is_known)
    end)
end


function iter_unknown_vars(sc::SolutionContext)
    flatten(imap(sc.var_data) do (key, entries_branch)
        ((key, branch, option) for (branch, option) in iter_options(entries_branch, key) if !option.is_known)
    end)
end
