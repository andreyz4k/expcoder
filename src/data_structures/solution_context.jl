
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
end

function insert_operation(sc::SolutionContext, block::ProgramBlock, outputs)
    @info sc
    @info block
    @info outputs
    for (key, (bl, branch, input_branches)) in outputs
        if bl.output_var[2] != branch
            bl = ProgramBlock(
                bl.p,
                bl.type,
                bl.input_vars,
                (bl.output_var[1], branch)
            )
        end
        if isnothing(branch.parent)
            sc.var_data[key] = branch
        else
            push!(branch.parent.children, branch)
        end
        push!(sc.updated_options, (key, branch))
        paths_count = 1
        for k in bl.input_vars
            for branch in input_branches
                if haskey(branch.values, k)
                    item = branch.values[k]
                    push!(item.outgoing_blocks, bl)
                    if !isempty(item.incoming_blocks)
                        paths_count *= sum(values(item.incoming_blocks))
                    end
                    break
                end
            end
        end
        branch.values[key].incoming_blocks[bl] = paths_count
    end
    @info sc
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
