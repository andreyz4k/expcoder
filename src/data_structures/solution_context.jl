
mutable struct SolutionContext
    var_data::Dict{String,EntriesBranch}
    target_key::String
    created_vars::Int64
    input_keys::Vector{String}
    updated_options::Set{Tuple{String,EntriesBranch}}
    example_count::Int64
    previous_keys::Dict{String,Set{String}}
    following_keys::Dict{String,Set{String}}
end

function create_starting_context(task::Task)::SolutionContext
    var_data = Dict{String,EntriesBranch}()
    argument_types = arguments_of_type(task.task_type)
    input_keys = []
    previous_keys = Dict{String,Set{String}}()
    following_keys = Dict{String,Set{String}}()
    for (i, (t, values)) in enumerate(zip(argument_types, zip(task.train_inputs...)))
        key = "\$i$i"
        entry = ValueEntry(t, collect(values))
        var_data[key] = EntriesBranch(Dict(key => EntryBranchItem(entry, Dict(), Set(), true)), nothing, Set())
        push!(input_keys, key)
        previous_keys[key] = Set([key])
        following_keys[key] = Set([key])
    end
    target_key = "out"
    entry = ValueEntry(return_of_type(task.task_type), task.train_outputs)
    var_data[target_key] = EntriesBranch(Dict(target_key => EntryBranchItem(entry, Dict(), Set(), false)), nothing, Set())
    previous_keys[target_key] = Set([target_key])
    following_keys[target_key] = Set([target_key])
    example_count = length(task.train_outputs)
    return SolutionContext(var_data, target_key, 0, input_keys, Set(), example_count, previous_keys, following_keys)
end

function reset_updated_keys(ctx::SolutionContext)
    ctx.updated_options = Set()
end

function create_next_var(solution_ctx::SolutionContext)
    solution_ctx.created_vars += 1
end

function insert_operation(sc::SolutionContext, updates)
    for (out_key, (bl, out_branch, input_branches)) in updates
        if bl.output_var[2] != out_branch
            if isnothing(out_branch.parent)
                sc.var_data[out_key] = out_branch
                for k in keys(out_branch.values)
                    push!(sc.updated_options, (k, out_branch))
                end
            elseif !in(out_branch, out_branch.parent.children)
                push!(out_branch.parent.children, out_branch)
                for k in keys(out_branch.values)
                    push!(sc.updated_options, (k, out_branch))
                end
            end
        end
        if bl.output_var[2] != out_branch || any(inp_br != input_branches[k] for (k, inp_br) in bl.input_vars)
            bl = ProgramBlock(
                bl.p,
                bl.type,
                bl.cost,
                [(k, input_branches[k]) for (k, _) in bl.input_vars],
                (bl.output_var[1], out_branch),
            )
            # @info "Adding block"
            # @info bl
        end
        if !haskey(sc.previous_keys, out_key)
            sc.previous_keys[out_key] = Set([out_key])
        end
        if !haskey(sc.following_keys, out_key)
            sc.following_keys[out_key] = Set([out_key])
        end
        paths_count = 1
        for (k, inp_branch) in bl.input_vars
            if !haskey(sc.var_data, k)
                sc.var_data[k] = inp_branch
                push!(sc.updated_options, (k, inp_branch))
            end
            item = inp_branch.values[k]

            push!(item.outgoing_blocks, bl)
            if !isempty(item.incoming_blocks)
                paths_count *= sum(values(item.incoming_blocks))
            elseif !item.is_known
                paths_count = 0
            end
            if !haskey(sc.following_keys, k)
                sc.following_keys[k] = Set([k])

            end
            union!(sc.following_keys[k], sc.following_keys[out_key])

            if !haskey(sc.previous_keys, k)
                sc.previous_keys[k] = Set([k])
            end
            union!(sc.previous_keys[out_key], sc.previous_keys[k])
        end
        out_branch.values[out_key].incoming_blocks[bl] = paths_count
    end
end

using IterTools: imap

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

function target_inputs(sc::SolutionContext)
    result = Dict()
    for (br, option) in iter_options(sc.var_data[sc.target_key], sc.target_key)
        if option.is_known
            merge!(result, option.incoming_blocks)
        end
    end
    result
end

keys_in_loop(sc, known_key, unknown_key) =
    !isempty(intersect(sc.previous_keys[known_key], sc.following_keys[unknown_key]))
