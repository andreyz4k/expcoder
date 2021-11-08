
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
        var_data[key] = EntriesBranch(
            Dict(key => EntryBranchItem(entry, [OrderedDict{String,ProgramBlock}()], Set(), true, true)),
            nothing,
            Set(),
        )
        push!(input_keys, key)
        previous_keys[key] = Set([key])
        following_keys[key] = Set([key])
    end
    target_key = "out"
    entry = ValueEntry(return_of_type(task.task_type), task.train_outputs)
    var_data[target_key] =
        EntriesBranch(Dict(target_key => EntryBranchItem(entry, [], Set(), false, false)), nothing, Set())
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
    new_paths = Dict()
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
        is_new_block = false
        original_block = bl
        if bl.output_var[2] != out_branch || any(inp_br != input_branches[k] for (k, inp_br) in bl.input_vars)
            # @info "Old block $bl"
            bl = ProgramBlock(
                bl.p,
                bl.type,
                bl.cost,
                [(k, input_branches[k]) for (k, _) in bl.input_vars],
                (bl.output_var[1], out_branch),
            )
            # @info "New block $bl"
            is_new_block = true
            # @info "Adding block"
            # @info bl
        end
        if !haskey(sc.previous_keys, out_key)
            sc.previous_keys[out_key] = Set([out_key])
        end
        if !haskey(sc.following_keys, out_key)
            sc.following_keys[out_key] = Set([out_key])
        end

        if all(inp_branch.values[k].is_known for (k, inp_branch) in bl.input_vars)
            if is_new_block
                # @info "Getting paths for new block $bl"
                new_block_paths = [OrderedDict{String,ProgramBlock}()]
                for (ik, inp_branch) in bl.input_vars
                    next_paths = []
                    for path in new_block_paths
                        for inp_path in inp_branch.values[ik].incoming_paths
                            bad_path = false
                            for (k, b) in inp_path
                                if haskey(path, k) && path[k] != b
                                    bad_path = true
                                    @warn "Paths mismatch" path inp_path
                                    break
                                end
                            end
                            if !bad_path
                                new_path = merge(path, inp_path)
                                push!(next_paths, new_path)
                            end
                        end
                    end
                    new_block_paths = next_paths
                end
                for path in new_block_paths
                    path[out_key] = bl
                end
            else
                # @info "Getting paths for existing block $bl"
                new_block_paths = []
                for l = 1:length(bl.input_vars)
                    if !haskey(new_paths, bl.input_vars[l])
                        continue
                    end
                    new_block_paths_part = [OrderedDict{String,ProgramBlock}()]
                    for (i, (ik, inp_branch)) in enumerate(bl.input_vars)
                        next_paths = []
                        for path in new_block_paths_part
                            if i == l
                                inp_paths = new_paths[(ik, inp_branch)]
                            elseif i < l && haskey(new_paths, (ik, inp_branch))
                                inp_paths =
                                    filter(!in(path, new_paths[(ik, inp_branch)]), inp_branch.values[ik].incoming_paths)
                            else
                                inp_paths = inp_branch.values[ik].incoming_paths
                            end
                            for inp_path in inp_paths
                                bad_path = false
                                for (k, b) in inp_path
                                    if haskey(path, k) && path[k] != b
                                        bad_path = true
                                        @warn "Paths mismatch" path inp_path
                                        break
                                    end
                                end
                                if !bad_path
                                    new_path = merge(path, inp_path)
                                    push!(next_paths, new_path)
                                end
                            end
                        end
                        new_block_paths_part = next_paths
                    end
                    for path in new_block_paths_part
                        path[out_key] = bl
                    end
                    # @info new_block_paths_part
                    append!(new_block_paths, new_block_paths_part)
                end
            end
            # @info new_block_paths
            append!(out_branch.values[out_key].incoming_paths, new_block_paths)
            new_paths[(out_key, out_branch)] = new_block_paths
            if !out_branch.values[out_key].is_meaningful && !isa(bl.p, FreeVar)
                out_branch.values[out_key].is_meaningful = true
            end
        end

        for (k, inp_branch) in bl.input_vars
            if !haskey(sc.var_data, k)
                sc.var_data[k] = inp_branch
                push!(sc.updated_options, (k, inp_branch))
            end
            item = inp_branch.values[k]

            if is_new_block && in(original_block, item.outgoing_blocks)
                delete!(item.outgoing_blocks, original_block)
            end
            push!(item.outgoing_blocks, bl)

            if !haskey(sc.following_keys, k)
                sc.following_keys[k] = Set([k])
            end
            union!(sc.following_keys[k], sc.following_keys[out_key])

            if !haskey(sc.previous_keys, k)
                sc.previous_keys[k] = Set([k])
            end
            union!(sc.previous_keys[out_key], sc.previous_keys[k])
        end
    end
    new_full_paths = []
    for (br, option) in iter_options(sc.var_data[sc.target_key], sc.target_key)
        if option.is_known && haskey(new_paths, (sc.target_key, br))
            append!(new_full_paths, new_paths[(sc.target_key, br)])
            # @info Dict((k, hash(b)) => v for ((k, b), v) in new_paths)
            # @info option.incoming_paths
        end
    end
    return new_full_paths
end

using IterTools: imap

function iter_known_vars(sc::SolutionContext)
    flatten(imap(sc.var_data) do (key, entries_branch)
        ((key, branch, option) for (branch, option) in iter_options(entries_branch, key) if option.is_known)
    end)
end

function iter_known_meaningful_vars(sc::SolutionContext)
    flatten(
        imap(sc.var_data) do (key, entries_branch)
            ((key, branch, option) for (branch, option) in iter_options(entries_branch, key) if option.is_meaningful)
        end,
    )
end

function iter_unknown_vars(sc::SolutionContext)
    flatten(imap(sc.var_data) do (key, entries_branch)
        ((key, branch, option) for (branch, option) in iter_options(entries_branch, key) if !option.is_known)
    end)
end

keys_in_loop(sc, known_key, unknown_key) =
    !isempty(intersect(sc.previous_keys[known_key], sc.following_keys[unknown_key]))
