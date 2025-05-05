
using MetaGraphsNext
using Graphs
using Dates

function sort_vars_and_blocks(sc::SolutionContext)
    output_var = sc.branch_vars[sc.target_branch_id]
    input_vars = collect(keys(sc.input_keys))
    var_groups = [input_vars, [output_var]]
    for var_id in output_var+1:sc.vars_count[]
        prev_vars = get_connected_to(sc.previous_vars, var_id)
        foll_vars = get_connected_from(sc.previous_vars, var_id)
        min_i = 0
        max_i = length(var_groups) + 1
        for (i, group) in enumerate(var_groups)
            if !isempty(intersect(prev_vars, group))
                min_i = i + 1
            end
            if !isempty(intersect(foll_vars, group))
                max_i = min(max_i, i - 1)
            end
        end
        if min_i <= max_i
            if max_i == 0
                insert!(var_groups, 1, [var_id])
            elseif max_i <= length(var_groups)
                push!(var_groups[max_i], var_id)
            elseif min_i == length(var_groups) + 1
                group = var_groups[end]
                prev_vars = intersect(prev_vars, group)
                new_group = setdiff(group, prev_vars)
                push!(new_group, var_id)
                var_groups[end] = collect(prev_vars)
                push!(var_groups, new_group)
            elseif min_i == 0
                push!(var_groups[1], var_id)
            else
                push!(var_groups[min_i], var_id)
            end
        elseif min_i == max_i + 1
            insert!(var_groups, min_i, [var_id])
        else
            prev_groups = []
            next_groups = []
            for j in max_i+1:min_i-1
                group = splice!(var_groups, max_i + 1)
                prev_group_vars = intersect(prev_vars, group)
                next_group_vars = setdiff(group, prev_group_vars)
                if !isempty(prev_group_vars)
                    push!(prev_groups, prev_group_vars)
                end
                if !isempty(next_group_vars)
                    push!(next_groups, next_group_vars)
                end
            end
            for group in reverse(next_groups)
                insert!(var_groups, max_i + 1, group)
            end
            insert!(var_groups, max_i + 1, [var_id])
            for group in reverse(prev_groups)
                insert!(var_groups, max_i + 1, group)
            end
        end
    end
    max_depth = length(var_groups)
    out_var_depths = Dict{UInt64,Tuple{Int,Float64}}()
    out_block_depths = Dict{UInt64,Float64}()
    for (i, group) in enumerate(var_groups)
        for var_id in group
            out_var_depths[var_id] = (i, (i - max_depth / 2) * 20 + (rand() - 0.5) * 10)
        end
    end
    for block_id in 1:length(sc.blocks)
        block = sc.blocks[UInt64(block_id)]
        if isa(block, ProgramBlock)
            i = out_var_depths[block.output_var][1]
            out_block_depths[block_id] = (i - max_depth / 2) * 20 - 10 + (rand() - 0.5) * 10
        else
            i = out_var_depths[block.input_vars[1]][1]
            out_block_depths[block_id] = (i - max_depth / 2) * 20 + 10 + (rand() - 0.5) * 10
        end
    end
    return out_var_depths, out_block_depths
end

function export_solution_context(sc::SolutionContext, previous_traces = nothing)
    data = MetaGraph(
        DiGraph();  # underlying graph structure
        label_type = String,  # branch id
        vertex_data_type = Dict,
        edge_data_type = Dict,
        # graph_data = "solution context",  # tag for the whole graph
        # weight_function = ed -> ed["cost"],
        # default_weight = Inf,
    )
    vars_depths, blocks_depths = sort_vars_and_blocks(sc)
    for branch_id in 1:sc.branches_count[]
        entry_id = sc.branch_entries[branch_id]
        entry = sc.entries[entry_id]
        vertex_dict = Dict(
            "_kind" => "branch",
            "_var_id" => sc.branch_vars[branch_id],
            "_is_unknown" => sc.branch_is_unknown[branch_id],
            "_is_explained" => sc.branch_is_explained[branch_id],
            "_is_not_copy" => sc.branch_is_not_copy[branch_id],
            "_is_not_const" => sc.branch_is_not_const[branch_id],
            "_has_data" => entry_has_data(entry),
            "_entry_id" => entry_id,
            "_type" => string(sc.types[entry.type_id]),
            "_entry_type" => typeof(entry),
            "_complexity" => sc.complexities[branch_id],
            "_unknown_complexity_factor" => sc.unknown_complexity_factors[branch_id],
            "_explained_complexity_factor" => sc.explained_complexity_factors[branch_id],
            "_unknown_min_path_cost" => sc.unknown_min_path_costs[branch_id],
            "_explained_min_path_cost" => sc.explained_min_path_costs[branch_id],
            "_unmatched_complexity" => sc.unmatched_complexities[branch_id],
            "_added_upstream_complexity" => sc.added_upstream_complexities[branch_id],
            "_unused_explained_complexity" => sc.unused_explained_complexities[branch_id],
            "_depth" => get(vars_depths, sc.branch_vars[branch_id], (-1, -200))[2] + rand(),
            "_depth_index" => get(vars_depths, sc.branch_vars[branch_id], (-1, -200))[1],
            "_related_explained_branches" =>
                string(get_connected_from(sc.related_explained_complexity_branches, branch_id)),
            "_related_unknown_branches" =>
                string(get_connected_from(sc.related_unknown_complexity_branches, branch_id)),
            "_prev_entries" => string(get_connected_from(sc.branch_prev_entries, branch_id)),
            "_following_entries" => string(get_connected_from(sc.branch_foll_entries, branch_id)),
        )
        if !isa(entry, NoDataEntry)
            vertex_dict["_entry_value"] = string(entry.values)
        end
        var_count = type_var_count(sc.types[entry.type_id])
        vertex_dict["_var_count"] = var_count
        if haskey(sc.entry_queues_reverse, entry_id) && !isempty(sc.entry_queues_reverse[entry_id])
            vertex_dict["_queue_explained_size"] = length(sc.entry_queues_reverse[entry_id])
            queue_min_cost = peek(sc.entry_queues_reverse[entry_id])[2]
            vertex_dict["_queue_explained_min_cost"] = queue_min_cost
            if sc.branch_is_explained[branch_id] &&
               sc.branch_is_not_copy[branch_id] &&
               !isnothing(sc.explained_min_path_costs[branch_id])
                queue_full_cost =
                    (
                        sc.explained_min_path_costs[branch_id]^sc.hyperparameters["path_cost_power"] +
                        queue_min_cost^sc.hyperparameters["block_cost_power"]
                    ) * sc.explained_complexity_factors[branch_id]^sc.hyperparameters["complexity_power"]

                queue_full_cost =
                    queue_full_cost *
                    (
                        (var_count + 1) * sc.hyperparameters["type_var_penalty_mult"]
                    )^sc.hyperparameters["type_var_penalty_power"]
                vertex_dict["_queue_explained_full_cost"] = queue_full_cost
            end
            if haskey(sc.pq_reverse, entry_id)
                vertex_dict["_queue_explained_priority"] = sc.pq_reverse[entry_id]
            end
            # if branch_id == 1
            #     for (i, (bp, pr)) in enumerate(sc.branch_queues_explained[branch_id])
            #         if i > 2000
            #             break
            #         end
            #         @info "$pr $bp"
            #     end
            # end
        end
        if haskey(sc.entry_queues_forward, entry_id) && !isempty(sc.entry_queues_forward[entry_id])
            vertex_dict["_queue_unknown_size"] = length(sc.entry_queues_forward[entry_id])
            queue_min_cost = peek(sc.entry_queues_forward[entry_id])[2]
            vertex_dict["_queue_unknown_min_cost"] = queue_min_cost
            if sc.branch_is_unknown[branch_id]
                queue_full_cost =
                    (
                        sc.unknown_min_path_costs[branch_id]^sc.hyperparameters["path_cost_power"] +
                        queue_min_cost^sc.hyperparameters["block_cost_power"]
                    ) * sc.unknown_complexity_factors[branch_id]^sc.hyperparameters["complexity_power"]
                if sc.branch_is_explained[branch_id]
                    queue_full_cost =
                        queue_full_cost^sc.hyperparameters["explained_penalty_power"] *
                        sc.hyperparameters["explained_penalty_mult"]
                end

                queue_full_cost =
                    queue_full_cost *
                    (
                        (var_count + 1) * sc.hyperparameters["type_var_penalty_mult"]
                    )^sc.hyperparameters["type_var_penalty_power"]
                vertex_dict["_queue_unknown_full_cost"] = queue_full_cost
            end
            if haskey(sc.pq_forward, entry_id)
                vertex_dict["_queue_unknown_priority"] = sc.pq_forward[entry_id]
            end
        end
        filter!(kv -> !isnothing(kv[2]), vertex_dict)
        add_vertex!(data, string(branch_id), vertex_dict)
    end

    for branch_id in 1:sc.branches_count[]
        for parent_id in get_connected_to(sc.branch_children, branch_id)
            add_edge!(data, string(parent_id), string(branch_id), Dict("_type" => "child"))
        end
    end

    prev_trace_blocks = []
    prev_trace_rev_blocks = []
    if !isnothing(previous_traces)
        for (trace, _) in previous_traces
            p = parse_program(trace.hit_program)
            in_blocks, out_blocks, copy_blocks, vars_mapping, var_types = _extract_blocks(sc.task, p, false)
            for (var, blocks) in Iterators.flatten([out_blocks, in_blocks])
                for (i, block) in enumerate(blocks)
                    if isa(block.p, FreeVar)
                        continue
                    end
                    if isa(block, ProgramBlock)
                        if all(!is_on_path(block.p, b.p, Dict()) for b in prev_trace_blocks)
                            push!(prev_trace_blocks, block)
                        end
                    else
                        if all(!is_on_path(block.p, b.p, Dict()) for b in prev_trace_rev_blocks)
                            push!(prev_trace_rev_blocks, block)
                        end
                    end
                end
            end
        end
    end

    for block_copy_id in 1:sc.block_copies_count[]
        outs = get_connected_to(sc.branch_incoming_blocks, block_copy_id)
        if isempty(outs)
            @info "block $block_copy_id has no outputs"
            inputs = get_connected_to(sc.branch_outgoing_blocks, block_copy_id)
            @info inputs
            block_id = first(values(inputs))
            @info sc.blocks[block_id]
        end
        output_branches = keys(outs)
        block_id = first(values(outs))
        input_branches = keys(get_connected_to(sc.branch_outgoing_blocks, block_copy_id))
        block = sc.blocks[block_id]
        block_dict = Dict(
            "_kind" => "block",
            "_block_id" => block_id,
            "_block_copy_id" => block_copy_id,
            "_block_type" => typeof(block),
            "_p" => string(block.p),
            "_type" => string(block.type),
            "_cost" => block.cost,
            "_depth" => get(blocks_depths, block_id, -200) + rand(),
            "_root_branch" => sc.block_root_branches[block_id],
        )

        if isa(block, ProgramBlock)
            block_dict["_is_reversible"] = block.is_reversible
            block_dict["_var_id"] = block.output_var
            block_dict["_depth_index"] = get(vars_depths, block.output_var, (-1, -200))[1]
            block_dict["_is_on_prev_trace"] =
                !isa(block.p, FreeVar) && any(is_on_path(block.p, b.p, Dict()) for b in prev_trace_blocks)
        else
            block_dict["_var_id"] = block.input_vars[1]
            block_dict["_depth_index"] = get(vars_depths, block.input_vars[1], (-1, -200))[1]
            block_dict["_is_on_prev_trace"] = any(is_on_path(block.p, b.p, Dict()) for b in prev_trace_rev_blocks)
        end

        add_vertex!(data, "b$block_copy_id", block_dict)
        for input_branch in input_branches
            add_edge!(data, string(input_branch), "b$block_copy_id", Dict("_type" => "input"))
        end
        for output_branch in output_branches
            add_edge!(data, "b$block_copy_id", string(output_branch), Dict("_type" => "output"))
        end
    end

    # @info data
    # filename = "solution_dumps/$(replace(task.name, " " => "_"))_p_$(sc.hyperparameters["path_cost_power"])_c_$(sc.hyperparameters["complexity_power"])_set_$(sc.type_weights["set"])_tuple_$(sc.type_weights["tuple2"])_list_$(sc.type_weights["list"])_any_$(sc.type_weights["any"])_$(now()).dot"
    filename = "solution_dumps/$(replace(sc.task.name, " " => "_"))_$(now()).dot"
    if !isdir("solution_dumps")
        mkdir("solution_dumps")
    end
    savegraph(filename, data, DOTFormat())
    @info filename
    # @info read(filename, String)
end
