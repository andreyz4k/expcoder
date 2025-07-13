
function build_manual_solution(task_name, guiding_model_server, grammar)
    all_tasks = get_arc_tasks()
    task = first(filter(t -> t.name == task_name, all_tasks))
    solutions = JSON.parsefile(joinpath(@__DIR__, "..", "data", "partial_solutions.json"))
    partial_solution = join(solutions[task_name][1], " ")

    register_channel = guiding_model_server.worker_register_channel
    register_response_channel = guiding_model_server.worker_register_result_channel
    task_name = "$(task.name)_$(randstring(6))"
    put!(register_channel, task_name)

    while true
        reg_task_name, request_channel, result_channel, end_tasks_channel = take!(register_response_channel)
        if reg_task_name == task_name
            @info "Building partial manual solution for $(task.name)"
            @time build_partial_solution(
                task,
                task_name,
                partial_solution,
                (request_channel, result_channel, end_tasks_channel),
                grammar,
            )
            return
        else
            put!(register_response_channel, (reg_task_name, request_channel, result_channel, end_tasks_channel))
            sleep(0.01)
        end
    end
end

function build_manual_solution(task_name, guiding_model_server::PythonGuidingModelServer, grammar)
    all_tasks = get_arc_tasks()
    task = first(filter(t -> t.name == task_name, all_tasks))
    solutions = JSON.parsefile(joinpath(@__DIR__, "..", "data", "partial_solutions.json"))
    partial_solution = join(solutions[task_name][1], " ")

    redis_db = guiding_model_server.model.redis_db
    conn = get_redis_connection(redis_db)
    task_name = "$(task.name)_$(randstring(6))"

    @info "Building partial manual solution for $(task.name)"
    @time build_partial_solution(task, task_name, partial_solution, conn, grammar)
    return
end

function build_partial_solution(task::Task, task_name, target_solution, guiding_model_channels, grammar, timeout = 20)
    verbose_test = false
    max_free_parameters = 10
    run_context = Dict{String,Any}("program_timeout" => 1, "timeout" => 40)

    type_weights = Dict(
        "int" => 1.0,
        "list" => 1.0,
        "color" => 1.0,
        "bool" => 1.0,
        "grid" => 1.0,
        "tuple2" => 1.0,
        "set" => 1.0,
        "any" => 1.0,
        "either" => 0.0,
    )

    hyperparameters = Dict(
        "path_cost_power" => 1.0,
        "complexity_power" => 1.0,
        "block_cost_power" => 1.0,
        "explained_penalty_power" => 1.0,
        "explained_penalty_mult" => 5.0,
        "match_duplicates_penalty" => 3.0,
        "type_var_penalty_mult" => 1.0,
        "type_var_penalty_power" => 1.0,
    )

    target_program = parse_program(target_solution)

    start_time = time()

    # verbose_test = false
    sc = create_starting_context(task, task_name, type_weights, hyperparameters, run_context, verbose_test, false)

    try
        rev_blocks, out_blocks, copy_blocks, vars_mapping, var_types =
            _extract_blocks(sc.types, task, target_program, verbose_test)
        rev_vars_mapping = Dict(v => k for (k, v) in vars_mapping)

        enqueue_updates(sc, guiding_model_channels, grammar)

        if verbose_test
            @info rev_blocks
            @info out_blocks
            @info copy_blocks
        end

        save_changes!(sc, 0)

        inner_mapping = Dict{UInt64,UInt64}()
        rev_inner_mapping = Dict{UInt64,UInt64}()
        for (arg, _) in task.task_type.arguments
            for (v, a) in sc.input_keys
                if a == arg
                    inner_mapping[v] = vars_mapping[arg]
                    rev_inner_mapping[vars_mapping[arg]] = v
                end
            end
        end
        inner_mapping[vars_mapping["out"]] = sc.branch_vars[sc.target_branch_id]
        rev_inner_mapping[sc.branch_vars[sc.target_branch_id]] = vars_mapping["out"]
        if verbose_test
            @info inner_mapping
        end

        matching_vars = Dict{Any,Any}()

        phase = 4

        skipped_copy_blocks = []
        skipped_blocks = []

        while (
            !isempty(sc.pq_forward) ||
            !isempty(sc.pq_reverse) ||
            !isempty(sc.copies_queue) ||
            !isempty(sc.duplicate_copies_queue) ||
            !isempty(sc.blocks_to_insert) ||
            !isempty(sc.rev_blocks_to_insert) ||
            !isempty(sc.waiting_entries)
        )
            receive_grammar_weights(sc, guiding_model_channels, grammar)

            phase = (phase + 1) % 5

            if phase == 2
                if isempty(sc.blocks_to_insert)
                    continue
                end
                (br_id, block_info), cost = peek(sc.blocks_to_insert)
                br_id, block_info = dequeue!(sc.blocks_to_insert)

                target_blocks_group = out_blocks

                var_id = sc.branch_vars[br_id]
                if !haskey(rev_inner_mapping, var_id) || !haskey(target_blocks_group, rev_inner_mapping[var_id])
                    if haskey(rev_inner_mapping, var_id) && haskey(rev_vars_mapping, rev_inner_mapping[var_id])
                        orig_var_id = rev_vars_mapping[rev_inner_mapping[var_id]]
                        if sc.verbose
                            @info "Skipping insert block $var_id $orig_var_id $br_id $block_info"
                        end
                    else
                        if sc.verbose
                            @info "Skipping insert block $var_id $br_id $block_info"
                        end
                    end
                    continue
                end

                target_blocks = target_blocks_group[rev_inner_mapping[var_id]]

                found_solutions = enumeration_iteration_insert_block_traced(
                    sc,
                    false,
                    br_id,
                    block_info,
                    guiding_model_channels,
                    grammar,
                    target_blocks,
                    inner_mapping,
                    rev_inner_mapping,
                )
                sc.iterations_count += 1
            elseif phase == 3
                if isempty(sc.rev_blocks_to_insert)
                    continue
                end
                (br_id, block_info), cost = peek(sc.rev_blocks_to_insert)
                br_id, block_info = dequeue!(sc.rev_blocks_to_insert)

                target_blocks_group = rev_blocks

                var_id = sc.branch_vars[br_id]
                if !haskey(rev_inner_mapping, var_id) || !haskey(target_blocks_group, rev_inner_mapping[var_id])
                    if haskey(rev_inner_mapping, var_id) && haskey(rev_vars_mapping, rev_inner_mapping[var_id])
                        orig_var_id = rev_vars_mapping[rev_inner_mapping[var_id]]
                        if sc.verbose
                            @info "Skipping rev insert block $var_id $orig_var_id $br_id $block_info"
                        end
                    else
                        if sc.verbose
                            @info "Skipping rev insert block $var_id $br_id $block_info"
                        end
                    end
                    continue
                end

                target_blocks = target_blocks_group[rev_inner_mapping[var_id]]

                found_solutions = enumeration_iteration_insert_block_traced(
                    sc,
                    true,
                    br_id,
                    block_info,
                    guiding_model_channels,
                    grammar,
                    target_blocks,
                    inner_mapping,
                    rev_inner_mapping,
                )
            elseif phase == 4
                if isempty(sc.copies_queue)
                    if isempty(sc.duplicate_copies_queue)
                        continue
                    end
                    block_info, cost = peek(sc.duplicate_copies_queue)
                    block_info = dequeue!(sc.duplicate_copies_queue)
                    is_duplicate = true
                else
                    block_info, cost = peek(sc.copies_queue)
                    block_info = dequeue!(sc.copies_queue)
                    is_duplicate = false
                end

                block, _ = block_info
                if is_block_loops(sc, block)
                    continue
                end

                filtered_target_blocks = filter(bl -> is_var_on_path(block, bl, inner_mapping, sc.verbose), copy_blocks)

                if isempty(filtered_target_blocks)
                    if sc.verbose
                        @info "Skipping copy block $block_info"
                    end
                    push!(skipped_copy_blocks, (block_info, cost, is_duplicate))
                    continue
                end

                found_solutions = enumeration_iteration_insert_copy_block_traced(
                    sc,
                    block_info,
                    guiding_model_channels,
                    grammar,
                    copy_blocks,
                    inner_mapping,
                    rev_inner_mapping,
                )
            else
                if phase == 0
                    pq = sc.pq_forward
                    is_forward = true
                else
                    pq = sc.pq_reverse
                    is_forward = false
                end
                if isempty(pq)
                    sleep(0.0001)
                    continue
                end
                entry_id = draw(pq)
                q = (is_forward ? sc.entry_queues_forward : sc.entry_queues_reverse)[entry_id]
                bp = dequeue!(q)
                target_blocks_group = is_forward ? out_blocks : rev_blocks

                if !haskey(matching_vars, (entry_id, is_forward))
                    entry = sc.entries[entry_id]
                    matching_vars[(entry_id, is_forward)] = []
                    for (var_id) in keys(target_blocks_group)
                        if might_unify(sc.types[entry.type_id], var_types[var_id])
                            push!(matching_vars[(entry_id, is_forward)], var_id)
                        end
                    end
                end

                if isempty(matching_vars[(entry_id, is_forward)])
                    if sc.verbose
                        @info "Skipping branch $entry_id $is_forward $bp"
                    end
                    push!(skipped_blocks, (entry_id, is_forward, bp))
                    update_entry_priority(sc, entry_id, !is_forward)
                    continue
                end
                target_blocks = vcat([target_blocks_group[v] for v in matching_vars[(entry_id, is_forward)]]...)

                enumeration_iteration_traced(sc, max_free_parameters, bp, entry_id, is_forward, target_blocks)
                found_solutions = []
            end

            for solution_path in found_solutions
                solution, cost, trace_values = extract_solution(sc, solution_path)
                # @info "Got solution $solution with cost $cost"
                ll = task.log_likelihood_checker(task, solution)
                if !isnothing(ll) && !isinf(ll)
                    dt = time() - start_time
                    res = HitResult(join(show_program(solution, false)), -cost, ll, dt, trace_values)
                    @info "Found solution"
                    @info "$solution"
                    export_solution_context(sc)
                    return res, -cost + ll
                end
            end
        end

        all_blocks = [sc.blocks[UInt64(i)] for i in 1:length(sc.blocks)]
        # @info all_blocks
        missing_blocks = []
        for (var_id, blocks) in rev_blocks
            if !haskey(inner_mapping, var_id)
                append!(missing_blocks, [(block, var_id) for block in blocks])
                continue
            end
            inner_var_id = inner_mapping[var_id]
            for block in blocks
                matching_blocks = filter(
                    b ->
                        isa(b, ReverseProgramBlock) &&
                            b.input_vars == [inner_var_id] &&
                            is_on_path(b.p, block.p, Dict()),
                    all_blocks,
                )
                if isempty(matching_blocks)
                    push!(missing_blocks, (block, var_id))
                end
            end
        end
        for (var_id, blocks) in out_blocks
            if !haskey(inner_mapping, var_id)
                append!(missing_blocks, [(block, var_id) for block in blocks])
                continue
            end
            inner_var_id = inner_mapping[var_id]
            for block in blocks
                matching_blocks = filter(
                    b -> isa(b, ProgramBlock) && b.output_var == inner_var_id && is_on_path(b.p, block.p, Dict()),
                    all_blocks,
                )

                # @info block
                # @info matching_blocks
                if isempty(matching_blocks)
                    push!(missing_blocks, (block, var_id))
                end
            end
        end
        for block in copy_blocks
            var_id = block.input_vars[1]
            if !haskey(inner_mapping, var_id)
                push!(missing_blocks, (block, var_id))
                continue
            end
            inner_var_id = inner_mapping[var_id]
            if !haskey(inner_mapping, block.output_var)
                push!(missing_blocks, (block, var_id))
                continue
            end
            dest_var_id = inner_mapping[block.output_var]
            matching_blocks = filter(
                b ->
                    isa(b, ProgramBlock) &&
                        isa(b.p, FreeVar) &&
                        b.input_vars == [inner_var_id] &&
                        b.output_var == dest_var_id,
                all_blocks,
            )
            if isempty(matching_blocks)
                push!(missing_blocks, (block, var_id))
            end
        end
        if !isempty(missing_blocks)
            export_solution_context(sc)
            @info "Missing blocks"
            @info missing_blocks
            @info [(bl, rev_vars_mapping[var_id]) for (bl, var_id) in missing_blocks]
            error("Could not find all blocks")
        end

        used_known_vars = Set{UInt64}()
        used_unknown_vars = Set{UInt64}()
        unused_known_vars = Dict{UInt64,Any}()
        unused_unknown_vars = DefaultDict{UInt64,Any}(() -> UInt64[])
        for branch_id in 1:sc.branches_count[]
            var_id = sc.branch_vars[branch_id]

            out_blocks = get_connected_from(sc.branch_outgoing_blocks, branch_id)
            if !isempty(out_blocks)
                push!(used_known_vars, var_id)
                if haskey(unused_known_vars, var_id)
                    delete!(unused_known_vars, var_id)
                end
            else
                if !in(var_id, used_known_vars) && branch_id != sc.target_branch_id
                    unused_known_vars[var_id] = branch_id
                end
            end

            in_blocks = get_connected_from(sc.branch_incoming_blocks, branch_id)
            if !isempty(in_blocks)
                push!(used_unknown_vars, var_id)
                if haskey(unused_unknown_vars, var_id)
                    delete!(unused_unknown_vars, var_id)
                end
            else
                if !in(var_id, used_unknown_vars) && !haskey(sc.input_keys, var_id)
                    push!(unused_unknown_vars[var_id], branch_id)
                end
            end
        end

        # @info rev_inner_mapping
        # @info inner_mapping
        for (var_id, branch_id) in unused_known_vars
            if haskey(rev_inner_mapping, var_id)
                orig_var_id = rev_vars_mapping[rev_inner_mapping[var_id]]
                @info "Unused explained var $orig_var_id"
            else
                @info "Unused explained var inner $var_id"
            end
            entry = sc.entries[sc.branch_entries[branch_id]]
            @info "Entry_id $(sc.branch_entries[branch_id])"
            @info sc.types[entry.type_id]
            @info entry.values
        end
        # @info unused_unknown_vars
        for (var_id, branch_ids) in unused_unknown_vars
            if haskey(rev_inner_mapping, var_id)
                orig_var_id = rev_vars_mapping[rev_inner_mapping[var_id]]
                @info "Unused unexplained var $orig_var_id $var_id"
            else
                @info "Unused unexplained var inner $var_id"
                continue
            end
            for branch_id in branch_ids
                entry = sc.entries[sc.branch_entries[branch_id]]
                @info "Entry_id $(sc.branch_entries[branch_id])"
                @info sc.types[entry.type_id]
                @info entry.values
            end
        end

        # if !isempty(unused_unknown_vars) || !isempty(unused_known_vars)
        #     export_solution_context(sc)
        #     error("Unused vars")
        # end

        # export_solution_context(sc)
        # error("Could not find solution")

        for (entry_id, is_forward, bp) in skipped_blocks
            if is_forward
                if haskey(sc.entry_queues_forward, entry_id)
                    q = sc.entry_queues_forward[entry_id]
                else
                    q = PriorityQueue{BlockPrototype,Float64}()
                end

                q[bp] = bp.cost
                update_entry_priority(sc, entry_id, false)
            else
                if haskey(sc.entry_queues_reverse, entry_id)
                    q = sc.entry_queues_reverse[entry_id]
                else
                    q = PriorityQueue{BlockPrototype,Float64}()
                end
                q[bp] = bp.cost
                update_entry_priority(sc, entry_id, true)
            end
        end

        @info "Skipped insert blocks"
        @info length(skipped_copy_blocks)
        @info length(skipped_blocks)

        for (block_info, cost, is_duplicate) in skipped_copy_blocks
            if is_duplicate
                sc.duplicate_copies_queue[block_info] = cost
            else
                sc.copies_queue[block_info] = cost
            end
        end

        enumeration_timeout = get_enumeration_timeout(timeout)

        phase = 4

        while (!(enumeration_timed_out(enumeration_timeout))) && (
            !isempty(sc.pq_forward) ||
            !isempty(sc.pq_reverse) ||
            !isempty(sc.copies_queue) ||
            !isempty(sc.blocks_to_insert) ||
            !isempty(sc.rev_blocks_to_insert) ||
            !isempty(sc.waiting_entries)
        )
            receive_grammar_weights(sc, guiding_model_channels, grammar)

            phase = (phase + 1) % 5

            if phase == 2
                if isempty(sc.blocks_to_insert)
                    continue
                end
                br_id, block_info = dequeue!(sc.blocks_to_insert)

                found_solutions =
                    enumeration_iteration_insert_block(sc, false, br_id, block_info, guiding_model_channels, grammar)
            elseif phase == 3
                if isempty(sc.rev_blocks_to_insert)
                    continue
                end
                br_id, block_info = dequeue!(sc.rev_blocks_to_insert)

                found_solutions =
                    enumeration_iteration_insert_block(sc, true, br_id, block_info, guiding_model_channels, grammar)
            elseif phase == 4
                if isempty(sc.copies_queue)
                    continue
                end
                block_info = dequeue!(sc.copies_queue)

                found_solutions =
                    enumeration_iteration_insert_copy_block(sc, block_info, guiding_model_channels, grammar)
            else
                if phase == 0
                    pq = sc.pq_forward
                    is_forward = true
                else
                    pq = sc.pq_reverse
                    is_forward = false
                end
                if isempty(pq)
                    sleep(0.0001)
                    continue
                end
                entry_id = draw(pq)
                q = (is_forward ? sc.entry_queues_forward : sc.entry_queues_reverse)[entry_id]
                bp = dequeue!(q)

                enumeration_iteration(sc, max_free_parameters, bp, entry_id, is_forward)
                found_solutions = []
            end

            sc.iterations_count += 1

            for solution_path in found_solutions
                solution, cost, trace_values = extract_solution(sc, solution_path)
                # @info "Got solution $solution with cost $cost"
                ll = task.log_likelihood_checker(task, solution)
                if !isnothing(ll) && !isinf(ll)
                    dt = time() - start_time
                    res = HitResult(join(show_program(solution, false)), -cost, ll, dt, trace_values)
                    @info "Found solution"
                    @info "$solution"
                    return res, -cost + ll
                end
            end
        end

        export_solution_context(sc)
        @info "Iterations count $(sc.iterations_count)"
        @info "Blocks found $(sc.blocks_found)"
        @info "Blocks inserted $(sc.blocks_inserted)"
        @info "Copy blocks inserted $(sc.copy_blocks_inserted)"
    catch e
        bt = catch_backtrace()
        export_solution_context(sc)
        @error "Error in build_partial_solution" exception = (e, bt)
        rethrow()
    finally
        mark_task_finished(guiding_model_channels, task_name)
    end

    @error "Could not find a trace for $(task.name) with target solution $target_solution"
    # error("Could not find a trace for $(task.name) with target solution $target_solution")
end
