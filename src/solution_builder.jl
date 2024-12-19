
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

function build_partial_solution(task::Task, task_name, target_solution, guiding_model_channels, grammar, timeout = 20)
    verbose_test = false
    max_free_parameters = 10
    run_context = Dict{String,Any}("program_timeout" => 1, "timeout" => 40)

    type_weights = Dict(
        "int" => 1.0,
        "list" => 1.0,
        "color" => 1.0,
        "bool" => 1.0,
        "float" => 1.0,
        "grid" => 1.0,
        "tuple2" => 1.0,
        "tuple3" => 1.0,
        "coord" => 1.0,
        "set" => 1.0,
        "any" => 1.0,
    )

    hyperparameters = Dict("path_cost_power" => 1.0, "complexity_power" => 1.0, "block_cost_power" => 1.0)

    # @info target_solution
    target_program = parse_program(target_solution)

    in_blocks, out_blocks, vars_mapping = _extract_blocks(task, target_program, verbose_test)
    rev_vars_mapping = Dict(v => k for (k, v) in vars_mapping)

    start_time = time()

    # verbose_test = true
    sc = create_starting_context(task, task_name, type_weights, hyperparameters, verbose_test)

    try
        enqueue_updates(sc, guiding_model_channels, grammar)

        if verbose_test
            @info in_blocks
            @info out_blocks
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

        from_input = true

        skipped_blocks = []

        while (!isempty(sc.pq_input) || !isempty(sc.pq_output) || !isempty(sc.waiting_branches))
            receive_grammar_weights(sc, guiding_model_channels, grammar)
            from_input = !from_input
            pq = from_input ? sc.pq_input : sc.pq_output
            if isempty(pq)
                sleep(0.0001)
                continue
            end
            (br_id, is_explained) = draw(pq)
            q = (is_explained ? sc.branch_queues_explained : sc.branch_queues_unknown)[br_id]
            bp = dequeue!(q)

            target_blocks_group = from_input ? in_blocks : out_blocks
            var_id = sc.branch_vars[br_id]
            if !haskey(rev_inner_mapping, var_id) || !haskey(target_blocks_group, rev_inner_mapping[var_id])
                if haskey(rev_inner_mapping, var_id) && haskey(rev_vars_mapping, rev_inner_mapping[var_id])
                    orig_var_id = rev_vars_mapping[rev_inner_mapping[var_id]]
                    # @info "Skipping branch $var_id $orig_var_id $br_id $is_explained $from_input"
                    push!(skipped_blocks, (br_id, is_explained, from_input, bp))
                else
                    # @info "Skipping branch $var_id $br_id $is_explained"
                end
                # @info bp
                update_branch_priority(sc, br_id, is_explained)
                continue
            end
            target_blocks = target_blocks_group[rev_inner_mapping[var_id]]

            found_solutions = enumeration_iteration_traced(
                run_context,
                sc,
                max_free_parameters,
                guiding_model_channels,
                grammar,
                bp,
                br_id,
                is_explained,
                target_blocks,
                inner_mapping,
                rev_inner_mapping,
            )

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

        all_blocks = [sc.blocks[UInt64(i)] for i in 1:length(sc.blocks)]
        # @info all_blocks
        missing_blocks = []
        for (var_id, blocks) in in_blocks
            if !haskey(inner_mapping, var_id)
                append!(missing_blocks, [(block, var_id) for block in blocks])
                continue
            end
            inner_var_id = inner_mapping[var_id]
            for block in blocks
                if isa(block, ReverseProgramBlock)
                    matching_blocks = filter(
                        b ->
                            isa(b, ReverseProgramBlock) &&
                                b.input_vars == [inner_var_id] &&
                                is_on_path(b.p, block.p, Dict(), true),
                        all_blocks,
                    )
                    if isempty(matching_blocks)
                        push!(missing_blocks, (block, var_id))
                    end
                else
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
                    b ->
                        isa(b, ProgramBlock) && b.output_var == inner_var_id && is_on_path(b.p, block.p, Dict(), true),
                    all_blocks,
                )

                # @info block
                # @info matching_blocks
                if isempty(matching_blocks)
                    push!(missing_blocks, (block, var_id))
                end
            end
        end
        if !isempty(missing_blocks)
            @info "Missing blocks"
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
            @info sc.types[entry.type_id]
            @info entry.values
        end
        # @info unused_unknown_vars
        for (var_id, branch_ids) in unused_unknown_vars
            if haskey(rev_inner_mapping, var_id)
                orig_var_id = rev_vars_mapping[rev_inner_mapping[var_id]]
                @info "Unused unexplained var $orig_var_id"
            else
                continue
                @info "Unused unexplained var inner $var_id"
            end
            for branch_id in branch_ids
                entry = sc.entries[sc.branch_entries[branch_id]]
                @info sc.types[entry.type_id]
                @info entry.values
            end
        end

        for (branch_id, is_explained, from_input, bp) in skipped_blocks
            if !is_explained
                if haskey(sc.branch_queues_unknown, branch_id)
                    q = sc.branch_queues_unknown[branch_id]
                else
                    q = PriorityQueue{BlockPrototype,Float64}()
                end

                enqueue_unknown_bp(sc, bp, q)
                if !isempty(q)
                    sc.branch_queues_unknown[branch_id] = q
                    update_branch_priority(sc, branch_id, false)
                end
            else
                if haskey(sc.branch_queues_explained, branch_id)
                    q = sc.branch_queues_explained[branch_id]
                else
                    q = PriorityQueue{BlockPrototype,Float64}()
                end
                enqueue_known_bp(sc, bp, q, branch_id)
                if !isempty(q)
                    sc.branch_queues_explained[branch_id] = q
                    update_branch_priority(sc, branch_id, true)
                end
            end
        end

        enumeration_timeout = get_enumeration_timeout(timeout)

        while (!(enumeration_timed_out(enumeration_timeout))) &&
            (!isempty(sc.pq_input) || !isempty(sc.pq_output) || !isempty(sc.waiting_branches))
            receive_grammar_weights(sc, guiding_model_channels, grammar)
            from_input = !from_input
            pq = from_input ? sc.pq_input : sc.pq_output
            if isempty(pq)
                sleep(0.0001)
                continue
            end
            (br_id, is_explained) = draw(pq)
            q = (is_explained ? sc.branch_queues_explained : sc.branch_queues_unknown)[br_id]
            bp = dequeue!(q)

            found_solutions = enumeration_iteration(
                run_context,
                sc,
                max_free_parameters,
                guiding_model_channels,
                grammar,
                bp,
                br_id,
                is_explained,
            )

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

        @info "Iterations count $(sc.iterations_count)"
        @info "Total number of valid blocks $(sc.total_number_of_enumerated_programs)"
    catch e
        bt = catch_backtrace()
        @error "Error in build_manual_trace" exception = (e, bt)
        rethrow()
    finally
        mark_task_finished(guiding_model_channels, task_name)
    end

    @error "Could not find a trace for $(task.name) with target solution $target_solution"
    # error("Could not find a trace for $(task.name) with target solution $target_solution")
end
