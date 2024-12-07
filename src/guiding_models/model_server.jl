
mutable struct GuidingModelServer
    model::Any
    worker_register_channel::RemoteChannel
    worker_register_result_channel::RemoteChannel
    request_channel::RemoteChannel
    result_channels::Dict{String,RemoteChannel}
    result_channels_lock::ReentrantLock
    end_tasks_channel::RemoteChannel
    stopped::Bool
    registration_loop::Any
    processing_loop::Any
end

function GuidingModelServer(model)
    worker_register_channel = RemoteChannel(() -> Channel{String}(20))
    worker_register_result_channel = RemoteChannel(() -> Channel{Any}(20))
    request_channel = RemoteChannel(() -> Channel{Any}(10000))
    result_channels = Dict{String,RemoteChannel}()
    end_tasks_channel = RemoteChannel(() -> Channel{Any}(100))
    return GuidingModelServer(
        model,
        worker_register_channel,
        worker_register_result_channel,
        request_channel,
        result_channels,
        ReentrantLock(),
        end_tasks_channel,
        false,
        nothing,
        nothing,
    )
end

function GuidingModelServer(model::PythonStandaloneGuidingModel)
    return PythonGuidingModelServer(model)
end

function _registration_loop(server::GuidingModelServer)
    try
        while !server.stopped
            task_name = take!(server.worker_register_channel)

            if !haskey(server.result_channels, task_name)
                result_channel = RemoteChannel(() -> Channel{Any}(1000))
                lock(server.result_channels_lock) do
                    server.result_channels[task_name] = result_channel
                end
            else
                @warn "Requesting a channel for an already registered task: $task_name"
            end
            put!(
                server.worker_register_result_channel,
                (task_name, server.request_channel, server.result_channels[task_name], server.end_tasks_channel),
            )
        end
    catch e
        if !server.stopped
            bt = catch_backtrace()
            @error "Got error in registration loop" exception = (e, bt)
            rethrow()
        end
    end
end

gpu_mem_threshold = 7 * 10^8

function _check_ended_tasks(server::GuidingModelServer)
    while isready(server.end_tasks_channel)
        task_name = take!(server.end_tasks_channel)
        lock(server.result_channels_lock) do
            delete!(server.result_channels, task_name)
        end
    end
end

function n_avail_c(rr::RemoteChannel, args...)
    rid = remoteref_id(rr)
    return if rr.where == myid()
        Base.n_avail(Distributed.lookup_ref(rid).c, args...)
    else
        remotecall_fetch(rid -> Base.n_avail(Distributed.lookup_ref(rid).c, args...), rr.where, rid)
    end
end

model_stats = DefaultDict(() -> [])

function _guiding_processing_loop(server::GuidingModelServer)
    wasted_time = 0.0
    total_skipped_early = 0
    total_skipped_late = 0
    total_success = 0
    try
        while !server.stopped
            _check_ended_tasks(server)
            request = take!(server.request_channel)
            start = time()
            input, output, trace_val, is_rev, entry_id, task_name, max_summary, options_count = request
            if !haskey(server.result_channels, task_name)
                wasted_time += time() - start
                total_skipped_early += 1
                continue
            end
            entry_ids = [entry_id]
            batch = ([input], [output], Tuple{Tp,Vector{Any}}[trace_val], [is_rev], [task_name])
            value_max_length = get_encoded_value_length(server.model, max_summary)
            batch_size = options_count

            mem_footprint = max(value_max_length)^2 * batch_size

            while isready(server.request_channel) && batch_size * value_max_length < 30000
                # @info "Fetching another request"
                _check_ended_tasks(server)
                w_start = time()

                request = fetch(server.request_channel)
                input, output, trace_val, is_rev, entry_id, task_name, max_summary, options_count = request

                if !haskey(server.result_channels, task_name)
                    take!(server.request_channel)
                    wasted_time += time() - w_start
                    total_skipped_early += 1
                    continue
                end

                new_val_max_length = max(value_max_length, get_encoded_value_length(server.model, max_summary))

                new_mem_footprint = new_val_max_length^2 * (batch_size + options_count)
                if new_mem_footprint > gpu_mem_threshold || (batch_size + options_count) * new_val_max_length > 30000
                    break
                end

                mem_footprint = new_mem_footprint
                value_max_length = new_val_max_length
                batch_size += options_count

                take!(server.request_channel)
                push!(entry_ids, entry_id)
                push!(batch[1], input)
                push!(batch[2], output)
                push!(batch[3], trace_val)
                push!(batch[4], is_rev)
                push!(batch[5], task_name)
            end

            model_inputs = (batch[1:3]..., reshape(batch[4], 1, :), batch[5])
            # @info model_inputs
            fetch_time = time() - start
            start = time()
            @info "Tasks count: $(length(batch[5]))"
            @info "Batch size: $batch_size"
            @info "Value max length: $value_max_length"
            @info "Batch table size $(batch_size * value_max_length)"
            @info "Memory footprint: $mem_footprint"
            @info "Remaining queue size: $(n_avail_c(server.request_channel))"
            times, guiding_result = try
                run_guiding_model(server.model, model_inputs)
            catch e
                @error "Got error in guiding model" exception = e
                @error "Memory footprint: $mem_footprint"
                @error "Model inputs: $(model_inputs)"
                rethrow()
            end
            # @info "Guiding model $(time() - start)"
            push!(model_stats["full_run"], time() - start)
            push!(model_stats["batch_size"], batch_size)
            push!(model_stats["value_max_length"], value_max_length)
            push!(model_stats["mem_footprint"], mem_footprint)
            push!(model_stats["fetch_time"], fetch_time)
            for (k, v) in times
                push!(model_stats[k], v)
            end
            start = time()

            _check_ended_tasks(server)
            # @info "Result size: $(size(guiding_result))"
            skipped = 0
            for (i, task_name) in enumerate(batch[5])
                if !haskey(server.result_channels, task_name)
                    skipped += 1
                    total_skipped_late += 1
                    continue
                end
                total_success += 1
                result_channel = server.result_channels[task_name]
                worker_result = guiding_result[:, i]
                channel_queue_size = n_avail_c(result_channel)
                if channel_queue_size > 900
                    @warn "Result channel almost full $channel_queue_size"
                end
                put!(result_channel, (task_name, entry_ids[i], batch[4][i], times, worker_result))
            end
            # @info "Skipped $skipped/$(length(batch[5]))"
            push!(model_stats["send_time"], time() - start)
            push!(model_stats["skipped"], skipped)
            push!(model_stats["out_batch_size"], length(batch[5]))
            # @info "Batch done"
        end
    catch e
        if !server.stopped
            bt = catch_backtrace()
            @error "Got error in guiding processing loop" exception = (e, bt)
            close(server.worker_register_channel)
            close(server.worker_register_result_channel)
            close(server.request_channel)
            close(server.end_tasks_channel)
            for (task_name, result_channel) in server.result_channels
                close(result_channel)
            end
            rethrow()
        end
    finally
        @info "Wasted time on fetching finished tasks: $wasted_time"
        @info "Total skipped early: $total_skipped_early"
        @info "Total skipped late: $total_skipped_late"
        @info "Total success: $total_success"
        @info "Success rate: $(total_success / (total_success + total_skipped_late))"
        for (k, v) in model_stats
            @info "Model stats $k: $(mean(v)) ± $(std(v)) total $(sum(v)) max $(maximum(v))"
        end
    end
end

function start_server(server::GuidingModelServer)
    server.registration_loop = Threads.@spawn _registration_loop(server)
    server.processing_loop = Threads.@spawn _guiding_processing_loop(server)
end

function stop_server(server::GuidingModelServer, verbose = false)
    server.stopped = true
    close(server.worker_register_channel)
    close(server.worker_register_result_channel)
    close(server.request_channel)
    close(server.end_tasks_channel)
    for (task_name, result_channel) in server.result_channels
        close(result_channel)
    end
    wait(server.registration_loop)
    wait(server.processing_loop)
    if verbose
        @info "Guiding model server stopped"
    end
end

function send_inputs_to_model(guiding_model_channels, model_inputs)
    channel_queue_size = n_avail_c(guiding_model_channels[1])
    if channel_queue_size > 9900
        @warn "Request channel almost full $channel_queue_size"
    end
    put!(guiding_model_channels[1], model_inputs)
end

contextual_grammar_cache = Dict()

function _grammar_with_weights(grammar::Grammar, production_scores, log_variable, log_lambda, log_free_var)
    productions = Tuple{Program,Tp,Float64}[(p, t, production_scores[p]) for (p, t, _) in grammar.library]
    return Grammar(log_variable, log_lambda, log_free_var, productions)
end

function receive_grammar_weights(sc::SolutionContext, guiding_model_channels, grammar)
    receiver_channel = guiding_model_channels[2]
    grammar_len = length(grammar)
    while isready(receiver_channel)
        response = take!(receiver_channel)
        if sc.verbose
            @info "Got response from model $response"
        end
        if response[1] != sc.task_name
            @warn "Wrong task name, expecting $(sc.task_name), got $(response[1])"
            continue
        end

        task_name, entry_id, is_rev, times, result = response

        # @info "Got response from model ($entry_id, $is_rev)"
        for (k, t) in times
            push!(sc.stats[k], t)
        end

        if haskey(sc.entry_grammars, (entry_id, is_rev))
            @info "Already have grammar for entry $entry_id, is_rev $is_rev"
            continue
        end

        log_variable = result[end-2]
        log_lambda = result[end-1]
        log_free_var = result[end]

        sc.entry_grammars[(entry_id, is_rev)] = if !haskey(contextual_grammar_cache, grammar_len)
            productions = Tuple{Program,Tp,Float64}[(p, p.t, result[i]) for (i, p) in enumerate(grammar)]
            g = Grammar(log_variable, log_lambda, log_free_var, productions)
            contextual_grammar_cache[grammar_len] = make_dummy_contextual(g)
            contextual_grammar_cache[grammar_len]
        else
            prototype = contextual_grammar_cache[grammar_len]
            production_scores = Dict{Program,Float64}(p => result[i] for (i, p) in enumerate(grammar))
            ContextualGrammar(
                _grammar_with_weights(prototype.no_context, production_scores, log_variable, log_lambda, log_free_var),
                _grammar_with_weights(prototype.no_context, production_scores, log_variable, log_lambda, log_free_var),
                Dict(
                    p => [
                        _grammar_with_weights(g, production_scores, log_variable, log_lambda, log_free_var) for
                        g in grammars
                    ] for (p, grammars) in prototype.contextual_library
                ),
            )
        end

        for (branch_id) in sc.waiting_branches[(entry_id, is_rev)]
            var_id = sc.branch_vars[branch_id]
            entry = sc.entries[entry_id]
            type_id = first(get_connected_from(sc.branch_types, branch_id))
            type = sc.types[type_id]
            context, type = instantiate(type, empty_context)

            bp = BlockPrototype(
                Hole(
                    type,
                    is_rev ? sc.known_var_locations[var_id] : sc.unknown_var_locations[var_id],
                    CombinedArgChecker([SimpleArgChecker(is_rev, -1, true)]),
                    is_rev ? nothing : entry.values,
                ),
                context,
                [],
                EPSILON,
                0,
                type,
                nothing,
                (var_id, branch_id),
                is_rev,
            )
            queue_group = is_rev ? sc.branch_queues_explained : sc.branch_queues_unknown
            if haskey(queue_group, branch_id)
                q = queue_group[branch_id]
            else
                q = PriorityQueue{BlockPrototype,Float64}()
            end
            if is_rev
                enqueue_known_bp(sc, bp, q, branch_id)
            else
                enqueue_unknown_bp(sc, bp, q)
            end
            if !isempty(q)
                queue_group[branch_id] = q
                update_branch_priority(sc, branch_id, is_rev)
            end
        end
        delete!(sc.waiting_branches, (entry_id, is_rev))
    end
end

function mark_task_finished(guiding_model_channels, task_name)
    put!(guiding_model_channels[3], task_name)
end

function generate_grammar(sc::SolutionContext, guiding_model_channels, grammar, entry_id, is_known, branch_id)
    if !haskey(sc.waiting_branches, (entry_id, is_known))
        sc.waiting_branches[(entry_id, is_known)] = [branch_id]
    else
        push!(sc.waiting_branches[(entry_id, is_known)], branch_id)
        return
    end

    inputs = []
    for (var_id, name) in sc.input_keys
        # Using var id as branch id because they are the same for input variables
        entry = sc.entries[sc.branch_entries[var_id]]
        push!(inputs, entry.values)
    end
    output_entry = sc.entries[sc.branch_entries[sc.target_branch_id]]
    output = output_entry.values

    val_entry = sc.entries[entry_id]
    trace_val = (sc.types[val_entry.type_id], val_entry.values)

    model_inputs =
        (inputs, output, trace_val, is_known, entry_id, sc.task_name, val_entry.max_summary, val_entry.options_count)

    send_inputs_to_model(guiding_model_channels, model_inputs)
    if sc.verbose
        @info "Sent inputs to model for ($entry_id, $is_known)"
        @info "Sent inputs to model for branch $branch_id $model_inputs"
    end
end

function load_guiding_model(path)
    model_info = JLD2.load(path)
    if model_info["type"] == "nn"
        load_guiding_model(NNGuidingModel, model_info["model_state"])
    elseif model_info["type"] == "dummy"
        load_guiding_model(DummyGuidingModel, model_info["model_state"])
    elseif model_info["type"] == "python"
        load_guiding_model(PythonGuidingModel, model_info["model_state"])
    elseif model_info["type"] == "standalone"
        load_guiding_model(PythonStandaloneGuidingModel, model_info["model_state"])
    else
        error("Unknown model type: $(model_info["type"])")
    end
end
