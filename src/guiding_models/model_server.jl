
mutable struct GuidingModelServer
    model::Any
    worker_register_channel::RemoteChannel
    worker_register_result_channel::RemoteChannel
    request_channel::RemoteChannel
    result_channels::Dict{String,RemoteChannel}
    end_tasks_channel::RemoteChannel
    stopped::Bool
    registration_loop::Any
    processing_loop::Any
end

function GuidingModelServer(model)
    worker_register_channel = RemoteChannel(() -> Channel{String}(20))
    worker_register_result_channel = RemoteChannel(() -> Channel{Any}(20))
    request_channel = RemoteChannel(() -> Channel{Any}(1000))
    result_channels = Dict{String,RemoteChannel}()
    end_tasks_channel = RemoteChannel(() -> Channel{Any}(100))
    return GuidingModelServer(
        model,
        worker_register_channel,
        worker_register_result_channel,
        request_channel,
        result_channels,
        end_tasks_channel,
        false,
        nothing,
        nothing,
    )
end

function _registration_loop(server::GuidingModelServer)
    try
        while !server.stopped
            task_name = take!(server.worker_register_channel)
            if !haskey(server.result_channels, task_name)
                result_channel = RemoteChannel(() -> Channel{Any}(1000))
                server.result_channels[task_name] = result_channel
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

gpu_mem_threshold = 3 * 10^8

function _guiding_processing_loop(server::GuidingModelServer)
    try
        while !server.stopped
            while isready(server.end_tasks_channel)
                task_name = take!(server.end_tasks_channel)
                task_channel = server.result_channels[task_name]
                close(task_channel)
                delete!(server.result_channels, task_name)
            end
            request = take!(server.request_channel)
            input, output, trace_val, is_rev, entry_id, task_name, max_summary, options_count = request
            if !haskey(server.result_channels, task_name)
                continue
            end
            entry_ids = [entry_id]
            batch = ([input], [output], Tuple{Tp,Vector{Any}}[trace_val], [is_rev], [task_name])
            value_max_length = get_encoded_value_length(server.model, max_summary)
            batch_size = options_count

            mem_footprint = max(value_max_length)^2 * batch_size

            while isready(server.request_channel)
                # @info "Fetching another request"
                while isready(server.end_tasks_channel)
                    task_name = take!(server.end_tasks_channel)
                    task_channel = server.result_channels[task_name]
                    close(task_channel)
                    delete!(server.result_channels, task_name)
                end

                request = fetch(server.request_channel)
                input, output, trace_val, is_rev, entry_id, task_name, max_summary, options_count = request

                if !haskey(server.result_channels, task_name)
                    take!(server.request_channel)
                    continue
                end

                val_max_length = get_encoded_value_length(server.model, max_summary)

                mem_footprint = max(value_max_length, val_max_length)^2 * (batch_size + options_count)
                if mem_footprint > gpu_mem_threshold
                    break
                end

                value_max_length = max(value_max_length, val_max_length)
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

            times, guiding_result = try
                run_guiding_model(server.model, model_inputs)
            catch e
                @error "Got error in guiding model" exception = e
                @error "Memory footprint: $mem_footprint"
                @error "Model inputs: $(model_inputs)"
                rethrow()
            end
            # @info "Result size: $(size(guiding_result))"
            for (i, task_name) in enumerate(batch[5])
                if !haskey(server.result_channels, task_name)
                    continue
                end
                result_channel = server.result_channels[task_name]
                worker_result = guiding_result[:, i]
                put!(result_channel, (task_name, entry_ids[i], batch[4][i], times, worker_result))
            end
            # @info "Batch done"
        end
    catch e
        if !server.stopped
            bt = catch_backtrace()
            @error "Got error in guiding processing loop" exception = (e, bt)
            rethrow()
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
    put!(guiding_model_channels[1], model_inputs)
end

contextual_grammar_cache = Dict()

function _grammar_with_weights(grammar::Grammar, production_scores, log_variable, log_lambda, log_free_var)
    productions = Tuple{Program,Tp,Float64}[(p, t, production_scores[p]) for (p, t, _) in grammar.library]
    return Grammar(log_variable, log_lambda, log_free_var, productions)
end

function grammar_receiver_loop(sc::SolutionContext, receiver_channel, grammar)
    try
        grammar_len = length(grammar)
        while true
            response = take!(receiver_channel)
            if sc.verbose
                @info "Got response from model $response"
            end
            if response[1] != sc.task_name
                @warn "Wrong task name, expecting $(sc.task_name), got $(response[1])"
                continue
            end
            if response[2] == "stop"
                if sc.verbose
                    @info "Stopping grammar receiver loop for task $(sc.task_name)"
                end
                break
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
                    _grammar_with_weights(
                        prototype.no_context,
                        production_scores,
                        log_variable,
                        log_lambda,
                        log_free_var,
                    ),
                    _grammar_with_weights(
                        prototype.no_context,
                        production_scores,
                        log_variable,
                        log_lambda,
                        log_free_var,
                    ),
                    Dict(
                        p => [
                            _grammar_with_weights(g, production_scores, log_variable, log_lambda, log_free_var)
                            for g in grammars
                        ] for (p, grammars) in prototype.contextual_library
                    ),
                )
            end

            lock(sc.queues_lock) do
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
    catch e
        bt = catch_backtrace()
        @error "Got error in grammar receiver loop" exception = (e, bt)
        rethrow()
    end
end

function generate_grammar(sc::SolutionContext, guiding_model_channels, grammar, entry_id, is_known, branch_id)
    should_stop = lock(sc.queues_lock) do
        if !haskey(sc.waiting_branches, (entry_id, is_known))
            sc.waiting_branches[(entry_id, is_known)] = [branch_id]
            false
        else
            push!(sc.waiting_branches[(entry_id, is_known)], branch_id)
            true
        end
    end
    if should_stop
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
