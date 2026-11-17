
mutable struct PythonStandaloneGuidingModel <: AbstractGuidingModel
    redis_db::Int
    process::Any
    redis_conn::Any
    load_path::Any
end

function PythonStandaloneGuidingModel(load_path = nothing)
    return PythonStandaloneGuidingModel(myid(), nothing, nothing, load_path)
end

function set_current_grammar!(guiding_model::PythonStandaloneGuidingModel, grammar)
    full_grammar = vcat([string(g) for g in grammar], ["\$0", "lambda", "\$v1"])
    Redis.set(guiding_model.redis_conn, "set_current_grammar", JSON.json(full_grammar))
    while true
        if Redis.exists(guiding_model.redis_conn, "set_current_grammar")
            sleep(0.1)
        else
            break
        end
    end
end

function clear_model_cache(guiding_model::PythonStandaloneGuidingModel) end

function build_train_set(all_traces, guiding_model::PythonStandaloneGuidingModel)
    for (grammar, gr_traces) in values(all_traces)
        full_grammar = vcat([string(g) for g in grammar], ["\$0", "lambda", "\$v1"])
        grammar_key = "grammar_traces_$(randstring(6))"
        traces_count = 0

        for (task_name, traces) in gr_traces
            for (hit, cost) in traces
                inputs = [v[2] for (k, v) in hit.trace_values if isa(k, String) && k != "output"]
                outputs = hit.trace_values["output"][2]
                if any(isa(v, PatternWrapper) for v in outputs)
                    continue
                end

                blocks = extract_program_blocks(hit.hit_program)
                for (var_id, p, is_rev) in blocks
                    trace_val = hit.trace_values[var_id]
                    summary = build_likelihood_summary(grammar, trace_val[1], p, is_rev)
                    if isempty(summary[2])
                        continue
                    end
                    trace_val_unfolded = _unfold_trace_value(trace_val...)
                    trace_payload = JSON.json(
                        Dict(
                            "inputs" => inputs,
                            "output" => outputs,
                            "trace_val" => trace_val_unfolded,
                            "is_rev" => is_rev,
                            "summary" => summary,
                        ),
                    )
                    Redis.rpush(guiding_model.redis_conn, grammar_key, trace_payload)
                    traces_count += 1
                end
            end
        end

        group_payload = JSON.json(Dict("grammar" => full_grammar, "key" => grammar_key, "count" => traces_count))
        Redis.rpush(guiding_model.redis_conn, "train_set", group_payload)
    end
    return length(all_traces)
end

function update_guiding_model(guiding_model::PythonStandaloneGuidingModel, traces)
    groups_count = build_train_set(traces, guiding_model)
    if groups_count == 0
        return guiding_model
    end
    Redis.set(guiding_model.redis_conn, "update_model", groups_count)
    while true
        if Redis.exists(guiding_model.redis_conn, "update_model")
            sleep(0.1)
        else
            break
        end
    end
    return guiding_model
end

using JLD2

function save_guiding_model(m::PythonStandaloneGuidingModel, path)
    py_path = path * ".pt"
    Redis.set(m.redis_conn, "save_model", py_path)
    while true
        if Redis.exists(m.redis_conn, "save_model")
            sleep(0.1)
        else
            break
        end
    end
    model_state = Dict("py_model" => py_path)
    jldsave(path; type = "standalone", model_state)
end

function load_guiding_model(::Type{PythonStandaloneGuidingModel}, model_state)
    py_path = model_state["py_model"]
    m = PythonStandaloneGuidingModel(py_path)

    return m
end

struct PythonGuidingModelServer
    model::PythonStandaloneGuidingModel
end

import Redis

using CondaPkg

function start_server(server::PythonGuidingModelServer, is_test = false)
    @info "Starting Python model server"
    # Reset redis db
    server.model.redis_conn = get_redis_connection(server.model.redis_db)
    Redis.flushdb(server.model.redis_conn, "sync")
    lock(_python_task_states_lock) do
        empty!(_python_task_states)
    end
    cache_type = "sqlite"
    CondaPkg.withenv() do
        python = CondaPkg.which("python")
        cmd = `$python src/guiding_models/guiding_model_server.py $(server.model.redis_db) $(cache_type)`
        if is_test
            cmd = addenv(cmd, "WANDB_MODE" => "offline")
        end
        server.model.process = run(pipeline(cmd, stdout = stdout, stderr = stderr); wait = false)
    end
    if !isnothing(server.model.load_path)
        Redis.set(server.model.redis_conn, "load_model", server.model.load_path)
        while true
            if Redis.exists(server.model.redis_conn, "load_model")
                sleep(0.1)
            else
                break
            end
        end
    end
end

function stop_server(server::PythonGuidingModelServer, verbose = false)
    kill(server.model.process, Base.SIGINT)
    while (process_running(server.model.process))
        sleep(0.1)
    end
    Redis.disconnect(server.model.redis_conn)
    if verbose
        @info "Guiding model server stopped"
    end
end

function get_redis_connection(redis_db)
    return Redis.RedisConnection(; db = redis_db)
end

# Protocol with guiding_model_server.py:
#   task_io:<task>   - inputs and output of the task, sent once on the first request
#   active_tasks     - set of tasks currently being solved; the server polls them round-robin
#   requests:<task>  - per-task list of guiding requests, deleted as a whole when the task finishes
#   <task>           - per-task list of responses
#
# Each task keeps at most PYTHON_MODEL_MAX_IN_FLIGHT requests on the server. The rest wait
# locally, and the cheapest ones are sent first as responses come back.
const PYTHON_MODEL_MAX_IN_FLIGHT = Ref(64)

mutable struct PythonTaskState
    in_flight::Int
    queued::PriorityQueue{Tuple{UInt64,Bool},Float64}
    queued_requests::Dict{Tuple{UInt64,Bool},Any}
end

PythonTaskState() = PythonTaskState(0, PriorityQueue{Tuple{UInt64,Bool},Float64}(), Dict{Tuple{UInt64,Bool},Any}())

const _python_task_states = Dict{String,PythonTaskState}()
const _python_task_states_lock = ReentrantLock()

function _get_python_task_state!(redis_conn::Redis.RedisConnection, task_name, inputs, output)
    state, is_new = lock(_python_task_states_lock) do
        if haskey(_python_task_states, task_name)
            _python_task_states[task_name], false
        else
            _python_task_states[task_name] = PythonTaskState()
            _python_task_states[task_name], true
        end
    end
    if is_new
        # Lets the master clean up after this task if the worker process dies
        Redis.sadd(redis_conn, "worker_tasks:$(myid())", task_name)
        # task_io must be set before the task becomes visible in active_tasks
        Redis.set(redis_conn, "task_io:$task_name", JSON.json(Dict("inputs" => inputs, "output" => output)))
        Redis.sadd(redis_conn, "active_tasks", task_name)
    end
    return state
end

function _send_queued_requests(redis_conn::Redis.RedisConnection, task_name)
    payloads = lock(_python_task_states_lock) do
        state = get(_python_task_states, task_name, nothing)
        payloads = String[]
        if isnothing(state)
            return payloads
        end
        while state.in_flight < PYTHON_MODEL_MAX_IN_FLIGHT[] && !isempty(state.queued)
            key = dequeue!(state.queued)
            trace_val, is_known, entry_id = pop!(state.queued_requests, key)
            trace_val_batch = _unfold_trace_value(trace_val...)
            push!(
                payloads,
                JSON.json(Dict("trace_val" => trace_val_batch, "is_known" => is_known, "entry_id" => entry_id)),
            )
            state.in_flight += 1
        end
        payloads
    end
    if !isempty(payloads)
        Redis.rpush(redis_conn, "requests:$task_name", payloads...)
    end
end

function send_inputs_to_model(redis_conn::Redis.RedisConnection, model_inputs, priority = 0.0)
    (inputs, output, trace_val, is_known, entry_id, task_name, max_summary, options_count) = model_inputs
    state = _get_python_task_state!(redis_conn, task_name, inputs, output)
    lock(_python_task_states_lock) do
        key = (UInt64(entry_id), is_known)
        state.queued_requests[key] = (trace_val, is_known, entry_id)
        state.queued[key] = priority
    end
    _send_queued_requests(redis_conn, task_name)
end

function receive_grammar_weights(sc::SolutionContext, redis_conn::Redis.RedisConnection, grammar)
    received = 0
    while true
        response = Redis.lpop(redis_conn, sc.task_name)
        if isnothing(response)
            break
        end
        received += 1
        if sc.verbose
            @info "Got response from model $response"
        end
        response_dict = JSON.parse(response)

        times = response_dict["times"]
        entry_id = UInt64(response_dict["entry_id"])
        is_rev = response_dict["is_known"]
        result = response_dict["result"]

        # @info "Got response from model ($entry_id, $is_rev)"
        for (k, t) in times
            push!(sc.stats[k], t)
        end

        if haskey(sc.entry_grammars, (entry_id, is_rev))
            @info "Already have grammar for entry $entry_id, is_rev $is_rev"
            continue
        end
        process_grammar_results(sc, entry_id, is_rev, result, grammar)
    end
    if received > 0
        lock(_python_task_states_lock) do
            state = get(_python_task_states, sc.task_name, nothing)
            if !isnothing(state)
                state.in_flight = max(state.in_flight - received, 0)
            end
        end
        _send_queued_requests(redis_conn, sc.task_name)
    end
end

function _drop_task_on_server(redis_conn::Redis.RedisConnection, task_name)
    # Drop all pending requests at once, the server never reads them
    Redis.srem(redis_conn, "active_tasks", task_name)
    Redis.del(redis_conn, "requests:$task_name", "task_io:$task_name")
    # Lets the server purge requests it has already fetched into its internal queues
    Redis.rpush(redis_conn, "finished_tasks", task_name)
    Redis.expire(redis_conn, task_name, 5)
end

function mark_task_finished(redis_conn::Redis.RedisConnection, task_name)
    _drop_task_on_server(redis_conn, task_name)
    Redis.srem(redis_conn, "worker_tasks:$(myid())", task_name)
    lock(_python_task_states_lock) do
        delete!(_python_task_states, task_name)
    end
end

# Called on the master when a worker process dies without finishing its tasks.
# The retried task gets a new name, so the old one would otherwise stay registered.
function cleanup_worker_tasks(server::PythonGuidingModelServer, worker_id)
    # The master's main connection may be in use by another task, so use a separate one
    redis_conn = get_redis_connection(server.model.redis_db)
    try
        key = "worker_tasks:$worker_id"
        task_names = Redis.smembers(redis_conn, key)
        for task_name in task_names
            _drop_task_on_server(redis_conn, task_name)
        end
        Redis.del(redis_conn, key)
        if !isempty(task_names)
            @warn "Cleaned up guiding model requests of dead worker $worker_id: $(collect(task_names))"
        end
    finally
        Redis.disconnect(redis_conn)
    end
end

function send_wandb_log(server::PythonGuidingModelServer, log_dict)
    Redis.rpush(server.model.redis_conn, "wandb_logs", JSON.json(log_dict))
end

function send_wandb_config(server::PythonGuidingModelServer, config)
    Redis.rpush(server.model.redis_conn, "wandb_config", JSON.json(config))
end
