
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

function send_inputs_to_model(redis_conn::Redis.RedisConnection, model_inputs)
    (inputs, output, trace_val, is_known, entry_id, task_name, max_summary, options_count) = model_inputs
    trace_val_batch = _unfold_trace_value(trace_val...)
    payload = JSON.json(
        Dict(
            "inputs" => inputs,
            "output" => output,
            "trace_val" => trace_val_batch,
            "is_known" => is_known,
            "entry_id" => entry_id,
            "task_name" => task_name,
        ),
    )
    Redis.rpush(redis_conn, "requests", payload)
end

function receive_grammar_weights(sc::SolutionContext, redis_conn::Redis.RedisConnection, grammar)
    while true
        response = Redis.lpop(redis_conn, sc.task_name)
        if isnothing(response)
            break
        end
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
end

function mark_task_finished(redis_conn::Redis.RedisConnection, task_name)
    Redis.rpush(redis_conn, "finished_tasks", task_name)
    Redis.expire(redis_conn, task_name, 5)
end

function send_wandb_log(server::PythonGuidingModelServer, log_dict)
    Redis.rpush(server.model.redis_conn, "wandb_logs", JSON.json(log_dict))
end

function send_wandb_config(server::PythonGuidingModelServer, config)
    Redis.rpush(server.model.redis_conn, "wandb_config", JSON.json(config))
end
