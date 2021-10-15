
using Distributed

@everywhere include("solver.jl")

import Redis
import Redis: execute_command

function start_timeout_monitor(pid)
    Timer(1, interval = 1) do t
        if !in(pid, workers())
            close(t)
            return
        end
        conn = Redis.RedisConnection()
        queue_name = "timeouts:$pid"
        Redis.watch(conn, queue_name)
        timeouts = Redis.hgetall(conn, queue_name)
        timeouts = sort(timeouts, rev = true)
        for (depth, timeout_data) in timeouts
            threshold_str, status = split(timeout_data, "|")
            threshold_time = parse(Float64, threshold_str)
            if status == "1"
                if threshold_time + 10 < time()
                    new_threshold = "$(time())|1"
                    Redis.multi(conn)
                    Redis.hset(conn, queue_name, depth, new_threshold)
                    res = Redis.execute_command(conn, ["exec"])
                    if res == [0]
                        @warn "Interrupting worker again $pid"
                        interrupt(pid)
                    end
                end
                break
            elseif threshold_time < time()
                max_depth, last_threshold = maximum(timeouts)
                threshold_str, _ = split(last_threshold, "|")
                new_data = threshold_str * "|1"
                Redis.multi(conn)
                Redis.hset(conn, queue_name, max_depth, new_data)
                res = Redis.execute_command(conn, ["exec"])
                if res == [0]
                    @warn "Interrupting worker $pid"
                    interrupt(pid)
                end
                break
            end
        end

        Redis.disconnect(conn)
    end
end


function setup_worker(pid, source_path)
    @async begin
        @fetchfrom pid begin
            task_local_storage()[:SOURCE_PATH] = source_path
            include("solver.jl")
        end
        @fetchfrom pid solver.init_logger()
        @spawnat pid solver.worker_loop()
    end
end


function add_new_workers(count, source_path)
    @warn "Adding $count new workers"
    new_pids = addprocs(count)
    setup_futures = [setup_worker(pid, source_path) for pid in new_pids]
    for f in setup_futures
        fetch(f)
    end
    for pid in new_pids
        start_timeout_monitor(pid)
    end
    @info "Finished adding new workers"
    new_pids
end

function should_stop(conn)
    has_new_commands = Redis.llen(conn, "commands")
    if has_new_commands > 0
        _, message = Redis.blpop(conn, ["commands"], 0)

        if message == "stop"
            Redis.rpush(conn, "commands", message)
            @info "Stopping enumeration service"
            return true
        end
    end
    false
end

function main()
    @info "Starting enumeration service"
    @everywhere solver.init_logger()

    source_path = get(task_local_storage(), :SOURCE_PATH, nothing)

    for pid in workers()
        @spawnat pid solver.worker_loop()
        start_timeout_monitor(pid)
    end

    active_workers = workers()
    num_workers = length(active_workers)

    conn = Redis.RedisConnection()
    while true
        if should_stop(conn)
            break
        end

        if workers() == active_workers
            sleep(1)
            continue
        end

        for pid in active_workers
            if !in(pid, workers())
                @warn "Worker $pid is dead"
                processing_key = "processing:$pid"
                payload = Redis.get(conn, processing_key)
                if !isnothing(payload)
                    @warn "Rescheduling task from worker $pid"
                    Redis.multi(conn)
                    Redis.rpush(conn, "tasks", payload)
                    Redis.del(conn, processing_key)
                    Redis.execute_command(conn, ["exec"])
                end
            end
        end
        active_workers = workers()
        if should_stop(conn)
            break
        end
        new_pids = add_new_workers(num_workers - length(workers()), source_path)
        append!(active_workers, new_pids)
        sleep(1)

    end
    Redis.disconnect(conn)
end


if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
