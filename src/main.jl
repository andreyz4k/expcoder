
using Redis
using Distributed
using JSON

@everywhere include("solver.jl")


function run_with_timeout(seconds, pid, name, semaphore, available_workers, workers_info_lock, payload)
    fut = @spawnat pid solver.run_solving_process(payload)
    timer_fut = @async isready(fut)
    Timer(seconds + 1) do _
        istaskdone(timer_fut) || interrupt(pid)
    end

    try
        result = fetch(fut)
        conn = RedisConnection()
        rpush(conn, "results", JSON.json(Dict("status" => "success", "payload" => result, "name" => name)))
    catch e
        if isa(e, RemoteException)
            conn = RedisConnection()
            if isa(e.captured.ex, InterruptException)
                rpush(
                    conn,
                    "results",
                    JSON.json(Dict("status" => "error", "payload" => "Task timeouted", "name" => name)),
                )
            else
                buf = IOBuffer()
                showerror(buf, e.captured)
                rpush(
                    conn,
                    "results",
                    JSON.json(Dict("status" => "error", "payload" => String(take!(buf)), "name" => name)),
                )
            end
        else
            rethrow()
        end
    finally
        lock(workers_info_lock) do
            available_workers[pid] = true
        end
        Base.release(semaphore)
    end
end


function main()
    conn = RedisConnection()
    semaphore = Base.Semaphore(length(workers()))
    available_workers = Dict(w => true for w in workers())
    workers_info_lock = Base.ReentrantLock()
    @info "Starting enumeration service"
    while true
        @info "waiting message"
        queue, message = blpop(conn, ["commands", "tasks"], 0)
        @info "got message" message

        if queue == "commands" && message == "stop"
            @info "Stopping enumeration service"
            break
        end

        Base.acquire(semaphore)
        payload = JSON.parse(message)
        timeout = payload["timeout"]
        name = payload["name"]
        pid = lock(workers_info_lock) do
            pid = first(w for (w, state) in available_workers if state == true)
            available_workers[pid] = false
            pid
        end
        @async run_with_timeout(timeout, pid, name, semaphore, available_workers, workers_info_lock, payload)
        @info "finished scheduling, going to next iteration"
    end
end


if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
