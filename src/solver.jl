module solver

include("logging.jl")
include("parser.jl")
include("type.jl")
include("program.jl")
include("grammar.jl")
include("task.jl")
include("load.jl")
include("data_structures/data_structures.jl")
include("pattern_matching.jl")
include("enumeration.jl")
include("export.jl")

import Redis
import Redis: execute_command


mutable struct RedisContext
    conn::Redis.RedisConnection
end

function get_conn(ctx::RedisContext)
    if Redis.is_connected(ctx.conn)
        ctx.conn
    else
        ctx.conn = Redis.RedisConnection()
        ctx.conn
    end
end

function disconnect_redis(ctx::RedisContext)
    if Redis.is_connected(ctx.conn)
        Redis.disconnect(ctx.conn)
    end
end

function set_timeout(redis, queue_name, end_time)
    while true
        try
            conn = get_conn(redis)
            Redis.watch(conn, queue_name)
            depth = Redis.hlen(conn, queue_name)
            Redis.multi(conn)
            Redis.hset(conn, queue_name, depth, "$end_time|0")
            res = Redis.execute_command(conn, ["exec"])
            # @info "Set timeout $res"
            if res == [1]
                return depth
            end
        catch
            disconnect_redis(redis)
            rethrow()
        end
    end
end

function remove_timeout(redis, queue_name, depth)
    while true
        try
            conn = get_conn(redis)
            Redis.watch(conn, queue_name)
            status = Redis.hget(conn, queue_name, depth)
            if status[end] == '0'
                Redis.multi(conn)
                Redis.hdel(conn, queue_name, depth)
                res = Redis.execute_command(conn, ["exec"])
                # @info "remove timeout $res"
                if res == [1]
                    return
                end
            else
                Redis.unwatch(conn)
                while true
                    sleep(1)
                end
            end
        catch
            disconnect_redis(redis)
            rethrow()
        end
    end
end

function clean_fired_timeout(redis, queue_name, depth)
    while true
        try
            conn = get_conn(redis)
            Redis.watch(conn, queue_name)
            status = Redis.hget(conn, queue_name, depth)
            if status[end] == '1'
                Redis.multi(conn)
                Redis.hdel(conn, queue_name, depth)
                res = Redis.execute_command(conn, ["exec"])
                # @info "clean fired timeout $res"
                if res == [1]
                    return
                end
            else
                Redis.unwatch(conn)
                error("Wrong timeout status on cleanup")
            end
        catch
            disconnect_redis(redis)
            rethrow()
        end
    end
end


macro run_with_timeout(timeout, expr)
    return quote
        reuse_redis = $(esc(:(@isdefined redis)))
        if !reuse_redis
            redis = RedisContext(Redis.RedisConnection())
        else
            redis = $(esc(:(redis)))
        end
        local end_time = time() + $(esc(timeout))
        local queue_name = "timeouts:$(myid())"
        local depth = set_timeout(redis, queue_name, end_time)

        local result = nothing
        local inner_exception = nothing
        try
            try
                result = $(esc(expr))
            catch e
                if isa(e, InterruptException)
                    rethrow()
                else
                    bt = catch_backtrace()
                    @error "Exception while running task" exception = (e, bt)
                    inner_exception = e
                end
            end
            remove_timeout(redis, queue_name, depth)
        catch e
            if isa(e, InterruptException)
                clean_fired_timeout(redis, queue_name, depth)
            else
                rethrow()
            end
        end
        if !reuse_redis
            disconnect_redis(redis)
        end
        if !isnothing(inner_exception)
            throw(inner_exception)
        end
        result
    end
end


function run_solving_process(message)
    @info "running processing"
    @info message
    task, maximum_frontier, g, _mfp, _nc, timeout, _verbose = load_problems(message)
    solutions, number_enumerated = enumerate_for_task(g, timeout, task, maximum_frontier)
    return export_frontiers(number_enumerated, task, solutions)
end

using Distributed

function get_new_task(redis)
    while true
        try
            conn = get_conn(redis)
            # watch(conn, "tasks")
            queue, message = Redis.blpop(conn, ["commands", "tasks"], 0)
            if queue == "commands" && message == "stop"
                # unwatch(conn)
                Redis.rpush(conn, "commands", message)
                return message
            end
            Redis.multi(conn)
            Redis.set(conn, "processing:$(myid())", message)
            res = Redis.execute_command(conn, ["exec"])
            if res == ["OK"]
                return message
            end
        catch e
            bt = catch_backtrace()
            @error "Error while fetching task" exception=(e,bt)
            disconnect_redis(redis)
            rethrow()
        end
    end
end

using JSON

function worker_loop()
    @info "Starting worker loop"
    redis = RedisContext(Redis.RedisConnection())
    while true
        try
            message = get_new_task(redis)
            if message == "stop"
                @info "Stopping worker"
                break
            end
            payload = JSON.parse(message)
            timeout = payload["timeout"]
            name = payload["name"]
            output = try
                result = @run_with_timeout timeout run_solving_process(payload)
                if isnothing(result)
                    result = Dict("number_enumerated" => 0, "solutions" => [])
                end
                Dict("status" => "success", "payload" => result, "name" => name)
            catch e
                buf = IOBuffer()
                showerror(buf, e)
                bt = catch_backtrace()
                @error "Error while running task" exception = (e, bt)
                Dict("status" => "error", "payload" => String(take!(buf)), "name" => name)
            end
            conn = get_conn(redis)
            Redis.multi(conn)
            Redis.rpush(conn, "results", JSON.json(output))
            Redis.del(conn, "processing:$(myid())")
            Redis.execute_command(conn, ["exec"])
        catch e
            disconnect_redis(redis)
            bt = catch_backtrace()
            @error "Error while processing a task" exception = (e, bt)
            rethrow()
        end
    end
    disconnect(conn)
end


end
