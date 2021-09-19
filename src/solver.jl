module solver

using Redis

function main()
    conn = RedisConnection()
    while true
        @info "waiting message"
        queue, message = blpop(conn, ["tasks", "commands"], 0)
        @info "got message" message

        if queue == "commands" && message == "stop"
            break
        end
        rpush(conn, "results", message)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end

end
