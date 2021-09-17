module solver

function main()
    while true
        message = readline(stdin)

        if message == "stop"
            break
        end
        write(stdout, message * "\n")
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end

end
