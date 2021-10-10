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


function run_solving_process(message)
    @info "running processing"
    @info message
    try
        task, maximum_frontier, g, _mfp, _nc, timeout, _verbose = load_problems(message)
        solutions, number_enumerated = enumerate_for_task(g, timeout, task, maximum_frontier)
        return export_frontiers(number_enumerated, task, solutions)
    catch e
        if isa(e, InterruptException)
            return Dict("number_enumerated" => 0, "solutions" => [])
        else
            rethrow()
        end
    end
end


end
