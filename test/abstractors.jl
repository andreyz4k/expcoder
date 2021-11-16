
using Test

using solver: load_problems, enumerate_for_task, RedisContext
import Redis

@testset "Abstractors" begin
    @testset "Repeat" begin
        payload = Dict(
            "DSL" => Dict{String,Any}(
                "logVariable" => 0.0,
                "productions" => Any[
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "map"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "unfold"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "range"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "index"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "fold"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "length"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "if"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "+"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "-"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "empty"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "cons"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "car"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "cdr"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "empty?"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "0"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "1"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "*"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "mod"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "gt?"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "eq?"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "is-prime"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "is-square"),
                    Dict{String,Any}("logProbability" => 0.0, "expression" => "repeat"),
                ],
            ),
            "task" => Dict{String,Any}(
                "name" => "invert repeated",
                "maximumFrontier" => 10,
                "examples" => Any[
                    Dict{String,Any}("output" => Any[4, 4, 4, 4, 4], "inputs" => Any[Any[5, 5, 5, 5]]),
                    Dict{String,Any}("output" => Any[1, 1, 1, 1, 1, 1], "inputs" => Any[Any[6]]),
                    Dict{String,Any}("output" => Any[3, 3], "inputs" => Any[Any[2, 2, 2]]),
                ],
                "test_examples" => Any[],
                "request" => Dict{String,Any}(
                    "arguments" => Any[
                        Dict{String,Any}(
                            "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                            "constructor" => "list",
                        ),
                        Dict{String,Any}(
                            "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                            "constructor" => "list",
                        ),
                    ],
                    "constructor" => "->",
                ),
            ),
            "name" => "invert repeated",
            "programTimeout" => 1,
            "timeout" => 20,
            "verbose" => false,
            "shatter" => 10,
        )
        task, maximum_frontier, g, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated = @time enumerate_for_task(
            Dict(
                "redis" => RedisContext(Redis.RedisConnection()),
                "program_timeout" => program_timeout,
                "timeout" => timeout,
            ),
            g,
            task,
            maximum_frontier,
            verbose,
        )
        @test length(solutions) == 3
        @test number_enumerated == 39
    end
end
