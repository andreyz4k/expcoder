
using Test

using solver: load_problems, enumerate_for_task

@testset "Loading task" begin
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
            ],
        ),
        "task" => Dict{String,Any}(
            "name" => "add-k with k=1",
            "maximumFrontier" => 10,
            "examples" => Any[
                Dict{String,Any}("output" => Any[4, 5, 5, 14, 7], "inputs" => Any[Any[3, 4, 4, 13, 6]]),
                Dict{String,Any}("output" => Any[], "inputs" => Any[Any[]]),
                Dict{String,Any}("output" => Any[1, 3, 13, 3, 12, 1], "inputs" => Any[Any[0, 2, 12, 2, 11, 0]]),
                Dict{String,Any}("output" => Any[5, 13, 16], "inputs" => Any[Any[4, 12, 15]]),
                Dict{String,Any}("output" => Any[16, 3, 17, 3, 6, 16, 7], "inputs" => Any[Any[15, 2, 16, 2, 5, 15, 6]]),
                Dict{String,Any}("output" => Any[9, 14, 7], "inputs" => Any[Any[8, 13, 6]]),
                Dict{String,Any}("output" => Any[1, 12, 8, 10, 4], "inputs" => Any[Any[0, 11, 7, 9, 3]]),
                Dict{String,Any}("output" => Any[10, 11, 5], "inputs" => Any[Any[9, 10, 4]]),
                Dict{String,Any}("output" => Any[10, 2, 14, 11, 14], "inputs" => Any[Any[9, 1, 13, 10, 13]]),
                Dict{String,Any}("output" => Any[10, 7], "inputs" => Any[Any[9, 6]]),
                Dict{String,Any}("output" => Any[], "inputs" => Any[Any[]]),
                Dict{String,Any}("output" => Any[8, 10, 9, 2, 13, 4], "inputs" => Any[Any[7, 9, 8, 1, 12, 3]]),
                Dict{String,Any}("output" => Any[5, 15, 2], "inputs" => Any[Any[4, 14, 1]]),
                Dict{String,Any}("output" => Any[7, 3, 14], "inputs" => Any[Any[6, 2, 13]]),
                Dict{String,Any}("output" => Any[15], "inputs" => Any[Any[14]]),
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
        "name" => "add-k with k=1",
        "programTimeout" => 2,
        "timeout" => 10,
        "verbose" => false,
        "shatter" => 10,
    )

    payload = Dict{String,Any}(
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
            ],
        ),
        "task" => Dict{String,Any}(
            "name" => "empty",
            "maximumFrontier" => 10,
            "examples" => Any[
                Dict{String,Any}("output" => false, "inputs" => Any[Any[1, 2, 3]]),
                Dict{String,Any}("output" => true, "inputs" => Any[Any[]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[0]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[1, 1, 2, 1]]),
                Dict{String,Any}("output" => true, "inputs" => Any[Any[]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[7, 7, 3, 2]]),
                Dict{String,Any}("output" => true, "inputs" => Any[Any[]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[10, 10, 6, 13, 4]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[4, 7, 16, 11, 10, 3, 15]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[4]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[6, 0, 14, 0, 2, 12]]),
                Dict{String,Any}("output" => true, "inputs" => Any[Any[]]),
                Dict{String,Any}("output" => true, "inputs" => Any[Any[]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[12, 15]]),
                Dict{String,Any}("output" => false, "inputs" => Any[Any[2, 16, 2, 5, 15, 6, 7]]),
            ],
            "test_examples" => Any[],
            "request" => Dict{String,Any}(
                "arguments" => Any[
                    Dict{String,Any}(
                        "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                        "constructor" => "list",
                    ),
                    Dict{String,Any}("arguments" => Any[], "constructor" => "bool"),
                ],
                "constructor" => "->",
            ),
        ),
        "name" => "empty",
        "programTimeout" => 10,
        "timeout" => 7,
        "verbose" => false,
        "shatter" => 10,
    )
    @testset "full loading" begin
        task, maximum_frontier, g, _mfp, _nc, timeout, _verbose = load_problems(payload)
    end

    @testset "try_enumerate" begin
        task, maximum_frontier, g, _mfp, _nc, timeout, verbose = load_problems(payload)
        solutions, number_enumerated = enumerate_for_task(g, timeout, task, maximum_frontier, verbose)
    end
end
