
using Test

using JSON
using solver: load_problems, enumerate_for_task

@testset "Arc tasks" begin
    sample_payload = Dict{String,Any}(
        "DSL" => Dict{String,Any}(
            "logVariable" => 0.18440093100070953,
            "productions" => Any[
                Dict{String,Any}(
                    "logProbability" => 0.26229602098464966,
                    "expression" => "map",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1) -> list(t0) -> list(t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.17433375120162964,
                    "expression" => "map_set",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1) -> set(t0) -> set(t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.020587414503097534,
                    "expression" => "map_grid",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1) -> grid(t0) -> grid(t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.25952717661857605,
                    "expression" => "map2",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1 -> t2) -> list(t0) -> list(t1) -> list(t2)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.7479397058486938,
                    "expression" => "map2_grid",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1 -> t2) -> grid(t0) -> grid(t1) -> grid(t2)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.09426483511924744,
                    "expression" => "unfold",
                    "is_reversible" => false,
                    "type" => "(t0 -> bool) -> (t0 -> t1) -> (t0 -> t0) -> t0 -> list(t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.31616055965423584,
                    "expression" => "range",
                    "is_reversible" => true,
                    "type" => "int -> list(int)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.24963818490505219,
                    "expression" => "index",
                    "is_reversible" => false,
                    "type" => "int -> list(t0) -> t0",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.6580096483230591,
                    "expression" => "index2",
                    "is_reversible" => false,
                    "type" => "int -> int -> grid(t0) -> t0",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.24903573095798492,
                    "expression" => "fold",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1 -> t1) -> list(t0) -> t1 -> t1",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.043374061584472656,
                    "expression" => "fold_set",
                    "is_reversible" => true,
                    "type" => "(t0 -> set(t1) -> set(t1)) -> set(t0) -> set(t1) -> set(t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.05344507470726967,
                    "expression" => "fold_h",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1 -> t1) -> grid(t0) -> list(t1) -> list(t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.01714884489774704,
                    "expression" => "fold_v",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1 -> t1) -> grid(t0) -> list(t1) -> list(t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.024114713072776794,
                    "expression" => "length",
                    "is_reversible" => false,
                    "type" => "list(t0) -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.33626657724380493,
                    "expression" => "height",
                    "is_reversible" => false,
                    "type" => "grid(t0) -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.36573341488838196,
                    "expression" => "width",
                    "is_reversible" => false,
                    "type" => "grid(t0) -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.01316140592098236,
                    "expression" => "if",
                    "is_reversible" => false,
                    "type" => "bool -> t0 -> t0 -> t0",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.0700928121805191,
                    "expression" => "+",
                    "is_reversible" => true,
                    "type" => "int -> int -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.18608686327934265,
                    "expression" => "-",
                    "is_reversible" => false,
                    "type" => "int -> int -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.05018486827611923,
                    "expression" => "empty",
                    "is_reversible" => false,
                    "type" => "list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.05018486827611923,
                    "expression" => "empty_set",
                    "is_reversible" => false,
                    "type" => "set(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.26301681995391846,
                    "expression" => "cons",
                    "is_reversible" => true,
                    "type" => "t0 -> list(t0) -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.26301681995391846,
                    "expression" => "adjoin",
                    "is_reversible" => true,
                    "type" => "t0 -> set(t0) -> set(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.11566320061683655,
                    "expression" => "car",
                    "is_reversible" => false,
                    "type" => "list(t0) -> t0",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.4045564830303192,
                    "expression" => "cdr",
                    "is_reversible" => false,
                    "type" => "list(t0) -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.04355373978614807,
                    "expression" => "empty?",
                    "is_reversible" => false,
                    "type" => "list(t0) -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.21377874910831451,
                    "expression" => "*",
                    "is_reversible" => true,
                    "type" => "int -> int -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.4629265069961548,
                    "expression" => "mod",
                    "is_reversible" => false,
                    "type" => "int -> int -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.28995591402053833,
                    "expression" => "gt?",
                    "is_reversible" => false,
                    "type" => "int -> int -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.20868434011936188,
                    "expression" => "eq?",
                    "is_reversible" => false,
                    "type" => "t0 -> t0 -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.3835919499397278,
                    "expression" => "is-prime",
                    "is_reversible" => false,
                    "type" => "int -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.26428088545799255,
                    "expression" => "is-square",
                    "is_reversible" => false,
                    "type" => "int -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.27473536133766174,
                    "expression" => "repeat",
                    "is_reversible" => true,
                    "type" => "t0 -> int -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.20100094377994537,
                    "expression" => "repeat_grid",
                    "is_reversible" => true,
                    "type" => "t0 -> int -> int -> grid(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.1020718663930893,
                    "expression" => "concat",
                    "is_reversible" => true,
                    "type" => "list(t0) -> list(t0) -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.3644667863845825,
                    "expression" => "rows",
                    "is_reversible" => true,
                    "type" => "grid(t0) -> list(list(t0))",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.08203943073749542,
                    "expression" => "columns",
                    "is_reversible" => true,
                    "type" => "grid(t0) -> list(list(t0))",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.34513404965400696,
                    "expression" => "rows_to_grid",
                    "is_reversible" => true,
                    "type" => "list(list(t0)) -> grid(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.302104651927948,
                    "expression" => "columns_to_grid",
                    "is_reversible" => true,
                    "type" => "list(list(t0)) -> grid(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.0025863386690616608,
                    "expression" => "rev_select",
                    "is_reversible" => true,
                    "type" => "(t0 -> bool) -> list(t0) -> list(t0) -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.0025863386690616608,
                    "expression" => "rev_select_set",
                    "is_reversible" => true,
                    "type" => "(t0 -> bool) -> set(t0) -> set(t0) -> set(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.3118687868118286,
                    "expression" => "rev_select_grid",
                    "is_reversible" => true,
                    "type" => "(t0 -> bool) -> grid(t0) -> grid(t0) -> grid(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.3658756911754608,
                    "expression" => "rev_list_elements",
                    "is_reversible" => true,
                    "type" => "set(tuple2(int, t0)) -> int -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.16821910440921783,
                    "expression" => "rev_grid_elements",
                    "is_reversible" => true,
                    "type" => "set(tuple2(tuple2(int, int), t0)) -> int -> int -> grid(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.19650761783123016,
                    "expression" => "zip2",
                    "is_reversible" => true,
                    "type" => "list(t0) -> list(t1) -> list(tuple2(t0, t1))",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.04930289089679718,
                    "expression" => "zip_grid2",
                    "is_reversible" => true,
                    "type" => "list(t0) -> list(t1) -> list(tuple2(t0, t1))",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.04608079418540001,
                    "expression" => "tuple2",
                    "is_reversible" => true,
                    "type" => "t0 -> t1 -> tuple2(t0, t1)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.04608079418540001,
                    "expression" => "tuple2_first",
                    "is_reversible" => false,
                    "type" => "tuple2(t0, t1) -> t0",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.7565436363220215,
                    "expression" => "tuple2_second",
                    "is_reversible" => false,
                    "type" => "tuple2(t0, t1) -> t1",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.24813920259475708,
                    "expression" => "reverse",
                    "is_reversible" => true,
                    "type" => "list(t0) -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.39079853892326355,
                    "expression" => "rev_fold",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1 -> t1) -> t1 -> t1 -> list(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => -0.3027239739894867,
                    "expression" => "rev_fold_set",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1 -> t1) -> t1 -> t1 -> set(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.05734211206436157,
                    "expression" => "list_to_set",
                    "is_reversible" => false,
                    "type" => "list(t0) -> set(t0)",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "rev_groupby",
                    "is_reversible" => true,
                    "type" => "(t0 -> t1) -> t0 -> set(tuple2(t1, set(t0))) -> set(tuple2(t1, set(t0)))",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "rev_greedy_cluster",
                    "is_reversible" => true,
                    "type" => "(t0 -> set(t0) -> bool) -> t0 -> set(set(t0)) -> set(set(t0))",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "not",
                    "is_reversible" => true,
                    "type" => "bool -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "and",
                    "is_reversible" => true,
                    "type" => "bool -> bool -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "or",
                    "is_reversible" => true,
                    "type" => "bool -> bool -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "all",
                    "is_reversible" => false,
                    "type" => "(t0 -> bool) -> list(t0) -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "any",
                    "is_reversible" => false,
                    "type" => "(t0 -> bool) -> list(t0) -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "all_set",
                    "is_reversible" => false,
                    "type" => "(t0 -> bool) -> set(t0) -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "any_set",
                    "is_reversible" => false,
                    "type" => "(t0 -> bool) -> set(t0) -> bool",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0,
                    "expression" => "abs",
                    "is_reversible" => true,
                    "type" => "int -> int",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.15116432309150696,
                    "expression" => "0",
                    "is_reversible" => false,
                    "type" => "int",
                ),
                Dict{String,Any}(
                    "logProbability" => 0.0043089985847473145,
                    "expression" => "1",
                    "is_reversible" => false,
                    "type" => "int",
                ),
            ],
        ),
        "type_weights" => Dict{String,Any}(
            "int" => 1.0,
            "list" => 1.0,
            "color" => 1.0,
            "bool" => 1.0,
            "float" => 1.0,
            "grid" => 1.0,
            "tuple2" => 1.0,
            "tuple3" => 1.0,
            "coord" => 1.0,
            "set" => 1.0,
        ),
        "programTimeout" => 3.0,
        "timeout" => 40,
        "verbose" => false,
        "shatter" => 10,
    )

    function create_task(task_dict)
        result = copy(sample_payload)
        result["task"] = task_dict
        result["name"] = task_dict["name"]
        return result
    end

    function create_arc_task(filename)
        arc_task = JSON.parsefile("../../dreamcoder/domains/arc/ARC/data/training/" * filename)
        task_dict = Dict{String,Any}(
            "name" => filename,
            "maximumFrontier" => 10,
            "extras" => 5,
            "request" => Dict{String,Any}(
                "arguments" => Dict{String,Any}(
                    "inp0" => Dict{String,Any}(
                        "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "color")],
                        "constructor" => "grid",
                    ),
                ),
                "output" => Dict{String,Any}(
                    "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "color")],
                    "constructor" => "grid",
                ),
                "constructor" => "->",
            ),
            "specialTask" => "arc",
        )
        task_dict["examples"] = Any[
            Dict{String,Any}("inputs" => Dict{String,Any}("inp0" => example["input"]), "output" => example["output"]) for example in arc_task["train"]
        ]
        task_dict["test_examples"] = Any[
            Dict{String,Any}("inputs" => Dict{String,Any}("inp0" => example["input"]), "output" => example["output"]) for example in arc_task["test"]
        ]
        return create_task(task_dict)
    end

    @testset "a85d4709.json" begin
        payload = create_arc_task("a85d4709.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 1000
    end

    @testset "5c2c9af4.json" begin
        payload = create_arc_task("5c2c9af4.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 1500
    end

    @testset "23581191.json" begin
        payload = create_arc_task("23581191.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 3000
    end

    @testset "4258a5f9.json" begin
        payload = create_arc_task("4258a5f9.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 1000
    end

    @testset "f25ffba3.json" begin
        payload = create_arc_task("f25ffba3.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 1
        @test number_enumerated < 10000
    end

    @testset "74dd1130.json" begin
        payload = create_arc_task("74dd1130.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) >= 5
        @test number_enumerated < 1000
    end

    @testset "7837ac64.json" begin
        payload = create_arc_task("7837ac64.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 3000
    end

    @testset "6fa7a44f.json" begin
        payload = create_arc_task("6fa7a44f.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) > 0
        @test number_enumerated < 10000
    end

    @testset "c9e6f938.json" begin
        payload = create_arc_task("c9e6f938.json")
        @info payload["name"]
        for prod in payload["DSL"]["productions"]
            prod["logProbability"] = 0.0
        end
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) > 0
        @test number_enumerated < 10000
    end

    @testset "bbc9ae5d.json" begin
        payload = create_arc_task("bbc9ae5d.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 1000
    end

    @testset "63613498.json" begin
        payload = create_arc_task("63613498.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        # verbose = true
        # timeout = 600
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 3000
    end

    @testset "d8c310e9.json" begin
        payload = create_arc_task("d8c310e9.json")
        @info payload["name"]
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        # verbose = true
        # timeout = 600
        solutions, number_enumerated =
            @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
        @test length(solutions) == 0
        @test number_enumerated >= 3000
    end

    # @testset "8731374e.json" begin
    #     payload = create_arc_task("8731374e.json")
    #     @info payload["name"]
    #     task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
    #     solutions, number_enumerated =
    #         @time enumerate_for_task(g, type_weights, task, maximum_frontier, timeout, verbose)
    #     @test length(solutions) == 0
    #     @test number_enumerated >= 1
    #     @test number_enumerated < 10000
    # end
end
