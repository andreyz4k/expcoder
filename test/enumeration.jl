
using solver:
    solve_task,
    get_guiding_model,
    get_starting_grammar,
    Task,
    parse_type,
    supervised_task_checker,
    Program,
    Tp,
    Grammar,
    make_dummy_contextual,
    set_current_grammar!,
    GuidingModelServer,
    start_server,
    stop_server,
    parse_program

@testset "Enumeration" begin
    type_weights = Dict{String,Any}(
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
        "any" => 1.0,
    )

    timeout = 30
    program_timeout = 3.0
    maximum_solutions = 10
    verbose = false
    hyperparameters = Dict{String,Any}("path_cost_power" => 1.0, "complexity_power" => 1.0, "block_cost_power" => 1.0)
    guiding_model = get_guiding_model("dummy")
    grammar_strs = [
        "map",
        "unfold",
        "range",
        "index",
        "fold",
        "length",
        "if",
        "+",
        "-",
        "empty",
        "cons",
        "car",
        "cdr",
        "empty?",
        "0",
        "1",
        "*",
        "mod",
        "gt?",
        "eq?",
        "is-prime",
        "is-square",
        "repeat",
        "concat",
        "rev_fix_param",
    ]
    grammar = [parse_program(s) for s in grammar_strs]
    set_current_grammar!(guiding_model, grammar)

    guiding_model.log_lambda = -10.0
    guiding_model.log_free_var = 3.0
    guiding_model.preset_weights["rev_fix_param"] = 4.0

    function create_task(name, type_str, examples)
        train_inputs = []
        train_outputs = []
        for example in examples
            push!(train_inputs, example["inputs"])
            push!(train_outputs, example["output"])
        end
        task = Task(name, parse_type(type_str), supervised_task_checker, train_inputs, train_outputs, [], [])
        return task
    end

    function test_solve_task(task)
        guiding_model_server = GuidingModelServer(guiding_model)
        start_server(guiding_model_server)

        try
            register_channel = guiding_model_server.worker_register_channel
            register_response_channel = guiding_model_server.worker_register_result_channel
            put!(register_channel, task.name)
            task_name, request_channel, result_channel, end_tasks_channel = take!(register_response_channel)
            return @time solve_task(
                task,
                task_name,
                (request_channel, result_channel, end_tasks_channel),
                grammar,
                nothing,
                nothing,
                timeout,
                program_timeout,
                type_weights,
                hyperparameters,
                maximum_solutions,
                verbose,
            )
        finally
            stop_server(guiding_model_server)
        end
    end

    @testcase_log "try_enumerate add-k with k=1" begin
        task = create_task(
            "add-k with k=1",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[4, 5, 5, 14, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 4, 4, 13, 6]),
                ),
                Dict{String,Any}("output" => Any[], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}(
                    "output" => Any[1, 3, 13, 3, 12, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 2, 12, 2, 11, 0]),
                ),
                Dict{String,Any}("output" => Any[5, 13, 16], "inputs" => Dict{String,Any}("inp0" => Any[4, 12, 15])),
                Dict{String,Any}(
                    "output" => Any[16, 3, 17, 3, 6, 16, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 2, 16, 2, 5, 15, 6]),
                ),
                Dict{String,Any}("output" => Any[9, 14, 7], "inputs" => Dict{String,Any}("inp0" => Any[8, 13, 6])),
                Dict{String,Any}(
                    "output" => Any[1, 12, 8, 10, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 11, 7, 9, 3]),
                ),
                Dict{String,Any}("output" => Any[10, 11, 5], "inputs" => Dict{String,Any}("inp0" => Any[9, 10, 4])),
                Dict{String,Any}(
                    "output" => Any[10, 2, 14, 11, 14],
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 1, 13, 10, 13]),
                ),
                Dict{String,Any}("output" => Any[10, 7], "inputs" => Dict{String,Any}("inp0" => Any[9, 6])),
                Dict{String,Any}("output" => Any[], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}(
                    "output" => Any[8, 10, 9, 2, 13, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 9, 8, 1, 12, 3]),
                ),
                Dict{String,Any}("output" => Any[5, 15, 2], "inputs" => Dict{String,Any}("inp0" => Any[4, 14, 1])),
                Dict{String,Any}("output" => Any[7, 3, 14], "inputs" => Dict{String,Any}("inp0" => Any[6, 2, 13])),
                Dict{String,Any}("output" => Any[15], "inputs" => Dict{String,Any}("inp0" => Any[14])),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) >= 0
    end

    @testcase_log "try_enumerate empty" begin
        task = create_task(
            "empty",
            "inp0:list(int) -> bool",
            [
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 3])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[0])),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[1, 1, 2, 1])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[7, 7, 3, 2])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[10, 10, 6, 13, 4])),
                Dict{String,Any}(
                    "output" => false,
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 7, 16, 11, 10, 3, 15]),
                ),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[4])),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[6, 0, 14, 0, 2, 12])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[12, 15])),
                Dict{String,Any}("output" => false, "inputs" => Dict{String,Any}("inp0" => Any[2, 16, 2, 5, 15, 6, 7])),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) >= 1
    end

    # powers_options = [1.0, 2.0, 3.0, 4.0, 5.0]
    # complexity_options = [1.0]

    # @testcase "try_enumerate append-index-k with k=5 $cost_power $complexity_power $block_cost_power $any_complexity" for cost_power in
    #                                                                                                                       powers_options,
    #     complexity_power in powers_options,
    #     block_cost_power in powers_options,
    #     list_complexity in complexity_options,
    #     set_complexity in complexity_options,
    #     tuple2_complexity in complexity_options,
    #     any_complexity in [0.0, 0.1, 0.5, 1.0, 2.0, 3.0]

    #     hyperparameters = Dict{String,Any}(
    #         "path_cost_power" => cost_power,
    #         "complexity_power" => complexity_power,
    #         "block_cost_power" => block_cost_power,
    #     )
    #     type_weights = Dict{String,Any}(
    #         "int" => 1.0,
    #         "list" => list_complexity,
    #         "color" => 1.0,
    #         "bool" => 1.0,
    #         "float" => 1.0,
    #         "grid" => 1.0,
    #         "tuple2" => tuple2_complexity,
    #         "tuple3" => 1.0,
    #         "coord" => 1.0,
    #         "set" => set_complexity,
    #         "any" => any_complexity,
    #     )
    @testcase_log "try_enumerate append-index-k with k=5" begin
        task = create_task(
            "append-index-k with k=5",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[11, 9, 15, 7, 2, 3, 11, 7, 1, 2, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[11, 9, 15, 7, 2, 3, 11, 7, 1, 2]),
                ),
                Dict{String,Any}(
                    "output" => Any[11, 9, 16, 5, 5, 16, 11, 9, 5],
                    "inputs" => Dict{String,Any}("inp0" => Any[11, 9, 16, 5, 5, 16, 11, 9]),
                ),
                Dict{String,Any}(
                    "output" => Any[12, 12, 3, 2, 14, 15, 10, 11, 4, 11, 15, 2, 14],
                    "inputs" => Dict{String,Any}("inp0" => Any[12, 12, 3, 2, 14, 15, 10, 11, 4, 11, 15, 2]),
                ),
                Dict{String,Any}(
                    "output" => Any[4, 6, 1, 7, 1, 13, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 6, 1, 7, 1, 13]),
                ),
                Dict{String,Any}(
                    "output" => Any[8, 16, 5, 13, 14, 12, 6, 0, 14],
                    "inputs" => Dict{String,Any}("inp0" => Any[8, 16, 5, 13, 14, 12, 6, 0]),
                ),
                Dict{String,Any}(
                    "output" => Any[9, 11, 8, 0, 7, 8, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 11, 8, 0, 7, 8]),
                ),
                Dict{String,Any}(
                    "output" => Any[12, 4, 7, 10, 13, 3, 14, 4, 12, 4, 13],
                    "inputs" => Dict{String,Any}("inp0" => Any[12, 4, 7, 10, 13, 3, 14, 4, 12, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 12, 0, 0, 15, 9, 9, 9, 2, 15],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 12, 0, 0, 15, 9, 9, 9, 2]),
                ),
                Dict{String,Any}(
                    "output" => Any[12, 5, 6, 5, 15, 2, 10, 7, 7, 2, 13, 10, 15],
                    "inputs" => Dict{String,Any}("inp0" => Any[12, 5, 6, 5, 15, 2, 10, 7, 7, 2, 13, 10]),
                ),
                Dict{String,Any}(
                    "output" => Any[13, 0, 16, 8, 9, 10, 16, 7, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 0, 16, 8, 9, 10, 16, 7]),
                ),
                Dict{String,Any}(
                    "output" => Any[16, 15, 7, 8, 2, 5, 14, 15, 8, 8, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[16, 15, 7, 8, 2, 5, 14, 15, 8, 8]),
                ),
                Dict{String,Any}(
                    "output" => Any[7, 7, 5, 15, 2, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 7, 5, 15, 2]),
                ),
                Dict{String,Any}(
                    "output" => Any[13, 2, 13, 16, 1, 3, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 2, 13, 16, 1, 3]),
                ),
                Dict{String,Any}(
                    "output" => Any[6, 4, 15, 14, 7, 12, 3, 0, 4, 16, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 4, 15, 14, 7, 12, 3, 0, 4, 16]),
                ),
                Dict{String,Any}(
                    "output" => Any[15, 15, 9, 4, 2, 2, 14, 13, 5, 4, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 15, 9, 4, 2, 2, 14, 13, 5, 4]),
                ),
            ],
        )
        solutions = test_solve_task(task)
        @test length(solutions) >= 2
        # end
    end

    @testcase_log "try_enumerate len" begin
        task = create_task(
            "len",
            "inp0:list(int) -> int",
            [
                Dict{String,Any}("output" => 3, "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 3])),
                Dict{String,Any}("output" => 1, "inputs" => Dict{String,Any}("inp0" => Any[0])),
                Dict{String,Any}("output" => 4, "inputs" => Dict{String,Any}("inp0" => Any[1, 1, 2, 1])),
                Dict{String,Any}("output" => 2, "inputs" => Dict{String,Any}("inp0" => Any[2, 9])),
                Dict{String,Any}("output" => 1, "inputs" => Dict{String,Any}("inp0" => Any[0])),
                Dict{String,Any}("output" => 7, "inputs" => Dict{String,Any}("inp0" => Any[10, 14, 8, 2, 12, 10, 3])),
                Dict{String,Any}("output" => 0, "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => 2, "inputs" => Dict{String,Any}("inp0" => Any[2, 7])),
                Dict{String,Any}("output" => 5, "inputs" => Dict{String,Any}("inp0" => Any[13, 11, 10, 12, 13])),
                Dict{String,Any}("output" => 1, "inputs" => Dict{String,Any}("inp0" => Any[15])),
                Dict{String,Any}("output" => 5, "inputs" => Dict{String,Any}("inp0" => Any[5, 6, 2, 8, 9])),
                Dict{String,Any}("output" => 0, "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => 1, "inputs" => Dict{String,Any}("inp0" => Any[3])),
                Dict{String,Any}("output" => 3, "inputs" => Dict{String,Any}("inp0" => Any[7, 14, 11])),
                Dict{String,Any}("output" => 6, "inputs" => Dict{String,Any}("inp0" => Any[15, 15, 0, 1, 3, 16])),
            ],
        )
        solutions = test_solve_task(task)
        @test length(solutions) >= 1
    end

    @testcase_log "try_enumerate is-mod-k with k=1" begin
        task = create_task(
            "is-mod-k with k=1",
            "inp0:list(int) -> bool",
            [
                Dict{String,Any}(
                    "output" => true,
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 7, 16, 11, 10, 3, 15]),
                ),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[4])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[6, 0, 14, 0, 2, 12])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[0, 6, 4, 12, 15])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[2, 16, 2, 5, 15, 6, 7])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[6, 11, 0, 11, 7, 9])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[9, 10, 4])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[1, 13, 10, 13])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[6, 1, 13, 7])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[1, 12, 3])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[14, 1])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[2, 13, 3])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[14, 13, 12, 6])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[6, 14, 7])),
                Dict{String,Any}("output" => true, "inputs" => Dict{String,Any}("inp0" => Any[13, 14, 7, 1, 0, 11, 0])),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) >= 5
    end

    @testcase_log "prepend-k with k=0" begin
        task = create_task(
            "prepend-k with k=0",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[0, 12, 0, 1, 9, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[12, 0, 1, 9, 4]),
                ),
                Dict{String,Any}("output" => Any[0, 9, 10, 8], "inputs" => Dict{String,Any}("inp0" => Any[9, 10, 8])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}(
                    "output" => Any[0, 5, 11, 9, 0, 7, 1, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 11, 9, 0, 7, 1, 7]),
                ),
                Dict{String,Any}("output" => Any[0, 14, 0, 3], "inputs" => Dict{String,Any}("inp0" => Any[14, 0, 3])),
                Dict{String,Any}(
                    "output" => Any[0, 6, 9, 8, 16, 1, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 9, 8, 16, 1, 2]),
                ),
                Dict{String,Any}("output" => Any[0, 16, 11], "inputs" => Dict{String,Any}("inp0" => Any[16, 11])),
                Dict{String,Any}(
                    "output" => Any[0, 8, 0, 16, 10, 7, 12, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[8, 0, 16, 10, 7, 12, 10]),
                ),
                Dict{String,Any}("output" => Any[0, 12, 4], "inputs" => Dict{String,Any}("inp0" => Any[12, 4])),
                Dict{String,Any}("output" => Any[0, 1], "inputs" => Dict{String,Any}("inp0" => Any[1])),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 5, 13, 1, 3],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 5, 13, 1, 3]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 6, 8, 0, 11],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 8, 0, 11]),
                ),
                Dict{String,Any}("output" => Any[0, 16], "inputs" => Dict{String,Any}("inp0" => Any[16])),
                Dict{String,Any}(
                    "output" => Any[0, 4, 14, 11, 0],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 14, 11, 0]),
                ),
                Dict{String,Any}("output" => Any[0, 5], "inputs" => Dict{String,Any}("inp0" => Any[5])),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) >= 1
    end

    @testcase_log "remove empty lists" begin
        task = create_task(
            "remove empty lists",
            "inp0:list(list(bool)) -> list(list(bool))",
            [
                Dict{String,Any}(
                    "output" => Any[Any[false, false, false], Any[false], Any[true], Any[true]],
                    "inputs" =>
                        Dict{String,Any}("inp0" => Any[Any[false, false, false], Any[false], Any[true], Any[true]]),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[false, true, false], Any[true, false, false], Any[true, false]],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[Any[false, true, false], Any[], Any[true, false, false], Any[true, false]],
                    ),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[false], Any[true, true, true], Any[true]],
                    "inputs" =>
                        Dict{String,Any}("inp0" => Any[Any[false], Any[], Any[true, true, true], Any[true]]),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[true, false], Any[true, false], Any[true, true, false]],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[Any[], Any[true, false], Any[true, false], Any[true, true, false]],
                    ),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[false], Any[false, false], Any[true, true, true]],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[Any[false], Any[], Any[false, false], Any[true, true, true]],
                    ),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[false, true, true], Any[false, true], Any[true, false]],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[Any[false, true, true], Any[], Any[false, true], Any[true, false]],
                    ),
                ),
                Dict{String,Any}(
                    "output" => Any[
                        Any[false, false, false],
                        Any[false, true, true],
                        Any[false, false, true],
                        Any[false, true],
                    ],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[
                            Any[false, false, false],
                            Any[false, true, true],
                            Any[false, false, true],
                            Any[false, true],
                        ],
                    ),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[true, true], Any[true], Any[true, true]],
                    "inputs" => Dict{String,Any}("inp0" => Any[Any[true, true], Any[true], Any[true, true], Any[]]),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[true, true], Any[true, false], Any[false]],
                    "inputs" =>
                        Dict{String,Any}("inp0" => Any[Any[], Any[true, true], Any[true, false], Any[false]]),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[true], Any[true, true, false], Any[false, true]],
                    "inputs" =>
                        Dict{String,Any}("inp0" => Any[Any[true], Any[], Any[true, true, false], Any[false, true]]),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[true, true, true], Any[true, false]],
                    "inputs" =>
                        Dict{String,Any}("inp0" => Any[Any[true, true, true], Any[], Any[true, false], Any[]]),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[true, true, false], Any[false], Any[false, true, false]],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[Any[], Any[true, true, false], Any[false], Any[false, true, false]],
                    ),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[false], Any[true, false, true], Any[false, true, false], Any[false]],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[Any[false], Any[true, false, true], Any[false, true, false], Any[false]],
                    ),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[false, false], Any[false], Any[false]],
                    "inputs" => Dict{String,Any}("inp0" => Any[Any[false, false], Any[false], Any[], Any[false]]),
                ),
                Dict{String,Any}(
                    "output" => Any[Any[false, false, true], Any[true, true], Any[true], Any[false, true, true]],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Any[Any[false, false, true], Any[true, true], Any[true], Any[false, true, true]],
                    ),
                ),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) == 0
    end

    @testcase_log "prepend-index-k with k=3" begin
        task = create_task(
            "prepend-index-k with k=3",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[9, 15, 12, 9, 14, 7, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 12, 9, 14, 7, 9]),
                ),
                Dict{String,Any}(
                    "output" => Any[1, 7, 8, 1, 6, 16, 11],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 8, 1, 6, 16, 11]),
                ),
                Dict{String,Any}(
                    "output" => Any[1, 11, 3, 1, 8, 15, 7, 7, 14, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[11, 3, 1, 8, 15, 7, 7, 14, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[15, 9, 11, 15, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 11, 15, 2]),
                ),
                Dict{String,Any}("output" => Any[6, 11, 3, 6], "inputs" => Dict{String,Any}("inp0" => Any[11, 3, 6])),
                Dict{String,Any}(
                    "output" => Any[5, 6, 8, 5, 6, 10, 3],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 8, 5, 6, 10, 3]),
                ),
                Dict{String,Any}(
                    "output" => Any[8, 4, 3, 8, 13, 2, 12, 6, 9, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 3, 8, 13, 2, 12, 6, 9, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[13, 3, 15, 13, 1, 8, 13, 9, 6],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 15, 13, 1, 8, 13, 9, 6]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 6, 3, 0, 5, 4, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 3, 0, 5, 4, 2]),
                ),
                Dict{String,Any}(
                    "output" => Any[15, 6, 10, 15, 8, 14, 3, 4, 16, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 10, 15, 8, 14, 3, 4, 16, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[5, 5, 10, 5, 16],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 10, 5, 16]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 8, 14, 3, 5, 11],
                    "inputs" => Dict{String,Any}("inp0" => Any[8, 14, 3, 5, 11]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 11, 10, 3, 14, 0, 5],
                    "inputs" => Dict{String,Any}("inp0" => Any[11, 10, 3, 14, 0, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[14, 15, 6, 14, 4, 12, 0, 15],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 6, 14, 4, 12, 0, 15]),
                ),
                Dict{String,Any}(
                    "output" => Any[6, 13, 16, 6, 9, 16, 6, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 16, 6, 9, 16, 6, 10]),
                ),
            ],
        )
        solutions = test_solve_task(task)
        @test length(solutions) > 0
    end

    @testcase_log "range +1 maximum list" begin
        task = create_task(
            "range +1 maximum list",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 8]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[2, 9, 9, 5, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 0, 6, 7]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 10, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[2, 9, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[10, 8, 0]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 9, 3, 0, 5]),
                ),
                Dict{String,Any}("output" => Any[0, 1, 2, 3], "inputs" => Dict{String,Any}("inp0" => Any[3, 0])),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[10, 0]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 1, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 8, 0]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 9]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6],
                    "inputs" => Dict{String,Any}("inp0" => Any[2, 2, 6]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5, 6, 7, 8],
                    "inputs" => Dict{String,Any}("inp0" => Any[8, 0]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 1, 2, 3, 4, 5],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 5, 3, 4]),
                ),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) == 0
    end

    # @testcase "drop-k with k=5 $cost_power $complexity_power $block_cost_power $any_complexity" for cost_power in
    #                                                                                                 powers_options,
    #     complexity_power in powers_options,
    #     block_cost_power in powers_options,
    #     list_complexity in complexity_options,
    #     set_complexity in complexity_options,
    #     tuple2_complexity in complexity_options,
    #     any_complexity in [0.0, 0.1, 0.5, 1.0, 2.0, 3.0]

    #     hyperparameters = Dict{String,Any}(
    #         "path_cost_power" => cost_power,
    #         "complexity_power" => complexity_power,
    #         "block_cost_power" => block_cost_power,
    #     )
    #     type_weights = Dict{String,Any}(
    #         "int" => 1.0,
    #         "list" => list_complexity,
    #         "color" => 1.0,
    #         "bool" => 1.0,
    #         "float" => 1.0,
    #         "grid" => 1.0,
    #         "tuple2" => tuple2_complexity,
    #         "tuple3" => 1.0,
    #         "coord" => 1.0,
    #         "set" => set_complexity,
    #         "any" => any_complexity,
    #     )
    @testcase_log "drop-k with k=5" begin
        task = create_task(
            "drop-k with k=5",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[7, 2, 11, 14, 6, 7, 11],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 6, 2, 1, 7, 7, 2, 11, 14, 6, 7, 11]),
                ),
                Dict{String,Any}(
                    "output" => Any[11, 15, 11, 2, 7, 8],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 1, 12, 11, 6, 11, 15, 11, 2, 7, 8]),
                ),
                Dict{String,Any}(
                    "output" => Any[5, 6, 0, 6, 3, 16],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 10, 1, 4, 3, 5, 6, 0, 6, 3, 16]),
                ),
                Dict{String,Any}(
                    "output" => Any[16, 12, 9, 2, 7, 13],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 10, 1, 5, 6, 16, 12, 9, 2, 7, 13]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 15, 11, 11, 14],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 8, 14, 3, 14, 3, 15, 11, 11, 14]),
                ),
                Dict{String,Any}(
                    "output" => Any[9, 9, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[14, 2, 8, 4, 1, 9, 9, 4]),
                ),
                Dict{String,Any}("output" => Any[], "inputs" => Dict{String,Any}("inp0" => Any[4, 14, 0, 12, 7])),
                Dict{String,Any}("output" => Any[12], "inputs" => Dict{String,Any}("inp0" => Any[2, 9, 16, 2, 7, 12])),
                Dict{String,Any}(
                    "output" => Any[3, 8, 0, 13],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 8, 7, 16, 13, 3, 8, 0, 13]),
                ),
                Dict{String,Any}(
                    "output" => Any[6, 2, 11, 4, 11],
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 15, 0, 1, 8, 6, 2, 11, 4, 11]),
                ),
                Dict{String,Any}(
                    "output" => Any[0, 4, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 16, 16, 16, 6, 0, 4, 7]),
                ),
                Dict{String,Any}(
                    "output" => Any[9, 1, 13, 4, 8, 6],
                    "inputs" => Dict{String,Any}("inp0" => Any[16, 7, 3, 14, 4, 9, 1, 13, 4, 8, 6]),
                ),
                Dict{String,Any}("output" => Any[5], "inputs" => Dict{String,Any}("inp0" => Any[7, 13, 16, 12, 4, 5])),
                Dict{String,Any}(
                    "output" => Any[11, 9],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 11, 10, 7, 13, 11, 9]),
                ),
                Dict{String,Any}(
                    "output" => Any[7, 11],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 15, 3, 15, 7, 7, 11]),
                ),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) > 0
        # end
    end

    @testcase_log "product" begin
        task = create_task(
            "product",
            "inp0:list(int) -> int",
            [
                Dict{String,Any}("output" => 6, "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 3])),
                Dict{String,Any}("output" => 0, "inputs" => Dict{String,Any}("inp0" => Any[0])),
                Dict{String,Any}("output" => 2, "inputs" => Dict{String,Any}("inp0" => Any[1, 1, 2, 1])),
                Dict{String,Any}("output" => 105, "inputs" => Dict{String,Any}("inp0" => Any[7, 15])),
                Dict{String,Any}("output" => 105, "inputs" => Dict{String,Any}("inp0" => Any[15, 7])),
                Dict{String,Any}("output" => 891, "inputs" => Dict{String,Any}("inp0" => Any[11, 9, 9])),
                Dict{String,Any}("output" => 84, "inputs" => Dict{String,Any}("inp0" => Any[7, 1, 6, 2])),
                Dict{String,Any}("output" => 6, "inputs" => Dict{String,Any}("inp0" => Any[6])),
                Dict{String,Any}("output" => 743424, "inputs" => Dict{String,Any}("inp0" => Any[8, 6, 8, 11, 11, 16])),
                Dict{String,Any}("output" => 483840, "inputs" => Dict{String,Any}("inp0" => Any[10, 6, 8, 4, 6, 6, 7])),
                Dict{String,Any}("output" => 0, "inputs" => Dict{String,Any}("inp0" => Any[16, 1, 14, 0, 12])),
                Dict{String,Any}("output" => 0, "inputs" => Dict{String,Any}("inp0" => Any[0, 4, 11, 12, 15, 5, 2])),
                Dict{String,Any}(
                    "output" => 3243240,
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 5, 6, 11, 6, 13, 14]),
                ),
                Dict{String,Any}("output" => 1755, "inputs" => Dict{String,Any}("inp0" => Any[3, 1, 5, 9, 13])),
                Dict{String,Any}("output" => 34320, "inputs" => Dict{String,Any}("inp0" => Any[3, 10, 8, 13, 11])),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) == 0
    end

    @testcase_log "keep gt 3" begin
        task = create_task(
            "keep gt 3",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}("output" => Any[], "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 3, 2, 2])),
                Dict{String,Any}("output" => Any[6], "inputs" => Dict{String,Any}("inp0" => Any[1, 0, 0, 6, 0])),
                Dict{String,Any}("output" => Any[6, 6], "inputs" => Dict{String,Any}("inp0" => Any[6, 0, 0, 6, 3])),
                Dict{String,Any}("output" => Any[5, 5, 4], "inputs" => Dict{String,Any}("inp0" => Any[5, 2, 0, 5, 4])),
                Dict{String,Any}("output" => Any[5], "inputs" => Dict{String,Any}("inp0" => Any[3, 5, 0, 0, 0])),
                Dict{String,Any}("output" => Any[6, 5], "inputs" => Dict{String,Any}("inp0" => Any[3, 1, 6, 0, 5])),
                Dict{String,Any}("output" => Any[6, 4, 4], "inputs" => Dict{String,Any}("inp0" => Any[3, 3, 6, 4, 4])),
                Dict{String,Any}("output" => Any[5, 5, 5], "inputs" => Dict{String,Any}("inp0" => Any[2, 5, 5, 3, 5])),
                Dict{String,Any}("output" => Any[6, 5], "inputs" => Dict{String,Any}("inp0" => Any[3, 6, 2, 3, 5])),
                Dict{String,Any}("output" => Any[4, 5, 6], "inputs" => Dict{String,Any}("inp0" => Any[4, 5, 6, 2, 1])),
                Dict{String,Any}("output" => Any[6, 4], "inputs" => Dict{String,Any}("inp0" => Any[0, 0, 6, 4, 0])),
                Dict{String,Any}("output" => Any[4, 4], "inputs" => Dict{String,Any}("inp0" => Any[3, 1, 0, 4, 4])),
                Dict{String,Any}("output" => Any[5, 6, 5], "inputs" => Dict{String,Any}("inp0" => Any[5, 6, 5, 2, 3])),
                Dict{String,Any}("output" => Any[6], "inputs" => Dict{String,Any}("inp0" => Any[0, 6, 3, 3, 0])),
                Dict{String,Any}("output" => Any[6, 5], "inputs" => Dict{String,Any}("inp0" => Any[6, 2, 5, 3, 2])),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) == 0
    end

    @testcase_log "modulo-k with k=5" begin
        task = create_task(
            "modulo-k with k=5",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[15])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[10])),
                Dict{String,Any}("output" => Any[], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => Any[0, 1, 0, 4], "inputs" => Dict{String,Any}("inp0" => Any[5, 6, 0, 9])),
                Dict{String,Any}("output" => Any[2, 0], "inputs" => Dict{String,Any}("inp0" => Any[7, 15])),
                Dict{String,Any}("output" => Any[], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}("output" => Any[1], "inputs" => Dict{String,Any}("inp0" => Any[11])),
                Dict{String,Any}("output" => Any[3], "inputs" => Dict{String,Any}("inp0" => Any[13])),
                Dict{String,Any}("output" => Any[2], "inputs" => Dict{String,Any}("inp0" => Any[7])),
                Dict{String,Any}(
                    "output" => Any[2, 2, 3, 0, 3, 0, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[2, 2, 13, 0, 13, 5, 2]),
                ),
                Dict{String,Any}("output" => Any[2, 1, 2], "inputs" => Dict{String,Any}("inp0" => Any[2, 6, 12])),
                Dict{String,Any}("output" => Any[0, 0], "inputs" => Dict{String,Any}("inp0" => Any[0, 10])),
                Dict{String,Any}(
                    "output" => Any[2, 4, 0, 1, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 4, 0, 1, 11]),
                ),
                Dict{String,Any}("output" => Any[], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}(
                    "output" => Any[1, 2, 1, 1, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[11, 2, 16, 6, 4]),
                ),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) == 0
    end

    @testcase_log "prepend-k with k=3" begin
        task = create_task(
            "prepend-k with k=3",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[3, 16, 4, 10, 12, 5, 11],
                    "inputs" => Dict{String,Any}("inp0" => Any[16, 4, 10, 12, 5, 11]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 13, 8, 9, 4, 0],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 8, 9, 4, 0]),
                ),
                Dict{String,Any}("output" => Any[3, 0, 6], "inputs" => Dict{String,Any}("inp0" => Any[0, 6])),
                Dict{String,Any}(
                    "output" => Any[3, 5, 3, 0, 3, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 3, 0, 3, 7]),
                ),
                Dict{String,Any}("output" => Any[3, 6, 0], "inputs" => Dict{String,Any}("inp0" => Any[6, 0])),
                Dict{String,Any}("output" => Any[3], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}(
                    "output" => Any[3, 2, 5, 9, 14, 14],
                    "inputs" => Dict{String,Any}("inp0" => Any[2, 5, 9, 14, 14]),
                ),
                Dict{String,Any}("output" => Any[3, 7], "inputs" => Dict{String,Any}("inp0" => Any[7])),
                Dict{String,Any}("output" => Any[3], "inputs" => Dict{String,Any}("inp0" => Any[])),
                Dict{String,Any}(
                    "output" => Any[3, 13, 14, 10, 10, 14, 14],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 14, 10, 10, 14, 14]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 0, 2, 11, 9, 3],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 2, 11, 9, 3]),
                ),
                Dict{String,Any}("output" => Any[3, 11, 14, 7], "inputs" => Dict{String,Any}("inp0" => Any[11, 14, 7])),
                Dict{String,Any}(
                    "output" => Any[3, 9, 14, 2, 5, 12, 10, 3],
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 14, 2, 5, 12, 10, 3]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 10, 0, 8, 0],
                    "inputs" => Dict{String,Any}("inp0" => Any[10, 0, 8, 0]),
                ),
                Dict{String,Any}("output" => Any[3, 14, 11], "inputs" => Dict{String,Any}("inp0" => Any[14, 11])),
            ],
        )

        solutions = test_solve_task(task)
        @test length(solutions) > 0
    end
end
