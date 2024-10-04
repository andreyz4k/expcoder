
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
    make_dummy_contextual

@testset "Abstractors tasks" begin
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

    timeout = 40
    program_timeout = 3.0
    maximum_solutions = 10
    verbose = false
    hyperparameters = Dict{String,Any}("path_cost_power" => 1.0, "complexity_power" => 1.0, "block_cost_power" => 1.0)
    guiding_model = get_guiding_model("dummy")
    grammar = get_starting_grammar()

    log_variable = 4.0
    log_lambda = -10.0
    log_free_var = -3.0
    productions = Tuple{Program,Tp,Float64}[(p, p.t, p.name == "rev_fix_param" ? 4.0 : 0.0) for p in grammar]
    g = Grammar(log_variable, log_lambda, log_free_var, productions, nothing)
    guiding_model.grammars[grammar] = make_dummy_contextual(g)

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

    @testcase_log "Repeat" begin
        task = create_task(
            "invert repeated",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[4, 4, 4, 4, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 5, 5, 5]),
                ),
                Dict{String,Any}("output" => Any[1, 1, 1, 1, 1, 1], "inputs" => Dict{String,Any}("inp0" => Any[6])),
                Dict{String,Any}("output" => Any[3, 3], "inputs" => Dict{String,Any}("inp0" => Any[2, 2, 2])),
            ],
        )

        solutions = @time solve_task(
            task,
            guiding_model,
            grammar,
            nothing,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
        @test length(solutions) >= 1
    end

    @testcase_log "Find const" begin
        task = create_task(
            "find const",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[4, 4, 4, 4, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[5, 5, 5, 5]),
                ),
                Dict{String,Any}("output" => Any[1, 1, 1, 1, 1], "inputs" => Dict{String,Any}("inp0" => Any[6])),
                Dict{String,Any}("output" => Any[3, 3, 3, 3, 3], "inputs" => Dict{String,Any}("inp0" => Any[2, 2, 2])),
            ],
        )

        solutions = @time solve_task(
            task,
            guiding_model,
            grammar,
            nothing,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
        @test length(solutions) >= 1
    end

    @testcase_log "Use eithers" begin
        task = create_task(
            "use eithers",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 3, 4, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[4, 2, 4, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 2, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 3, 3, 8, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 3, 3, 8]),
                ),
            ],
        )

        solutions = @time solve_task(
            task,
            guiding_model,
            grammar,
            nothing,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
        @test length(solutions) >= 1
    end

    @testcase_log "Use eithers 2" begin
        task = create_task(
            "use eithers",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 3, 4, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[4, 2, 4, 3, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 2, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 3, 3, 8, 4, 6, 7, 8, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 3, 3, 8]),
                ),
            ],
        )
        solutions = @time solve_task(
            task,
            guiding_model,
            grammar,
            nothing,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
        @test length(solutions) >= 1
    end

    @testcase_log "Use eithers from input" begin
        task = create_task(
            "use eithers",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[1, 2, 3, 4, 5],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 3, 4, 5, 10, 9, 8, 7]),
                ),
                Dict{String,Any}(
                    "output" => Any[4, 2, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 2, 4, 10, 9, 8, 7]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 3, 3, 8],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 3, 3, 8, 10, 9, 8, 7]),
                ),
            ],
        )

        solutions = @time solve_task(
            task,
            guiding_model,
            grammar,
            nothing,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
        @test length(solutions) >= 1
    end

    # powers_options = [1.0, 2.0, 3.0, 4.0, 5.0]
    # complexity_options = [1.0]

    # @testcase "Replace background $cost_power $complexity_power $block_cost_power $any_complexity" for cost_power in
    #                                                                                                    powers_options,
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

    @testcase_log "Replace background" begin
        task = create_task(
            "replace background",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[1, 2, 1, 4, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 2, 3, 4, 3]),
                ),
                Dict{String,Any}(
                    "output" => Any[4, 2, 4, 1, 1, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 2, 4, 3, 3, 3]),
                ),
                Dict{String,Any}(
                    "output" => Any[1, 5, 2, 6, 1, 1, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 5, 2, 6, 3, 3, 4]),
                ),
            ],
        )

        g_base_cont = guiding_model.grammars[grammar]
        g_base = g_base_cont.no_context

        productions = Tuple{Program,Tp,Float64}[
            (p, p.t, in(p.name, Set(["repeat", "eq?", "rev_select", "rev_fix_param"])) ? 4.0 : 0.0) for p in grammar
        ]
        g = Grammar(g_base.log_variable, g_base.log_lambda, g_base.log_free_var, productions, nothing)
        guiding_model.grammars[grammar] = make_dummy_contextual(g)

        solutions = @time solve_task(
            task,
            guiding_model,
            grammar,
            nothing,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
        @test length(solutions) >= 1
        guiding_model.grammars[grammar] = g_base_cont
    end
    # end
end
