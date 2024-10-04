using solver:
    solve_task,
    get_guiding_model,
    get_starting_grammar,
    Task,
    parse_type,
    supervised_task_checker,
    parse_program,
    _get_custom_arg_checkers,
    is_reversible

@testset "Inventions" begin
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
    program_timeout = 1.0
    maximum_solutions = 10
    verbose = false
    hyperparameters = Dict{String,Any}("path_cost_power" => 1.0, "complexity_power" => 1.0, "block_cost_power" => 1.0)
    guiding_model = get_guiding_model("dummy")
    base_grammar = get_starting_grammar()

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

    @testcase_log "slice-k-n with k=2 and n=1" begin
        task = create_task(
            "slice-k-n with k=2 and n=1",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}("output" => Any[13], "inputs" => Dict{String,Any}("inp0" => Any[9, 13, 15, 7, 10])),
                Dict{String,Any}(
                    "output" => Any[7],
                    "inputs" => Dict{String,Any}("inp0" => Any[16, 7, 12, 11, 14, 6, 9, 14, 0, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[13],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 13, 3, 4, 8, 16, 5, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[15],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 15, 0, 9, 9, 15, 15, 3, 4]),
                ),
                Dict{String,Any}("output" => Any[12], "inputs" => Dict{String,Any}("inp0" => Any[11, 12, 4, 5, 2])),
                Dict{String,Any}("output" => Any[2], "inputs" => Dict{String,Any}("inp0" => Any[15, 2, 4, 4, 4, 9])),
                Dict{String,Any}("output" => Any[15], "inputs" => Dict{String,Any}("inp0" => Any[5, 15, 15, 13, 6])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[0, 0, 4, 12, 0, 3, 9])),
                Dict{String,Any}(
                    "output" => Any[0],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 0, 3, 0, 11, 2, 1, 0, 8, 1, 15]),
                ),
                Dict{String,Any}("output" => Any[1], "inputs" => Dict{String,Any}("inp0" => Any[16, 1, 14, 11, 16, 4])),
                Dict{String,Any}("output" => Any[15], "inputs" => Dict{String,Any}("inp0" => Any[16, 15, 9, 11, 12])),
                Dict{String,Any}(
                    "output" => Any[15],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 15, 13, 6, 16, 2]),
                ),
                Dict{String,Any}("output" => Any[10], "inputs" => Dict{String,Any}("inp0" => Any[12, 10, 1, 9, 6])),
                Dict{String,Any}("output" => Any[6], "inputs" => Dict{String,Any}("inp0" => Any[2, 6, 5, 5, 2])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[9, 0, 16, 9, 10])),
            ],
        )

        grammar = vcat(base_grammar, [parse_program("#(lambda (repeat (car \$0)))")])

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

    @testcase_log "Invented abstractor 1" begin
        task = create_task(
            "slice-k-n with k=2 and n=1",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}("output" => Any[13], "inputs" => Dict{String,Any}("inp0" => Any[9, 13, 15, 7, 10])),
                Dict{String,Any}(
                    "output" => Any[7],
                    "inputs" => Dict{String,Any}("inp0" => Any[16, 7, 12, 11, 14, 6, 9, 14, 0, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[13],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 13, 3, 4, 8, 16, 5, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[15],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 15, 0, 9, 9, 15, 15, 3, 4]),
                ),
                Dict{String,Any}("output" => Any[12], "inputs" => Dict{String,Any}("inp0" => Any[11, 12, 4, 5, 2])),
                Dict{String,Any}("output" => Any[2], "inputs" => Dict{String,Any}("inp0" => Any[15, 2, 4, 4, 4, 9])),
                Dict{String,Any}("output" => Any[15], "inputs" => Dict{String,Any}("inp0" => Any[5, 15, 15, 13, 6])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[0, 0, 4, 12, 0, 3, 9])),
                Dict{String,Any}(
                    "output" => Any[0],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 0, 3, 0, 11, 2, 1, 0, 8, 1, 15]),
                ),
                Dict{String,Any}("output" => Any[1], "inputs" => Dict{String,Any}("inp0" => Any[16, 1, 14, 11, 16, 4])),
                Dict{String,Any}("output" => Any[15], "inputs" => Dict{String,Any}("inp0" => Any[16, 15, 9, 11, 12])),
                Dict{String,Any}(
                    "output" => Any[15],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 15, 13, 6, 16, 2]),
                ),
                Dict{String,Any}("output" => Any[10], "inputs" => Dict{String,Any}("inp0" => Any[12, 10, 1, 9, 6])),
                Dict{String,Any}("output" => Any[6], "inputs" => Dict{String,Any}("inp0" => Any[2, 6, 5, 5, 2])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[9, 0, 16, 9, 10])),
            ],
        )

        grammar = vcat(
            base_grammar,
            [
                parse_program("#(lambda (repeat (car \$0)))"),
                parse_program("#(lambda (lambda (repeat (cons \$0 \$1))))"),
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

    @testcase_log "Invented abstractors 2" begin
        task = create_task(
            "append-index-k with k=3",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[0, 13, 12, 12, 12],
                    "inputs" => Dict{String,Any}("inp0" => Any[0, 13, 12, 12]),
                ),
                Dict{String,Any}(
                    "output" => Any[6, 8, 2, 6, 7, 14, 9, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 8, 2, 6, 7, 14, 9]),
                ),
                Dict{String,Any}(
                    "output" => Any[6, 15, 6, 15, 5, 13, 6],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 15, 6, 15, 5, 13]),
                ),
                Dict{String,Any}(
                    "output" => Any[15, 13, 7, 2, 4, 10, 7],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 13, 7, 2, 4, 10]),
                ),
                Dict{String,Any}(
                    "output" => Any[1, 2, 1, 7, 12, 15, 12, 13, 11, 4, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 2, 1, 7, 12, 15, 12, 13, 11, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[9, 5, 2, 15, 8, 1, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[9, 5, 2, 15, 8, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[3, 13, 5, 7, 4, 3, 3, 5],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 13, 5, 7, 4, 3, 3]),
                ),
                Dict{String,Any}(
                    "output" => Any[6, 14, 12, 4, 4, 15, 3, 1, 4, 12],
                    "inputs" => Dict{String,Any}("inp0" => Any[6, 14, 12, 4, 4, 15, 3, 1, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[14, 2, 10, 6, 7, 9, 14, 2, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[14, 2, 10, 6, 7, 9, 14, 2]),
                ),
                Dict{String,Any}(
                    "output" => Any[11, 11, 2, 9, 2],
                    "inputs" => Dict{String,Any}("inp0" => Any[11, 11, 2, 9]),
                ),
                Dict{String,Any}(
                    "output" => Any[8, 6, 13, 11, 15, 2, 13],
                    "inputs" => Dict{String,Any}("inp0" => Any[8, 6, 13, 11, 15, 2]),
                ),
                Dict{String,Any}(
                    "output" => Any[15, 0, 13, 10, 7, 1, 14, 5, 10, 10, 13],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 0, 13, 10, 7, 1, 14, 5, 10, 10]),
                ),
                Dict{String,Any}(
                    "output" => Any[11, 0, 12, 10, 15, 13, 12],
                    "inputs" => Dict{String,Any}("inp0" => Any[11, 0, 12, 10, 15, 13]),
                ),
                Dict{String,Any}(
                    "output" => Any[14, 10, 10, 14, 14, 2, 9, 10],
                    "inputs" => Dict{String,Any}("inp0" => Any[14, 10, 10, 14, 14, 2, 9]),
                ),
                Dict{String,Any}(
                    "output" => Any[12, 7, 16, 14, 16],
                    "inputs" => Dict{String,Any}("inp0" => Any[12, 7, 16, 14]),
                ),
            ],
        )

        grammar = vcat(
            base_grammar,
            [
                parse_program("#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2)))))"),
                parse_program("#(lambda (repeat \$0 Const(int, 1)))"),
                parse_program("#(lambda (lambda (- \$0 (- \$0 \$1))))"),
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

    @testcase_log "Invented abstractors 3" begin
        task = create_task(
            "slice-k-n with k=2 and n=1",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}("output" => Any[13], "inputs" => Dict{String,Any}("inp0" => Any[9, 13, 15, 7, 10])),
                Dict{String,Any}(
                    "output" => Any[7],
                    "inputs" => Dict{String,Any}("inp0" => Any[16, 7, 12, 11, 14, 6, 9, 14, 0, 5]),
                ),
                Dict{String,Any}(
                    "output" => Any[13],
                    "inputs" => Dict{String,Any}("inp0" => Any[7, 13, 3, 4, 8, 16, 5, 1]),
                ),
                Dict{String,Any}(
                    "output" => Any[15],
                    "inputs" => Dict{String,Any}("inp0" => Any[15, 15, 0, 9, 9, 15, 15, 3, 4]),
                ),
                Dict{String,Any}("output" => Any[12], "inputs" => Dict{String,Any}("inp0" => Any[11, 12, 4, 5, 2])),
                Dict{String,Any}("output" => Any[2], "inputs" => Dict{String,Any}("inp0" => Any[15, 2, 4, 4, 4, 9])),
                Dict{String,Any}("output" => Any[15], "inputs" => Dict{String,Any}("inp0" => Any[5, 15, 15, 13, 6])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[0, 0, 4, 12, 0, 3, 9])),
                Dict{String,Any}(
                    "output" => Any[0],
                    "inputs" => Dict{String,Any}("inp0" => Any[3, 0, 3, 0, 11, 2, 1, 0, 8, 1, 15]),
                ),
                Dict{String,Any}("output" => Any[1], "inputs" => Dict{String,Any}("inp0" => Any[16, 1, 14, 11, 16, 4])),
                Dict{String,Any}("output" => Any[15], "inputs" => Dict{String,Any}("inp0" => Any[16, 15, 9, 11, 12])),
                Dict{String,Any}(
                    "output" => Any[15],
                    "inputs" => Dict{String,Any}("inp0" => Any[13, 15, 13, 6, 16, 2]),
                ),
                Dict{String,Any}("output" => Any[10], "inputs" => Dict{String,Any}("inp0" => Any[12, 10, 1, 9, 6])),
                Dict{String,Any}("output" => Any[6], "inputs" => Dict{String,Any}("inp0" => Any[2, 6, 5, 5, 2])),
                Dict{String,Any}("output" => Any[0], "inputs" => Dict{String,Any}("inp0" => Any[9, 0, 16, 9, 10])),
            ],
        )

        grammar = vcat(
            base_grammar,
            [
                parse_program("#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2)))))"),
                parse_program("#(lambda (repeat \$0 Const(int, 1)))"),
                parse_program("#(lambda (lambda (+ (- \$0 \$1) \$1)))"),
                parse_program(
                    "#(lambda (lambda (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) Const(list(int), Any[]) \$0 \$1)))",
                ),
                parse_program("#(lambda (lambda (concat \$0 (#(lambda (repeat \$0 Const(int, 1))) \$1))))"),
                parse_program(
                    "#(lambda (lambda (lambda (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) (#(lambda (repeat \$0 Const(int, 1))) \$0) \$1 \$2))))",
                ),
                parse_program("#(lambda (concat \$0 \$0))"),
                parse_program("#(lambda (lambda (rev_fix_param (* \$1 \$0) \$1 (lambda Const(int, -1)))))"),
                parse_program("#(lambda (#(lambda (concat \$0 \$0)) (#(lambda (concat \$0 \$0)) \$0)))"),
                parse_program("#(lambda (lambda (lambda (- (- \$0 \$1) \$2))))"),
                parse_program("#(lambda (lambda (#(lambda (repeat \$0 Const(int, 1))) (+ \$1 (- \$0 \$1)))))"),
                parse_program(
                    "#(lambda (lambda (lambda (cons \$0 (#(lambda (lambda (concat \$0 (#(lambda (repeat \$0 Const(int, 1))) \$1)))) \$1 \$2)))))",
                ),
                parse_program("#(lambda (cdr (cdr \$0)))"),
                parse_program("#(lambda (concat \$0 (#(lambda (concat \$0 \$0)) \$0)))"),
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

    @testcase_log "Custom arg checkers 1" begin
        p = parse_program(
            "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$1)) \$1 \$2)))) \$0 \$1 \$2) \$2 (lambda Const(color, 0))))))",
        )
        @test is_reversible(p)
        @test _get_custom_arg_checkers(p) == []
    end

    @testcase_log "Custom arg checkers 2" begin
        p = parse_program("#(lambda (lambda (lambda (rows_to_grid (\$0 (\$1 (rows (rows_to_grid \$2))))))))")
        @test is_reversible(p)
        @test _get_custom_arg_checkers(p) == []
    end
end
