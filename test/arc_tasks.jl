using solver:
    create_arc_task,
    get_starting_grammar,
    get_guiding_model,
    solve_task,
    set_current_grammar!,
    GuidingModelServer,
    start_server,
    stop_server

@testset "Arc tasks" begin
    function _create_arc_task(filename, dir = "ARC/data/training/")
        fname = "data/" * dir * filename
        tp = parse_type("inp0:grid(color) -> grid(color)")
        return create_arc_task(fname, tp)
    end

    grammar = get_starting_grammar()
    guiding_model = get_guiding_model("dummy")
    set_current_grammar!(guiding_model, grammar)
    type_weights = Dict{String,Any}(
        "int" => 1.0,
        "list" => 1.0,
        "color" => 1.0,
        "bool" => 1.0,
        "grid" => 1.0,
        "tuple2" => 1.0,
        "set" => 1.0,
        "any" => 1.0,
        "either" => 0.0,
    )
    hyperparameters = Dict{String,Any}(
        "path_cost_power" => 1.0,
        "complexity_power" => 1.0,
        "block_cost_power" => 1.0,
        "explained_penalty_power" => 1.0,
        "explained_penalty_mult" => 5.0,
        "match_duplicates_penalty" => 3.0,
    )

    function test_solve_task(task, verbose = false)
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
                40,
                1,
                type_weights,
                hyperparameters,
                10,
                verbose,
            )
        finally
            stop_server(guiding_model_server)
        end
    end

    @testcase_log "a416b8f3.json" begin
        task = _create_arc_task("a416b8f3.json")

        result = test_solve_task(task)
        @test length(result) == 10
    end
end
