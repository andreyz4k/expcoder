
function hyperparam_search(; kwargs...)
    @info "Starting hyperparameter search"
    sweep_tag = randstring(12)
    group_tag = randstring(12)

    parsed_args = parse_args(ARGS, config_options(); as_symbols = true)
    merge!(parsed_args, kwargs)
    tasks = get_domain_tasks(parsed_args[:domain])

    if !isnothing(parsed_args[:resume])
        (restored_args, i, traces, grammar, guiding_model) = load_checkpoint(parsed_args[:resume])
        parsed_args = merge(restored_args, parsed_args)
    else
        grammar = get_starting_grammar()
        guiding_model = get_guiding_model(parsed_args[:model])
        i = 1
        traces = Dict{UInt64,Any}()
    end

    @info "Parsed arguments $parsed_args"

    grammar_hash = hash(grammar)
    guiding_model_server = GuidingModelServer(guiding_model)
    start_server(guiding_model_server)
    set_current_grammar!(guiding_model, grammar)
    worker_pool = ReplenishingWorkerPool(parsed_args[:workers])

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

    tasks_to_check = [t for t in tasks if haskey(traces[grammar_hash][2], t.name)]
    tasks = tasks_to_check

    k = 1

    # Main macro. The first argument to the for loop is always interpreted as the number of iterations
    try
        traces = get_manual_traces(
            parsed_args[:domain],
            tasks,
            grammar,
            grammar_hash,
            worker_pool,
            guiding_model_server,
            traces,
        )

        for path_cost_power in shuffle([0, 0.1, 0.3, 0.5, 1, 1.5, 2]),
            complexity_power in shuffle([0, 0.1, 0.3, 0.5, 1, 1.5, 2]),
            block_cost_power in shuffle([0, 0.1, 0.3, 0.5, 1, 1.5, 2])

            # for path_cost_power in [1], complexity_power in [1], block_cost_power in [1]
            hyperparameters = Dict(
                "path_cost_power" => path_cost_power,
                "complexity_power" => complexity_power,
                "block_cost_power" => block_cost_power,
            )
            @info "Running $k with hyperparameters $hyperparameters"
            k += 1
            tags = [sweep_tag]

            lg = WandbLogger(; project = "expcoder", group = group_tag, tags = tags, config = hyperparameters)
            wandb_run_id = string(lg.wrun.id)
            @info "Wandb run id $wandb_run_id"

            # Serialization.serialize(
            #     "manual_traces_$(i).jls",
            #     Dict{UInt64,Any}(h => ([string(p) for p in g], t) for (h, (g, t)) in traces),
            # )
            # guiding_model = update_guiding_model(guiding_model, traces)
            # @info "Finished updating model with manual traces"

            cur_traces = traces[grammar_hash][2]
            new_traces = try_solve_tasks(
                worker_pool,
                tasks,
                guiding_model_server,
                grammar,
                cur_traces,
                parsed_args[:timeout],
                parsed_args[:program_timeout],
                type_weights,
                hyperparameters,
                parsed_args[:maximum_solutions],
                parsed_args[:verbose],
            )

            Wandb.log(lg, Dict("solved_tasks" => length(new_traces)))

            log_traces(Dict(t["task"].name => t["traces"] for t in new_traces))
            close(lg)
        end
    finally
        stop(worker_pool)
        stop_server(guiding_model_server, true)
    end
end
