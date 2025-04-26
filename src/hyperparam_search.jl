using HyperTuning
using Wandb

function hyperparam_search(; kwargs...)
    sweep_tag = randstring(12)
    group_tag = "hyperparam_search3"
    @info "Starting hyperparameter search with group tag $group_tag and sweep tag $sweep_tag"

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

    tasks_to_check = [t for t in tasks if haskey(traces[grammar_hash][2], t.name)]
    tasks = tasks_to_check

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

        function objective(trial)
            @unpack path_cost_power,
            complexity_power,
            block_cost_power,
            explained_penalty_power,
            explained_penalty_mult,
            match_duplicates_penalty,
            weight_int,
            weight_list,
            weight_color,
            weight_bool,
            weight_grid,
            weight_tuple2,
            weight_set,
            weight_any,
            weight_either = trial
            hyperparameters = Dict(
                "path_cost_power" => path_cost_power,
                "complexity_power" => complexity_power,
                "block_cost_power" => block_cost_power,
                "explained_penalty_power" => explained_penalty_power,
                "explained_penalty_mult" => explained_penalty_mult,
                "match_duplicates_penalty" => match_duplicates_penalty,
            )
            type_weights = Dict{String,Any}(
                "int" => weight_int,
                "list" => weight_list,
                "color" => weight_color,
                "bool" => weight_bool,
                "grid" => weight_grid,
                "tuple2" => weight_tuple2,
                "set" => weight_set,
                "any" => weight_any,
                "either" => weight_either,
            )
            @info "Running with hyperparameters $hyperparameters"
            tags = [sweep_tag]

            lg = WandbLogger(;
                project = "expcoder",
                group = group_tag,
                tags = tags,
                config = merge(
                    hyperparameters,
                    Dict(
                        "weight_int" => weight_int,
                        "weight_list" => weight_list,
                        "weight_color" => weight_color,
                        "weight_bool" => weight_bool,
                        "weight_grid" => weight_grid,
                        "weight_tuple2" => weight_tuple2,
                        "weight_set" => weight_set,
                        "weight_any" => weight_any,
                        "weight_either" => weight_either,
                    ),
                ),
            )
            # wandb_run_id = string(lg.wrun.id)
            # @info "Wandb run id $wandb_run_id"

            # Serialization.serialize(
            #     "manual_traces_$(i).jls",
            #     Dict{UInt64,Any}(h => ([string(p) for p in g], t) for (h, (g, t)) in traces),
            # )
            # guiding_model = update_guiding_model(guiding_model, traces)
            # @info "Finished updating model with manual traces"

            try
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
                return Float64(-length(new_traces))
            finally
                close(lg)
            end
        end

        scenario = Scenario(
            path_cost_power = (-3.0 .. 3.5),
            complexity_power = (1.0 .. 2.5),
            block_cost_power = (5.0 .. 8.0),
            explained_penalty_power = (1.0 .. 8.0),
            explained_penalty_mult = (1.0 .. 20.0),
            match_duplicates_penalty = (1.0 .. 100.0),
            weight_int = [1.0, 2.0],
            weight_list = [1.0, 2.0],
            weight_color = [2.0, 4.0],
            weight_bool = [0.5, 1.0, 2.0, 4.0],
            weight_grid = [1.0, 1.0],
            weight_tuple2 = [0.5, 2.0, 4.0],
            weight_set = [1.0, 1.0],
            weight_any = [0.0, 0.1],
            weight_either = [0.0, 0.1, 0.2, 0.5, 4.0],
            max_trials = 600,
            batch_size = 1,
        )
        # scenario = Scenario(
        #     path_cost_power = [1.0, 1.0],
        #     complexity_power = [1.0, 1.0],
        #     block_cost_power = [1.0, 1.0],
        #     explained_penalty_power = [1.0, 1.0],
        #     explained_penalty_mult = [1.0, 1.0],
        #     match_duplicates_penalty = [3.0, 3.0],
        #     weight_int = [1.0, 1.0],
        #     weight_list = [1.0, 1.0],
        #     weight_color = [1.0, 1.0],
        #     weight_bool = [1.0, 1.0],
        #     weight_grid = [1.0, 1.0],
        #     weight_tuple2 = [1.0, 1.0],
        #     weight_set = [1.0, 1.0],
        #     weight_any = [1.0, 1.0],
        #     weight_either = [0.0, 0.0],
        #     max_trials = 1,
        #     batch_size = 1,
        # )

        HyperTuning.optimize(objective, scenario)

    finally
        stop(worker_pool)
        stop_server(guiding_model_server, true)
    end
end
