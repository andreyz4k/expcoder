
using ArgParse
using JSON

function create_arc_task(fname, tp)
    arc_task = JSON.parsefile(fname)

    train_inputs = []
    train_outputs = []
    for example in arc_task["train"]
        push!(train_inputs, Dict("inp0" => vcat([reshape(r, (1, length(r))) for r in example["input"]]...)))
        push!(train_outputs, vcat([reshape(r, (1, length(r))) for r in example["output"]]...))
    end
    test_inputs = []
    test_outputs = []
    for example in arc_task["test"]
        push!(test_inputs, Dict("inp0" => vcat([reshape(r, (1, length(r))) for r in example["input"]]...)))
        push!(test_outputs, vcat([reshape(r, (1, length(r))) for r in example["output"]]...))
    end

    return Task(basename(fname), tp, supervised_task_checker, train_inputs, train_outputs, test_inputs, test_outputs)
end

function get_arc_tasks()
    tasks = []
    tp = parse_type("inp0:grid(color) -> grid(color)")
    arc_folder = normpath(joinpath(@__DIR__, "../..", "data"))
    for fname in readdir(joinpath(arc_folder, "sortOfARC"); join = true)
        if endswith(fname, ".json")
            task = create_arc_task(fname, tp)
            push!(tasks, task)
        end
    end
    for fname in readdir(joinpath(arc_folder, "ARC/data/training"); join = true)
        if endswith(fname, ".json")
            task = create_arc_task(fname, tp)
            push!(tasks, task)
        end
    end
    return tasks
end

function get_domain_tasks(domain)
    if domain == "arc"
        return get_arc_tasks()
    end
    error("Unknown domain: $domain")
end

function get_starting_grammar()
    Program[p for (_, p) in every_primitive]
end

function get_guiding_model(model)
    if model == "dummy"
        return DummyGuidingModel()
    elseif model == "nn"
        return NNGuidingModel()
    end
    error("Unknown model: $model")
end

function enqueue_updates(sc::SolutionContext, guiding_model_channels, grammar)
    new_unknown_branches = Set(get_new_values(sc.branch_is_unknown))
    new_explained_branches = Set(get_new_values(sc.branch_is_not_copy))
    updated_factors_unknown_branches = Set(get_new_values(sc.unknown_complexity_factors))
    updated_factors_explained_branches = Set(get_new_values(sc.explained_complexity_factors))
    for branch_id in updated_factors_unknown_branches
        if in(branch_id, new_unknown_branches)
            enqueue_unknown_var(sc, branch_id, guiding_model_channels, grammar)
        elseif haskey(sc.branch_queues_unknown, branch_id)
            update_branch_priority(sc, branch_id, false)
        end
    end
    for branch_id in union(updated_factors_explained_branches, new_explained_branches)
        if !sc.branch_is_not_copy[branch_id]
            continue
        end
        if !haskey(sc.branch_queues_explained, branch_id)
            enqueue_known_var(sc, branch_id, guiding_model_channels, grammar)
        else
            update_branch_priority(sc, branch_id, true)
        end
    end
end

function block_state_successors(sc::SolutionContext, max_free_parameters, bp::BlockPrototype)::Vector{BlockPrototype}
    current_hole = follow_path(bp.skeleton, bp.path)
    if !isa(current_hole, Hole)
        error("Error during following path")
    end
    request = current_hole.t

    context = bp.context
    context, request = apply_context(context, request)
    if isarrow(request)
        return [
            BlockPrototype(
                modify_skeleton(
                    bp.skeleton,
                    (Abstraction(
                        Hole(
                            request.arguments[2],
                            nothing,
                            current_hole.locations,
                            step_arg_checker(current_hole.candidates_filter, ArgTurn(request.arguments[1])),
                            current_hole.possible_values,
                        ),
                    )),
                    bp.path,
                ),
                context,
                vcat(bp.path, [ArgTurn(request.arguments[1])]),
                bp.cost,
                bp.free_parameters,
                bp.request,
                bp.input_vars,
                bp.output_var,
                bp.reverse,
            ),
        ]
    else
        environment = path_environment(bp.path)

        bp_output_entry_id = sc.branch_entries[bp.output_var[2]]
        cg = sc.entry_grammars[(bp_output_entry_id, bp.reverse)]

        candidates = unifying_expressions(cg, environment, context, current_hole, bp.skeleton, bp.path)

        bps = map(candidates) do (candidate, argument_types, context, ll)
            if isa(candidate, Abstraction)
                new_free_parameters = 0
                application_template =
                    Apply(candidate, Hole(argument_types[1], nothing, [], current_hole.candidates_filter, nothing))
                new_skeleton = modify_skeleton(bp.skeleton, application_template, bp.path)
                new_path = vcat(bp.path, [LeftTurn(), ArgTurn(argument_types[1])])
            else
                new_free_parameters = number_of_free_parameters(candidate)

                if isempty(argument_types)
                    new_skeleton = modify_skeleton(bp.skeleton, candidate, bp.path)
                    new_path = unwind_path(bp.path, new_skeleton)
                else
                    application_template = candidate
                    custom_arg_checkers = _get_custom_arg_checkers(candidate)
                    custom_checkers_args_count = length(custom_arg_checkers)
                    for i in 1:length(argument_types)
                        current_checker = step_arg_checker(current_hole.candidates_filter, (candidate, i))

                        if i > custom_checkers_args_count || isnothing(custom_arg_checkers[i])
                            arg_checker = current_checker
                        else
                            arg_checker = combine_arg_checkers(current_checker, custom_arg_checkers[i])
                        end

                        application_template = Apply(
                            application_template,
                            Hole(argument_types[i], nothing, [(candidate, i)], arg_checker, nothing),
                        )
                    end
                    new_skeleton = modify_skeleton(bp.skeleton, application_template, bp.path)
                    new_path = vcat(bp.path, [LeftTurn() for _ in 2:length(argument_types)], [RightTurn()])
                end
            end
            context, new_request = apply_context(context, bp.request)
            return BlockPrototype(
                new_skeleton,
                context,
                new_path,
                bp.cost + ll,
                bp.free_parameters + new_free_parameters,
                new_request,
                bp.input_vars,
                bp.output_var,
                bp.reverse,
            )
        end
        return filter(
            (new_bp -> !state_violates_symmetry(new_bp.skeleton) && new_bp.free_parameters <= max_free_parameters),
            bps,
        )
    end
end

function enumeration_iteration_finished_output(sc::SolutionContext, bp::BlockPrototype)
    is_reverse = is_reversible(bp.skeleton)
    output_branch_id = bp.output_var[2]
    output_entry = sc.entries[sc.branch_entries[output_branch_id]]
    if is_reverse &&
       !isa(output_entry, AbductibleEntry) &&
       !(isa(output_entry, PatternEntry) && all(v == PatternWrapper(any_object) for v in output_entry.values))
        # @info "Try get reversed for $bp"
        p, input_vars = try_get_reversed_inputs(sc, bp.skeleton, bp.context, bp.path, bp.output_var[2], bp.cost)
        var_locations = collect_var_locations(p)
        for (var_id, locations) in var_locations
            sc.unknown_var_locations[var_id] = collect(locations)
        end
    elseif isnothing(bp.input_vars)
        p, new_vars = capture_free_vars(sc, bp.skeleton, bp.context)
        input_vars = []
        min_path_cost = sc.unknown_min_path_costs[output_branch_id] + bp.cost
        complexity_factor = sc.unknown_complexity_factors[output_branch_id]
        for (var_id, t) in new_vars
            t_id = push!(sc.types, t)
            entry = NoDataEntry(t_id)
            entry_index = push!(sc.entries, entry)
            branch_id = increment!(sc.branches_count)
            sc.branch_entries[branch_id] = entry_index
            sc.branch_vars[branch_id] = var_id
            sc.branch_types[branch_id, t_id] = true
            sc.branch_is_unknown[branch_id] = true
            sc.branch_unknown_from_output[branch_id] = sc.branch_unknown_from_output[output_branch_id]
            sc.unknown_min_path_costs[branch_id] = min_path_cost
            sc.unknown_complexity_factors[branch_id] = complexity_factor

            push!(input_vars, (var_id, branch_id, t_id))
        end
        constrained_branches = [b_id for (_, b_id, t_id) in input_vars if is_polymorphic(sc.types[t_id])]
        constrained_vars = [v_id for (v_id, _, t_id) in input_vars if is_polymorphic(sc.types[t_id])]
        if length(constrained_branches) >= 2
            context_id = push!(sc.constraint_contexts, bp.context)
            new_constraint_id = increment!(sc.constraints_count)
            # @info "Added new constraint with type only $new_constraint_id"
            sc.constrained_branches[constrained_branches, new_constraint_id] = constrained_vars
            sc.constrained_vars[constrained_vars, new_constraint_id] = constrained_branches
            sc.constrained_contexts[new_constraint_id] = context_id
        end
    else
        p = bp.skeleton
        input_vars = [
            (var_id, branch_id, first(get_connected_from(sc.branch_types, branch_id))) for
            (var_id, branch_id) in bp.input_vars
        ]
    end
    arg_types = [sc.types[v[3]] for v in input_vars]
    if isempty(arg_types)
        p_type = return_of_type(bp.request)
    else
        p_type = arrow(arg_types..., return_of_type(bp.request))
    end
    input_branches = Dict{UInt64,UInt64}(var_id => branch_id for (var_id, branch_id, _) in input_vars)
    new_block =
        ProgramBlock(p, p_type, bp.cost, [var_id for (var_id, _, _) in input_vars], bp.output_var[1], is_reverse)
    block_id = push!(sc.blocks, new_block)
    sc.block_root_branches[block_id] = bp.output_var[2]
    return [(block_id, input_branches, Dict{UInt64,UInt64}(bp.output_var[1] => bp.output_var[2]))], []
end

function create_wrapping_program_prototype(
    sc::SolutionContext,
    p,
    cost,
    input_var,
    input_branch,
    output_vars,
    var_id::UInt64,
    branch_id,
    input_type,
    context,
)
    var_ind = findfirst(v_info -> v_info[1] == var_id, output_vars)

    unknown_type_id = [t_id for (v_id, _, t_id) in output_vars if v_id == var_id][1]

    cg = sc.entry_grammars[(sc.branch_entries[input_branch], true)]

    candidate_functions = unifying_expressions(
        cg,
        Tp[],
        context,
        Hole(input_type, nothing, [], CombinedArgChecker([SimpleArgChecker(true, -1, false)]), nothing),
        Hole(input_type, nothing, [], CombinedArgChecker([SimpleArgChecker(true, -1, false)]), nothing),
        [],
    )

    wrapper, arg_types, new_context, wrap_cost =
        first(v for v in candidate_functions if v[1] == every_primitive["rev_fix_param"])

    unknown_type = sc.types[unknown_type_id]
    new_context = unify(new_context, unknown_type, arg_types[2])
    if isnothing(new_context)
        error("Can't unify $(unknown_type) with $(arg_types[2])")
    end
    new_context, fixer_type = apply_context(new_context, arg_types[3])

    unknown_entry = sc.entries[sc.branch_entries[branch_id]]
    custom_arg_checkers = _get_custom_arg_checkers(wrapper)
    filled_p, new_context = _fill_holes(p, new_context)

    wrapped_p = Apply(
        Apply(Apply(wrapper, filled_p), FreeVar(unknown_type, "r$var_ind", nothing)),
        Hole(fixer_type, nothing, [(wrapper, 3)], CombinedArgChecker([custom_arg_checkers[3]]), unknown_entry.values),
    )

    new_bp = BlockPrototype(
        wrapped_p,
        new_context,
        [RightTurn()],
        cost + wrap_cost + 0.001,
        number_of_free_parameters(filled_p),
        input_type,
        nothing,
        (input_var, input_branch),
        true,
    )
    return new_bp
end

collect_var_locations(p) = _collect_var_locations(p, Dict())

function _collect_var_locations(p::FreeVar, var_locations)
    if !haskey(var_locations, p.var_id)
        var_locations[p.var_id] = Set()
    end
    if !isnothing(p.location)
        push!(var_locations[p.var_id], p.location)
    end
    return var_locations
end

function _collect_var_locations(p::Apply, var_locations)
    var_locations = _collect_var_locations(p.f, var_locations)
    var_locations = _collect_var_locations(p.x, var_locations)
    return var_locations
end

function _collect_var_locations(p::Abstraction, var_locations)
    return _collect_var_locations(p.b, var_locations)
end

_collect_var_locations(p, var_locations) = var_locations

function create_reversed_block(
    sc::SolutionContext,
    p::Program,
    context,
    path,
    input_var::Tuple{UInt64,UInt64},
    cost,
    input_type,
)
    new_p, output_vars, either_var_ids, abductible_var_ids, either_branch_ids, abductible_branch_ids =
        try_get_reversed_values(sc, p, context, path, input_var[2], cost, true)
    if isempty(output_vars)
        throw(EnumerationException())
    end
    if isempty(either_var_ids) && isempty(abductible_var_ids)
        block = ReverseProgramBlock(new_p, cost, [input_var[1]], [v_id for (v_id, _, _) in output_vars])
        var_locations = collect_var_locations(new_p)
        for (var_id, locations) in var_locations
            sc.known_var_locations[var_id] = collect(locations)
        end
        block_id = push!(sc.blocks, block)
        sc.block_root_branches[block_id] = input_var[2]
        return [(
            block_id,
            Dict{UInt64,UInt64}(input_var[1] => input_var[2]),
            Dict{UInt64,UInt64}(v_id => b_id for (v_id, b_id, _) in output_vars),
        )],
        []
    else
        unfinished_prototypes = []
        for (var_id, branch_id) in
            Iterators.flatten([zip(either_var_ids, either_branch_ids), zip(abductible_var_ids, abductible_branch_ids)])
            push!(
                unfinished_prototypes,
                create_wrapping_program_prototype(
                    sc,
                    p,
                    cost,
                    input_var[1],
                    input_var[2],
                    output_vars,
                    var_id,
                    branch_id,
                    input_type,
                    context,
                ),
            )
        end
        drop_changes!(sc, sc.transaction_depth - 1)
        start_transaction!(sc, sc.transaction_depth + 1)
        return [], unfinished_prototypes
    end
end

function enumeration_iteration_finished_input(sc, bp::BlockPrototype)
    if bp.reverse
        # @info "Try get reversed for $bp"
        return create_reversed_block(
            sc,
            bp.skeleton,
            bp.context,
            bp.path,
            bp.output_var,
            bp.cost,
            return_of_type(bp.request),
        )
    else
        arg_types =
            [sc.types[first(get_connected_from(sc.branch_types, branch_id))] for (_, branch_id) in bp.input_vars]
        p_type = arrow(arg_types..., return_of_type(bp.request))
        new_block =
            ProgramBlock(bp.skeleton, p_type, bp.cost, [v_id for (v_id, _) in bp.input_vars], bp.output_var[1], false)
        new_block_id = push!(sc.blocks, new_block)
        sc.block_root_branches[new_block_id] = bp.output_var[2]
        input_branches = Dict{UInt64,UInt64}(var_id => branch_id for (var_id, branch_id) in bp.input_vars)
        target_output = Dict{UInt64,UInt64}(bp.output_var[1] => bp.output_var[2])
        return [(new_block_id, input_branches, target_output)], []
    end
end

function enumeration_iteration_finished(sc::SolutionContext, bp::BlockPrototype, br_id)
    if sc.branch_is_unknown[br_id]
        new_block_result, unfinished_prototypes = enumeration_iteration_finished_output(sc, bp)
    else
        new_block_result, unfinished_prototypes = enumeration_iteration_finished_input(sc, bp)
    end
    found_solutions = []
    for (new_block_id, input_branches, target_output) in new_block_result
        new_solution_paths = add_new_block(sc, new_block_id, input_branches, target_output)
        if sc.verbose
            @info "Got results $new_solution_paths"
        end
        append!(found_solutions, new_solution_paths)
    end

    return unfinished_prototypes, found_solutions
end

function enumeration_iteration(
    run_context,
    sc::SolutionContext,
    max_free_parameters::Int,
    guiding_model_channels,
    grammar,
    q,
    bp::BlockPrototype,
    br_id::UInt64,
    is_explained::Bool,
)
    sc.iterations_count += 1
    if (is_reversible(bp.skeleton) && !isa(sc.entries[sc.branch_entries[br_id]], AbductibleEntry)) || state_finished(bp)
        if sc.verbose
            @info "Checking finished $bp"
        end
        found_solutions = transaction(sc) do
            if is_block_loops(sc, bp)
                # @info "Block $bp creates a loop"
                throw(EnumerationException())
            end
            # enumeration_iteration_finished(sc, finalizer, g, bp, br_id)
            finish_results =
                @run_with_timeout run_context "program_timeout" enumeration_iteration_finished(sc, bp, br_id)
            if isnothing(finish_results)
                throw(EnumerationException())
            end
            unfinished_prototypes, found_solutions = finish_results
            for new_bp in unfinished_prototypes
                if sc.verbose
                    @info "Enqueing $new_bp"
                end
                q[new_bp] = new_bp.cost
            end
            enqueue_updates(sc, guiding_model_channels, grammar)
            if isempty(unfinished_prototypes)
                sc.total_number_of_enumerated_programs += 1
            end
            return found_solutions
        end
        if isnothing(found_solutions)
            found_solutions = []
        end
    else
        if sc.verbose
            @info "Checking unfinished $bp"
        end
        for new_bp in block_state_successors(sc, max_free_parameters, bp)
            if sc.verbose
                @info "Enqueing $new_bp"
            end
            q[new_bp] = new_bp.cost
        end
        found_solutions = []
    end
    update_branch_priority(sc, br_id, is_explained)
    return found_solutions
end

function solve_task(
    task,
    guiding_model_channels,
    grammar,
    timeout_container,
    timeout,
    program_timeout,
    type_weights,
    hyperparameters,
    maximum_solutions,
    verbose,
)
    run_context = Dict{String,Any}("timeout" => timeout, "program_timeout" => program_timeout)
    if !isnothing(timeout_container)
        run_context["timeout_container"] = timeout_container
    end

    enumeration_timeout = get_enumeration_timeout(timeout)

    sc = create_starting_context(task, type_weights, hyperparameters, verbose)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue{HitResult,Float64}()

    max_free_parameters = 10

    start_time = time()

    enqueue_updates(sc, guiding_model_channels, grammar)
    save_changes!(sc, 0)

    from_input = true

    while (!(enumeration_timed_out(enumeration_timeout))) &&
              (!isempty(sc.pq_input) || !isempty(sc.pq_output)) &&
              length(hits) < maximum_solutions
        from_input = !from_input
        pq = from_input ? sc.pq_input : sc.pq_output
        if isempty(pq)
            continue
        end
        (br_id, is_explained) = draw(pq)
        q = (is_explained ? sc.branch_queues_explained : sc.branch_queues_unknown)[br_id]
        bp = dequeue!(q)

        found_solutions = enumeration_iteration(
            run_context,
            sc,
            max_free_parameters,
            guiding_model_channels,
            grammar,
            q,
            bp,
            br_id,
            is_explained,
        )

        for solution_path in found_solutions
            solution, cost, trace_values = extract_solution(sc, solution_path)
            # @info "Got solution $solution with cost $cost"
            ll = task.log_likelihood_checker(task, solution)
            if !isnothing(ll) && !isinf(ll)
                dt = time() - start_time
                res = HitResult(join(show_program(solution, false)), -cost, ll, dt, trace_values)
                if haskey(hits, res)
                    # @warn "Duplicated solution $solution"
                else
                    hits[res] = -cost + ll
                end
                while length(hits) > maximum_solutions
                    dequeue!(hits)
                end
            end
        end
    end

    log_results(sc, hits)

    need_export = false
    if need_export
        export_solution_context(sc, task)
    end

    hits
end

function try_solve_task(
    task,
    guiding_model_channels,
    grammar,
    timeout_containers,
    timeout,
    program_timeout,
    type_weights,
    hyperparameters,
    maximum_solutions,
    verbose,
)
    @info "Solving task $(task.name)"
    timeout_container = myid() == 1 ? nothing : timeout_containers[myid()]
    traces = try
        solve_task(
            task,
            guiding_model_channels,
            grammar,
            timeout_container,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
    catch e
        bt = catch_backtrace()
        @error "Failed to solve task" exception = (e, bt)
        rethrow()
    end
    return Dict("task" => task, "traces" => traces)
end

function try_solve_tasks(
    worker_pool,
    tasks,
    guiding_model,
    grammar,
    timeout,
    program_timeout,
    type_weights,
    hyperparameters,
    maximum_solutions,
    verbose,
)
    timeout_containers = worker_pool.timeout_containers
    new_traces = pmap(
        worker_pool,
        tasks;
        retry_check = (s, e) -> isa(e, ProcessExitedException),
        retry_delays = zeros(5),
    ) do task
        # new_traces = map(tasks) do task
        @time try_solve_task(
            task,
            guiding_model,
            grammar,
            timeout_containers,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
    end
    filter!(tr -> !isempty(tr["traces"]), new_traces)
    @info "Got new solutions for $(length(new_traces))/$(length(tasks)) tasks"
    return new_traces
end

function try_solve_tasks(
    worker_pool,
    tasks,
    guiding_model_server::GuidingModelServer,
    grammar,
    timeout,
    program_timeout,
    type_weights,
    hyperparameters,
    maximum_solutions,
    verbose,
)
    timeout_containers = worker_pool.timeout_containers
    register_channel = guiding_model_server.worker_register_channel
    register_response_channel = guiding_model_server.worker_register_result_channel
    new_traces = pmap(
        worker_pool,
        tasks;
        retry_check = (s, e) -> isa(e, ProcessExitedException),
        retry_delays = zeros(5),
    ) do task
        # new_traces = map(tasks) do task
        put!(register_channel, myid())
        while true
            pid, request_channel, result_channel = take!(register_response_channel)
            if pid == myid()
                return @time try_solve_task(
                    task,
                    (request_channel, result_channel),
                    grammar,
                    timeout_containers,
                    timeout,
                    program_timeout,
                    type_weights,
                    hyperparameters,
                    maximum_solutions,
                    verbose,
                )
            else
                put!(register_response_channel, (pid, request_channel, result_channel))
                sleep(0.01)
            end
        end
    end
    filter!(tr -> !isempty(tr["traces"]), new_traces)
    @info "Got new solutions for $(length(new_traces))/$(length(tasks)) tasks"
    return new_traces
end

function config_options()
    s = ArgParseSettings()
    @add_arg_table! s begin
        "--workers", "-c"
        help = "number of workers to start"
        arg_type = Int
        default = 8

        "--iterations", "-i"
        help = "number of iterations"
        arg_type = Int
        default = 1

        "--domain", "-d"
        help = "domain"
        arg_type = String
        default = "arc"

        "--model", "-m"
        help = "guiding model type"
        arg_type = String
        default = "dummy"

        "--timeout", "-t"
        help = "timeout for solving a task"
        arg_type = Int
        default = 20

        "--program_timeout", "-p"
        help = "timeout for running a program"
        arg_type = Int
        default = 1

        "--maximum_solutions", "-s"
        help = "maximum number of solutions to find"
        arg_type = Int
        default = 10

        "--verbose", "-v"
        help = "verbose"
        action = :store_true

        "--resume", "-r"
        help = "resume from checkpoint path"
        arg_type = String
    end
    return s
end

function get_checkpoint_path(domain)
    checkpoint_dir = joinpath("checkpoints", domain, string(Dates.now()))
    if !isdir(checkpoint_dir)
        mkpath(checkpoint_dir)
    end
    return checkpoint_dir
end

using Serialization

function save_checkpoint(parsed_args, iteration, traces, grammar, guiding_model)
    path = get_checkpoint_path(parsed_args[:domain])
    Serialization.serialize(joinpath(path, "args.jls"), (parsed_args, iteration))
    Serialization.serialize(joinpath(path, "traces.jls"), traces)
    Serialization.serialize(joinpath(path, "grammar.jls"), grammar)
    Serialization.serialize(joinpath(path, "guiding_model.jls"), guiding_model)
    @info "Saved checkpoint for iteration $(iteration-1) to $path"
end

function load_checkpoint(path)
    args, iteration = Serialization.deserialize(joinpath(path, "args.jls"))
    loaded_traces = Serialization.deserialize(joinpath(path, "traces.jls"))
    traces = Dict{UInt64,Any}()
    for (grammar, gr_traces) in values(loaded_traces)
        grammar_hash = hash(grammar)
        traces[grammar_hash] = (grammar, gr_traces)
    end
    grammar = Serialization.deserialize(joinpath(path, "grammar.jls"))
    guiding_model = Serialization.deserialize(joinpath(path, "guiding_model.jls"))
    return args, iteration, traces, grammar, guiding_model
end

function log_traces(traces)
    @info "Task solutions"
    for (task_name, task_traces) in traces
        @info task_name
        for (hit, cost) in task_traces
            @info "$cost\t$(hit.hit_program)"
        end
        @info ""
    end
end

function log_grammar(iteration, grammar)
    @info "Grammar after iteration $iteration"
    for p in grammar
        @info "$(p)\t$(p.t)"
    end
    @info ""
end

function main(; kwargs...)
    @info "Starting enumeration service"
    parsed_args = parse_args(ARGS, config_options(); as_symbols = true)
    merge!(parsed_args, kwargs)

    if !isnothing(parsed_args[:resume])
        (restored_args, i, traces, grammar, guiding_model) = load_checkpoint(parsed_args[:resume])
        parsed_args = merge(restored_args, parsed_args)
    else
        grammar = get_starting_grammar()
        guiding_model = get_guiding_model(parsed_args[:model])
        traces = Dict{UInt64,Any}()
        i = 1
    end

    guiding_model_server = GuidingModelServer(guiding_model)
    start_server(guiding_model_server)

    grammar_hash = hash(grammar)

    @info "Parsed arguments $parsed_args"

    tasks = get_domain_tasks(parsed_args[:domain])

    # tasks = tasks[begin:10]

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
    hyperparameters = Dict{String,Any}("path_cost_power" => 1.0, "complexity_power" => 1.0, "block_cost_power" => 1.0)

    try
        while i <= parsed_args[:iterations]
            i += 1

            new_traces = try_solve_tasks(
                worker_pool,
                tasks,
                guiding_model_server,
                grammar,
                parsed_args[:timeout],
                parsed_args[:program_timeout],
                type_weights,
                hyperparameters,
                parsed_args[:maximum_solutions],
                parsed_args[:verbose],
            )
            if !haskey(traces, grammar_hash)
                traces[grammar_hash] = (grammar, Dict{String,Any}())
            end
            cur_traces = traces[grammar_hash][2]
            for task_traces in new_traces
                task_name = task_traces["task"].name
                if !haskey(cur_traces, task_name)
                    cur_traces[task_name] = PriorityQueue{HitResult,Float64}()
                end
                for (trace, cost) in task_traces["traces"]
                    cur_traces[task_name][trace] = cost

                    while length(cur_traces[task_name]) > parsed_args[:maximum_solutions]
                        dequeue!(cur_traces[task_name])
                    end
                end
            end

            cur_traces, grammar = compress_traces(cur_traces, grammar)
            grammar_hash = hash(grammar)
            traces[grammar_hash] = (grammar, cur_traces)

            @info "Got total solutions for $(length(cur_traces))/$(length(tasks)) tasks"
            log_traces(cur_traces)
            log_grammar(i, grammar)

            guiding_model = update_guiding_model(guiding_model, traces)
            save_checkpoint(parsed_args, i, traces, grammar, guiding_model)
        end
    finally
        stop(worker_pool)
        stop_server(guiding_model_server)
    end
end
