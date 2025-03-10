
function build_manual_traces(tasks, guiding_model_server, grammar, worker_pool, traces)
    if isnothing(traces)
        solutions = JSON.parsefile(joinpath(@__DIR__, "..", "data", "manual_solutions.json"))
        task_solutions = [(task, solutions[task.name]) for task in tasks if haskey(solutions, task.name)]
        sols = [(task, join(sol, " ")) for (task, sols) in task_solutions for sol in sols]
    else
        sols = [(task, hit.hit_program) for task in tasks for hit in keys(traces[task.name])]
    end
    register_channel = guiding_model_server.worker_register_channel
    register_response_channel = guiding_model_server.worker_register_result_channel
    new_traces = pmap(
        worker_pool,
        sols;
        retry_check = (s, e) -> isa(e, ProcessExitedException),
        retry_delays = zeros(5),
    ) do (task, sol)
        task_name = "$(task.name)_$(randstring(6))"
        put!(register_channel, task_name)
        while true
            reg_task_name, request_channel, result_channel, end_tasks_channel = take!(register_response_channel)
            if reg_task_name == task_name
                @info "Building manual trace for $(task.name)"
                hit, cost = @time build_manual_trace(
                    task,
                    task_name,
                    sol,
                    (request_channel, result_channel, end_tasks_channel),
                    grammar,
                )
                return (task.name, hit, cost)
            else
                put!(register_response_channel, (reg_task_name, request_channel, result_channel, end_tasks_channel))
                sleep(0.01)
            end
        end
    end

    traces = Dict{String,Any}()
    for (task_name, hit, cost) in new_traces
        if !haskey(traces, task_name)
            traces[task_name] = PriorityQueue{HitResult,Float64}()
        end
        traces[task_name][hit] = cost
    end
    return traces
end

function build_manual_traces(tasks, guiding_model_server::PythonGuidingModelServer, grammar, worker_pool, traces)
    if isnothing(traces)
        solutions = JSON.parsefile(joinpath(@__DIR__, "..", "data", "manual_solutions.json"))
        task_solutions = [(task, solutions[task.name]) for task in tasks if haskey(solutions, task.name)]
        sols = [(task, join(sol, " ")) for (task, sols) in task_solutions for sol in sols]
    else
        tasks_to_check = [t for t in tasks if haskey(traces, t.name)]
        sols = [(t, hit.hit_program) for t in tasks_to_check for hit in keys(traces[t.name])]
    end
    redis_db = guiding_model_server.model.redis_db
    new_traces = pmap(
        worker_pool,
        sols;
        retry_check = (s, e) -> isa(e, ProcessExitedException),
        retry_delays = zeros(5),
    ) do (task, sol)
        task_name = "$(task.name)_$(randstring(6))"
        conn = get_redis_connection(redis_db)
        @info "Building manual trace for $(task.name)"
        hit, cost = @time build_manual_trace(task, task_name, sol, conn, grammar)
        return (task.name, hit, cost)
    end

    traces = Dict{String,Any}()
    for (task_name, hit, cost) in new_traces
        if !haskey(traces, task_name)
            traces[task_name] = PriorityQueue{HitResult,Float64}()
        end
        traces[task_name][hit] = cost
    end
    return traces
end

_used_vars(p::FreeVar) = [p.var_id]
_used_vars(p::Apply) = vcat(_used_vars(p.f), _used_vars(p.x))
_used_vars(p::Abstraction) = _used_vars(p.b)
_used_vars(::Any) = []

function _extract_blocks(task, target_program, verbose = false)
    vars_mapping = Dict{Any,UInt64}()
    vars_from_input = Set{Any}()
    vars_from_rev = Set{Any}()
    for (arg, _) in task.task_type.arguments
        vars_mapping[arg] = length(vars_mapping) + 1
        push!(vars_from_input, arg)
        push!(vars_from_rev, arg)
    end
    vars_mapping["out"] = length(vars_mapping) + 1
    copied_vars = 0
    in_blocks = Dict()
    out_blocks = Dict()
    p = target_program
    while true
        if verbose
            @info p
            @info vars_mapping
            @info in_blocks
            @info out_blocks
            @info vars_from_input
            @info vars_from_rev
            @info copied_vars
        end
        if p isa LetClause
            vars = _used_vars(p.v)
            if verbose
                @info p.v
                @info vars
            end
            in_vars = UInt64[]
            for v in vars
                if !haskey(vars_mapping, v)
                    vars_mapping[v] = length(vars_mapping) + copied_vars + 1
                    push!(in_vars, vars_mapping[v])
                elseif v in vars_from_rev && !isa(p.v, FreeVar)
                    copied_vars += 1
                    out_var = length(vars_mapping) + copied_vars
                    push!(in_vars, out_var)
                    copy_block =
                        ProgramBlock(FreeVar(t0, vars_mapping[v], nothing), t0, 0.0, [vars_mapping[v]], out_var, false)
                    if v in vars_from_input
                        if !haskey(in_blocks, vars_mapping[v])
                            in_blocks[vars_mapping[v]] = []
                        end
                        push!(in_blocks[vars_mapping[v]], copy_block)
                    else
                        if !haskey(out_blocks, out_var)
                            out_blocks[out_var] = []
                        end
                        push!(out_blocks[out_var], copy_block)
                    end
                else
                    push!(in_vars, vars_mapping[v])
                end
                if v in vars_from_input
                    push!(vars_from_input, p.var_id)
                end
            end
            if !haskey(vars_mapping, p.var_id)
                vars_mapping[p.var_id] = length(vars_mapping) + copied_vars + 1
            end
            bl = ProgramBlock(p.v, t0, 0.0, in_vars, vars_mapping[p.var_id], is_reversible(p.v))
            if isa(p.v, FreeVar) && p.v.var_id in vars_from_input
                if !haskey(in_blocks, in_vars[1])
                    in_blocks[in_vars[1]] = []
                end
                push!(in_blocks[in_vars[1]], bl)
            else
                if !haskey(out_blocks, vars_mapping[p.var_id])
                    out_blocks[vars_mapping[p.var_id]] = []
                end
                push!(out_blocks[vars_mapping[p.var_id]], bl)
            end
            p = p.b
        elseif p isa LetRevClause
            if !haskey(vars_mapping, p.inp_var_id)
                vars_mapping[p.inp_var_id] = length(vars_mapping) + copied_vars + 1
            end
            for v in p.var_ids
                if !haskey(vars_mapping, v)
                    vars_mapping[v] = length(vars_mapping) + copied_vars + 1
                end
                push!(vars_from_rev, v)
                if p.inp_var_id in vars_from_input
                    push!(vars_from_input, v)
                end
            end

            bl = ReverseProgramBlock(p.v, t0, 0.0, [vars_mapping[p.inp_var_id]], [vars_mapping[v] for v in p.var_ids])
            if !haskey(in_blocks, vars_mapping[p.inp_var_id])
                in_blocks[vars_mapping[p.inp_var_id]] = []
            end
            push!(in_blocks[vars_mapping[p.inp_var_id]], bl)
            p = p.b
        elseif p isa FreeVar
            in_var = vars_mapping[p.var_id]
            bl = ProgramBlock(FreeVar(t0, in_var, nothing), t0, 0.0, [in_var], vars_mapping["out"], false)
            if !haskey(in_blocks, in_var)
                in_blocks[in_var] = []
            end
            push!(in_blocks[in_var], bl)
            break
        else
            vars = _used_vars(p)
            in_vars = []
            for v in unique(vars)
                if !haskey(vars_mapping, v)
                    vars_mapping[v] = length(vars_mapping) + copied_vars + 1
                    push!(in_vars, vars_mapping[v])
                elseif v in vars_from_rev
                    copied_vars += 1
                    out_var = length(vars_mapping) + copied_vars
                    push!(in_vars, out_var)
                    copy_block =
                        ProgramBlock(FreeVar(t0, vars_mapping[v], nothing), t0, 0.0, [vars_mapping[v]], out_var, false)
                    if v in vars_from_input
                        if !haskey(in_blocks, vars_mapping[v])
                            in_blocks[vars_mapping[v]] = []
                        end
                        push!(in_blocks[vars_mapping[v]], copy_block)
                    else
                        if !haskey(out_blocks, out_var)
                            out_blocks[out_var] = []
                        end
                        push!(out_blocks[out_var], copy_block)
                    end
                else
                    push!(in_vars, vars_mapping[v])
                end
            end
            bl = ProgramBlock(p, t0, 0.0, in_vars, vars_mapping["out"], is_reversible(p))
            if !haskey(out_blocks, vars_mapping["out"])
                out_blocks[vars_mapping["out"]] = []
            end
            push!(out_blocks[vars_mapping["out"]], bl)
            break
        end
    end
    return in_blocks, out_blocks, vars_mapping
end

is_on_path(prot::Hole, p, vars_mapping, final = false) = true
is_on_path(prot::Apply, p::Apply, vars_mapping, final = false) =
    is_on_path(prot.f, p.f, vars_mapping, final) && is_on_path(prot.x, p.x, vars_mapping, final)
is_on_path(prot::Abstraction, p::Abstraction, vars_mapping, final = false) =
    is_on_path(prot.b, p.b, vars_mapping, final)
is_on_path(prot, p, vars_mapping, final = false) = prot == p

function is_on_path(prot::FreeVar, p::FreeVar, vars_mapping, final = false)
    if !haskey(vars_mapping, p.var_id)
        if isnothing(prot.var_id)
            vars_mapping[p.var_id] = "r$(length(vars_mapping) + 1)"
        elseif final
            vars_mapping[p.var_id] = prot.var_id
        else
            return false
        end
    else
        if isnothing(prot.var_id)
            return false
        end
        if vars_mapping[p.var_id] != prot.var_id
            return false
        end
    end
    true
end

function is_var_on_path(bp::BlockPrototype, bl::ProgramBlock, vars_mapping, verbose = false)
    if !isa(bp.skeleton, FreeVar)
        return false
    end
    if !isa(bl.p, FreeVar)
        return false
    end
    if verbose
        @info "Check on path"
        @info bl.output_var
        @info vars_mapping[bl.output_var]
        @info bp.output_var
    end

    if !haskey(vars_mapping, bl.output_var) || vars_mapping[bl.output_var] != bp.output_var[1]
        return false
    end
    if haskey(vars_mapping, bl.input_vars[1])
        bp.skeleton.var_id == vars_mapping[bl.input_vars[1]]
    else
        true
    end
end

function is_bp_on_path(bp::BlockPrototype, bl::ProgramBlock, vars_mapping, verbose = false)
    if isa(bl.p, FreeVar)
        is_var_on_path(bp, bl, vars_mapping, verbose)
    else
        is_on_path(bp.skeleton, bl.p, Dict())
    end
end

function is_bp_on_path(bp::BlockPrototype, bl::ReverseProgramBlock, vars_mapping, verbose = false)
    block_main_func, block_main_func_args = application_parse(bl.p)
    if verbose
        @info "block_main_func: $block_main_func"
        @info "block_main_func_args: $block_main_func_args"
    end
    if block_main_func == every_primitive["rev_fix_param"]
        wrapped_func = block_main_func_args[1]
    else
        wrapped_func = nothing
    end
    is_on_path(bp.skeleton, bl.p, Dict()) || (wrapped_func !== nothing && is_on_path(bp.skeleton, wrapped_func, Dict()))
end

function enumeration_iteration_finished_traced(
    sc::SolutionContext,
    bp::BlockPrototype,
    br_id,
    target_blocks,
    vars_mapping,
    rev_vars_mapping,
)
    if bp.reverse
        new_block_result, unfinished_prototypes = create_reversed_block(
            sc,
            bp.skeleton,
            bp.context,
            bp.path,
            bp.output_var,
            bp.cost,
            return_of_type(bp.request),
        )
    else
        new_block_result = enumeration_iteration_finished_output(sc, bp)
        unfinished_prototypes = []
    end
    found_solutions = []
    filtered_target_blocks = filter(bl -> is_bp_on_path(bp, bl, vars_mapping, sc.verbose), target_blocks)
    if isempty(filtered_target_blocks)
        if sc.verbose
            @info "No target blocks for $bp"
            @info "New block result $new_block_result"
            @info "Target blocks $target_blocks"
            @info "Vars mapping $vars_mapping"
        end
        return unfinished_prototypes, found_solutions
    end
    target_block = filtered_target_blocks[1]

    for (new_block_id, input_branches, target_output) in new_block_result
        new_block = sc.blocks[new_block_id]
        if isa(new_block, ProgramBlock) || is_on_path(new_block.p, target_block.p, Dict(), true)
            if sc.verbose
                @info "Got new block $new_block"
                @info "Target block $target_block"
            end

            if isa(new_block, ProgramBlock)
                for (original_var, new_var) in zip(target_block.input_vars, new_block.input_vars)
                    if !haskey(vars_mapping, original_var)
                        vars_mapping[original_var] = new_var
                        rev_vars_mapping[new_var] = original_var
                    end
                end
            else
                for (original_var, new_var) in zip(target_block.output_vars, new_block.output_vars)
                    if !haskey(vars_mapping, original_var)
                        vars_mapping[original_var] = new_var
                        rev_vars_mapping[new_var] = original_var
                    end
                end
            end

            if sc.verbose
                @info "Updated vars mapping $vars_mapping"
                @info "Updated rev vars mapping $rev_vars_mapping"
            end

            new_solution_paths = add_new_block(sc, new_block_id, input_branches, target_output)
            if sc.verbose
                @info "Got results $new_solution_paths"
            end
            append!(found_solutions, new_solution_paths)
        else
            if sc.verbose
                @info "Not on path $new_block"
                # @info "Target blocks $target_blocks"
            end
        end
    end

    return unfinished_prototypes, found_solutions
end

function enumeration_iteration_traced(
    run_context,
    sc::SolutionContext,
    max_free_parameters::Int,
    guiding_model_channels,
    grammar,
    bp::BlockPrototype,
    br_id::UInt64,
    is_explained::Bool,
    target_blocks,
    vars_mapping,
    rev_vars_mapping,
)
    sc.iterations_count += 1
    q = (is_explained ? sc.branch_queues_explained : sc.branch_queues_unknown)[br_id]
    if (is_reversible(bp.skeleton) && !isa(sc.entries[sc.branch_entries[br_id]], AbductibleEntry)) || state_finished(bp)
        if sc.verbose
            @info "Checking finished $bp"
            @info "Target blocks $target_blocks"
        end
        found_solutions = transaction(sc) do
            if is_block_loops(sc, bp)
                @info "Block $bp creates a loop"
                throw(EnumerationException())
            end
            # enumeration_iteration_finished(sc, finalizer, g, bp, br_id)
            finish_results = @run_with_timeout run_context "program_timeout" enumeration_iteration_finished_traced(
                sc,
                bp,
                br_id,
                target_blocks,
                vars_mapping,
                rev_vars_mapping,
            )
            if isnothing(finish_results)
                throw(EnumerationException())
            end
            unfinished_prototypes, found_solutions = finish_results
            for new_bp in unfinished_prototypes
                if any(is_bp_on_path(new_bp, bl, vars_mapping) for bl in target_blocks)
                    if sc.verbose
                        @info "On path $new_bp"
                        @info "Enqueing $new_bp"
                    end
                    q[new_bp] = new_bp.cost
                else
                    if sc.verbose
                        @info "Not on path $new_bp"
                    end
                end
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
            @info "Target blocks $target_blocks"
        end
        for new_bp in block_state_successors(sc, max_free_parameters, bp)
            if any(is_bp_on_path(new_bp, bl, vars_mapping) for bl in target_blocks)
                if sc.verbose
                    @info "On path $new_bp"
                    @info "Enqueing $new_bp"
                end
                q[new_bp] = new_bp.cost
            else
                if sc.verbose
                    @info "Not on path $new_bp"
                end
            end
        end
        found_solutions = []
    end
    update_branch_priority(sc, br_id, is_explained)
    return found_solutions
end

function build_manual_trace(
    task::Task,
    task_name,
    target_solution,
    guiding_model_channels,
    grammar,
    verbose_test = false,
)
    max_free_parameters = 10
    run_context = Dict{String,Any}("program_timeout" => 1, "timeout" => 40)

    type_weights = Dict(
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
        "either" => 0.0,
    )

    hyperparameters = Dict("path_cost_power" => 1.0, "complexity_power" => 1.0, "block_cost_power" => 1.0)

    try
        target_program = parse_program(target_solution)

        ll = task.log_likelihood_checker(task, target_program)
        if isnothing(ll) || isinf(ll)
            error("Invalid target program $target_program for task $task")
        end

        in_blocks, out_blocks, vars_mapping = _extract_blocks(task, target_program, verbose_test)

        start_time = time()

        # verbose_test = true
        sc = create_starting_context(task, task_name, type_weights, hyperparameters, verbose_test, true)

        enqueue_updates(sc, guiding_model_channels, grammar)

        if verbose_test
            @info in_blocks
            @info out_blocks
        end
        save_changes!(sc, 0)

        inner_mapping = Dict{UInt64,UInt64}()
        rev_inner_mapping = Dict{UInt64,UInt64}()
        for (arg, _) in task.task_type.arguments
            for (v, a) in sc.input_keys
                if a == arg
                    inner_mapping[v] = vars_mapping[arg]
                    rev_inner_mapping[vars_mapping[arg]] = v
                end
            end
        end
        inner_mapping[vars_mapping["out"]] = first(get_connected_from(sc.branch_vars, sc.target_branch_id))
        rev_inner_mapping[first(get_connected_from(sc.branch_vars, sc.target_branch_id))] = vars_mapping["out"]
        if verbose_test
            @info inner_mapping
        end

        from_input = true

        while (!isempty(sc.pq_input) || !isempty(sc.pq_output) || !isempty(sc.waiting_branches))
            receive_grammar_weights(sc, guiding_model_channels, grammar)
            from_input = !from_input
            pq = from_input ? sc.pq_input : sc.pq_output
            if isempty(pq)
                sleep(0.0001)
                continue
            end
            (br_id, is_explained) = draw(pq)
            q = (is_explained ? sc.branch_queues_explained : sc.branch_queues_unknown)[br_id]
            bp = dequeue!(q)

            target_blocks_group = from_input ? in_blocks : out_blocks
            var_id = first(get_connected_from(sc.branch_vars, br_id))
            if !haskey(rev_inner_mapping, var_id) || !haskey(target_blocks_group, rev_inner_mapping[var_id])
                update_branch_priority(sc, br_id, is_explained)
                continue
            end
            target_blocks = target_blocks_group[rev_inner_mapping[var_id]]

            found_solutions = enumeration_iteration_traced(
                run_context,
                sc,
                max_free_parameters,
                guiding_model_channels,
                grammar,
                bp,
                br_id,
                is_explained,
                target_blocks,
                inner_mapping,
                rev_inner_mapping,
            )

            for solution_path in found_solutions
                solution, cost, trace_values = extract_solution(sc, solution_path)
                # @info "Got solution $solution with cost $cost"
                ll = task.log_likelihood_checker(task, solution)
                if !isnothing(ll) && !isinf(ll)
                    dt = time() - start_time
                    res = HitResult(join(show_program(solution, false)), -cost, ll, dt, trace_values)
                    return res, -cost + ll
                end
            end
        end
    catch e
        bt = catch_backtrace()
        @error "Error in build_manual_trace" exception = (e, bt)
        rethrow()
    finally
        mark_task_finished(guiding_model_channels, task_name)
    end
    @info [sc.blocks[UInt64(i)] for i in 1:length(sc.blocks)]
    @error "Could not find a trace for $(task.name) with target solution $target_solution"
    error("Could not find a trace for $(task.name) with target solution $target_solution")
end
