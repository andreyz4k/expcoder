
using JSON

using solver:
    parse_program,
    ProgramBlock,
    ReverseProgramBlock,
    LetClause,
    LetRevClause,
    t0,
    is_reversible,
    FreeVar,
    Apply,
    Abstraction,
    Hole,
    Primitive,
    Invented,
    create_starting_context,
    enqueue_updates,
    save_changes!,
    enumeration_iteration,
    state_finished,
    get_connected_from,
    get_connected_to,
    show_program,
    HitResult,
    BlockPrototype,
    application_parse,
    every_primitive,
    create_arc_task,
    get_guiding_model,
    supervised_task_checker,
    parse_type,
    Task,
    extract_solution,
    build_manual_trace,
    set_current_grammar!,
    contextual_grammar_cache,
    GuidingModelServer,
    start_server,
    stop_server,
    receive_grammar_weights,
    get_redis_connection,
    PythonGuidingModelServer,
    mark_task_finished,
    enumeration_iteration_insert_copy_block,
    enumeration_iteration_insert_block,
    is_var_on_path,
    is_on_path,
    _get_free_vars

using DataStructures

@testset "Reachable solutions" begin
    sample_library = Any[
        "map",
        "map_set",
        "map_grid",
        "map2",
        "map2_grid",
        "unfold",
        "range",
        "index",
        "index2",
        "fold",
        "fold_set",
        "fold_h",
        "fold_v",
        "length",
        "height",
        "width",
        "if",
        "+",
        "-",
        "empty",
        "empty_set",
        "cons",
        "car",
        "cdr",
        "empty?",
        "*",
        "mod",
        "gt?",
        "eq?",
        "is-prime",
        "is-square",
        "repeat",
        "repeat_grid",
        "concat",
        "rows_to_grid",
        "columns_to_grid",
        "rows",
        "columns",
        "0",
        "1",
        "rev_select",
        "rev_select_set",
        "rev_select_grid",
        "rev_list_elements",
        "rev_grid_elements",
        "zip2",
        "zip_grid2",
        "tuple2",
        "tuple2_first",
        "tuple2_second",
        "reverse",
        "rev_fold",
        "rev_fold_set",
        "list_to_set",
        "adjoin",
        "rev_groupby",
        "rev_greedy_cluster",
        "not",
        "and",
        "or",
        "all",
        "any",
        "all_set",
        "any_set",
        "abs",
        "rev_fix_param",
        "max_int",
        "min_int",
        "collect",
    ]

    sample_library2 = Any[
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

    function build_grammar(library)
        return [parse_program(p) for p in library]
    end

    function create_task(task_dict)
        return Task(
            task_dict["name"],
            parse_type(task_dict["request"]),
            supervised_task_checker,
            [ex["inputs"] for ex in task_dict["examples"]],
            [ex["output"] for ex in task_dict["examples"]],
            [ex["inputs"] for ex in task_dict["test_examples"]],
            [ex["output"] for ex in task_dict["test_examples"]],
        )
    end

    function _create_arc_task(filename, dir = "ARC/data/training/")
        fname = "data/" * dir * filename
        tp = parse_type("inp0:grid(color) -> grid(color)")
        return create_arc_task(fname, tp)
    end

    function _extract_blocks(task, target_program, verbose = false)
        vars_mapping = Dict{Any,UInt64}()
        vars_from_input = Set{Any}()
        for (arg, _) in task.task_type.arguments
            vars_mapping[arg] = length(vars_mapping) + 1
            push!(vars_from_input, arg)
        end
        vars_mapping["out"] = length(vars_mapping) + 1
        copied_vars = 0
        blocks = []
        p = target_program
        while true
            if verbose
                @info p
                @info vars_mapping
                @info blocks
                @info vars_from_input
                @info copied_vars
            end
            if p isa LetClause
                vars = _get_free_vars(p.v)
                if verbose
                    @info p.v
                    @info vars
                end
                in_vars = []
                for v in keys(vars)
                    if !haskey(vars_mapping, v)
                        vars_mapping[v] = length(vars_mapping) + copied_vars + 1
                        push!(in_vars, vars_mapping[v])
                    elseif v in vars_from_input && !isa(p.v, FreeVar)
                        copied_vars += 1
                        push!(in_vars, length(vars_mapping) + copied_vars)
                        copy_block = ProgramBlock(
                            FreeVar(t0, t0, vars_mapping[v], nothing),
                            t0,
                            0.0,
                            [vars_mapping[v]],
                            length(vars_mapping) + copied_vars,
                            false,
                        )
                        push!(blocks, copy_block)
                    else
                        push!(in_vars, vars_mapping[v])
                    end
                end
                if !haskey(vars_mapping, p.var_id)
                    vars_mapping[p.var_id] = length(vars_mapping) + copied_vars + 1
                end
                bl = ProgramBlock(p.v, t0, 0.0, in_vars, vars_mapping[p.var_id], is_reversible(p.v))
                push!(blocks, bl)
                p = p.b
            elseif p isa LetRevClause
                if !haskey(vars_mapping, p.inp_var_id)
                    vars_mapping[p.inp_var_id] = length(vars_mapping) + copied_vars + 1
                end
                for v in p.var_ids
                    if !haskey(vars_mapping, v)
                        vars_mapping[v] = length(vars_mapping) + copied_vars + 1
                    end
                    if p.inp_var_id in vars_from_input
                        push!(vars_from_input, v)
                    end
                end

                bl = ReverseProgramBlock(
                    p.v,
                    t0,
                    0.0,
                    [vars_mapping[p.inp_var_id]],
                    [vars_mapping[v] for v in p.var_ids],
                )
                push!(blocks, bl)
                p = p.b
            elseif p isa FreeVar
                in_var = vars_mapping[p.var_id]
                bl = ProgramBlock(FreeVar(t0, t0, in_var, nothing), t0, 0.0, [in_var], vars_mapping["out"], false)
                push!(blocks, bl)
                break
            else
                vars = _get_free_vars(p)
                in_vars = []
                for v in keys(vars)
                    if !haskey(vars_mapping, v)
                        vars_mapping[v] = length(vars_mapping) + copied_vars + 1
                        push!(in_vars, vars_mapping[v])
                    elseif v in vars_from_input
                        copied_vars += 1
                        push!(in_vars, length(vars_mapping) + copied_vars)
                        copy_block = ProgramBlock(
                            FreeVar(t0, t0, vars_mapping[v], nothing),
                            t0,
                            0.0,
                            [vars_mapping[v]],
                            length(vars_mapping) + copied_vars,
                            false,
                        )
                        push!(blocks, copy_block)
                    else
                        push!(in_vars, vars_mapping[v])
                    end
                end
                bl = ProgramBlock(p, t0, 0.0, in_vars, vars_mapping["out"], is_reversible(p))
                push!(blocks, bl)
                break
            end
        end
        return blocks, vars_mapping
    end

    function _block_can_be_next(bl::ProgramBlock, vars_mapping)
        if bl.p isa FreeVar
            return haskey(vars_mapping, bl.output_var) && haskey(vars_mapping, bl.input_vars[1])
        end
        return haskey(vars_mapping, bl.output_var)
    end

    function _block_can_be_next(bl::ReverseProgramBlock, vars_mapping)
        return haskey(vars_mapping, bl.input_vars[1])
    end

    function _get_entries(sc, vars_mapping, branches)
        result = Dict()
        for (original_var, mapped_var) in vars_mapping
            if !haskey(branches, mapped_var)
                continue
            end
            branch_id = branches[mapped_var]
            entry = sc.entries[sc.branch_entries[branch_id]]
            result[original_var] = entry
        end
        return result
    end

    function _fetch_branches_children(sc, branches)
        result = Dict()
        for (var_id, branch_id) in branches
            while !isempty(get_connected_from(sc.branch_children, branch_id))
                branch_id = first(get_connected_from(sc.branch_children, branch_id))
            end
            result[var_id] = branch_id
        end
        return result
    end

    function _simulate_copy_block_search(
        sc,
        task,
        bl::ProgramBlock,
        rem_blocks,
        branches,
        branches_history,
        vars_mapping,
        guiding_model_server,
        guiding_model_channels,
        grammar,
        run_context,
        mfp,
        verbose,
    )
        if verbose
            @info "Simulating block search for $bl"
        end

        out_branch_id = branches[vars_mapping[bl.output_var]]

        not_on_path = Set()
        @test !isempty(sc.copies_queue)
        while !isempty(sc.copies_queue)
            block_info, p = peek(sc.copies_queue)
            block_info = dequeue!(sc.copies_queue)
            if verbose
                @info block_info
            end

            block, _, _ = block_info

            if is_var_on_path(block, bl, vars_mapping, verbose)
                if verbose
                    @info "on path"
                end

                found_solutions =
                    enumeration_iteration_insert_copy_block(sc, block_info, guiding_model_channels, grammar)

                if verbose
                    @info "found end"
                    @info "Out branch id $out_branch_id"
                end

                for (block_info_, p_) in not_on_path
                    sc.copies_queue[block_info_] = p_
                end

                in_blocks = get_connected_from(sc.branch_incoming_blocks, out_branch_id)
                if verbose
                    @info "in_blocks: $in_blocks"
                end
                if isempty(in_blocks)
                    children = get_connected_from(sc.branch_children, out_branch_id)
                    if verbose
                        @info "children: $children"
                        @info sc.branch_children
                    end
                    if isempty(children)
                        if verbose
                            @info "Can't add block"
                        end
                        return Set(), Set([(_get_entries(sc, vars_mapping, branches), bl)])
                    end
                    @test length(children) == 1
                    child_id = first(children)
                    in_blocks = get_connected_from(sc.branch_incoming_blocks, child_id)
                end
                @test !isempty(in_blocks)
                if verbose
                    @info "in_blocks: $in_blocks"
                end
                created_block_id = first(values(in_blocks))
                created_block = sc.blocks[created_block_id]
                if verbose
                    @info "created_block: $created_block"
                end

                updated_branches = copy(branches)
                created_block_copy_id = first(keys(in_blocks))
                in_branches = keys(get_connected_to(sc.branch_outgoing_blocks, created_block_copy_id))
                for in_branch in in_branches
                    updated_branches[sc.branch_vars[in_branch]] = in_branch
                end
                out_branches = keys(get_connected_to(sc.branch_incoming_blocks, created_block_copy_id))
                for out_branch in out_branches
                    updated_branches[sc.branch_vars[out_branch]] = out_branch
                end
                updated_branches = _fetch_branches_children(sc, updated_branches)
                if verbose
                    @info "updated_branches: $updated_branches"
                end

                updated_vars_mapping = copy(vars_mapping)
                for (original_var, new_var) in zip(bl.input_vars, created_block.input_vars)
                    if !haskey(updated_vars_mapping, original_var)
                        updated_vars_mapping[original_var] = new_var
                    end
                end
                if verbose
                    @info "updated_vars_mapping: $updated_vars_mapping"
                end
                updated_history = vcat(branches_history, [(branches, bl)])

                if isempty(rem_blocks)
                    @test !isempty(found_solutions)
                    for solution_path in found_solutions
                        solution, cost = extract_solution(sc, solution_path)
                        ll = task.log_likelihood_checker(task, solution)
                        @test !isnothing(ll)
                        @test !isinf(ll)
                    end
                end

                return _check_reachable(
                    sc,
                    task,
                    rem_blocks,
                    updated_vars_mapping,
                    updated_branches,
                    updated_history,
                    guiding_model_server,
                    guiding_model_channels,
                    grammar,
                    run_context,
                    mfp,
                    verbose,
                )
            else
                push!(not_on_path, (block_info, p))
                if verbose
                    @info "not on path"
                end
            end
        end
        if verbose
            @info "Failed to find block $bl"
        end
        return Set(), Set([(_get_entries(sc, vars_mapping, branches), bl)])
    end

    function _simulate_block_search(
        sc,
        task,
        bl::ProgramBlock,
        rem_blocks,
        branches,
        branches_history,
        vars_mapping,
        guiding_model_server,
        guiding_model_channels,
        grammar,
        run_context,
        mfp,
        verbose,
    )
        if bl.p isa FreeVar
            return _simulate_copy_block_search(
                sc,
                task,
                bl,
                rem_blocks,
                branches,
                branches_history,
                vars_mapping,
                guiding_model_server,
                guiding_model_channels,
                grammar,
                run_context,
                mfp,
                verbose,
            )
        end

        if verbose
            @info "Simulating block search for $bl"
        end

        out_branch_id = branches[vars_mapping[bl.output_var]]
        # while !isempty(get_connected_from(sc.branch_children, out_branch_id))
        #     if verbose
        #         @info "Out branch id $out_branch_id"
        #         @info "Children $(get_connected_from(sc.branch_children, out_branch_id))"
        #     end
        #     out_branch_id = first(get_connected_from(sc.branch_children, out_branch_id))
        # end
        entry_id = sc.branch_entries[out_branch_id]

        if !haskey(sc.entry_queues_forward, entry_id)
            if verbose
                @info "Queue is empty"
            end
            return Set(), Set([(_get_entries(sc, vars_mapping, branches), bl)])
        end
        q = sc.entry_queues_forward[entry_id]
        not_on_path = Set()
        not_on_path_bp = Set()
        @test !isempty(sc.blocks_to_insert) || !isempty(q)
        while !isempty(sc.blocks_to_insert) || !isempty(q)
            if !isempty(sc.blocks_to_insert)
                (br_id, block_info), cost = peek(sc.blocks_to_insert)
                br_id, block_info = dequeue!(sc.blocks_to_insert)

                if br_id != out_branch_id || !is_on_path(block_info[1], bl.p, Dict())
                    push!(not_on_path, (br_id, block_info, cost))
                    continue
                end

                found_solutions =
                    enumeration_iteration_insert_block(sc, false, br_id, block_info, guiding_model_channels, grammar)

                if verbose
                    @info "found end"
                    @info "Out branch id $out_branch_id"
                end

                for (br_id_, block_info_, cost_) in not_on_path
                    sc.blocks_to_insert[(br_id_, block_info_)] = cost_
                end

                for (bp_, p_) in not_on_path_bp
                    q[bp_] = p_
                end

                in_blocks = get_connected_from(sc.branch_incoming_blocks, out_branch_id)
                if verbose
                    @info "in_blocks: $in_blocks"
                end
                if isempty(in_blocks)
                    children = get_connected_from(sc.branch_children, out_branch_id)
                    if verbose
                        @info "children: $children"
                        @info sc.branch_children
                    end
                    if isempty(children)
                        if verbose
                            @info "Can't add block"
                        end
                        return Set(), Set([(_get_entries(sc, vars_mapping, branches), bl)])
                    end
                    @test length(children) == 1
                    child_id = first(children)
                    in_blocks = get_connected_from(sc.branch_incoming_blocks, child_id)
                end
                @test !isempty(in_blocks)
                if verbose
                    @info "in_blocks: $in_blocks"
                end
                created_block_id = first(values(in_blocks))
                created_block = sc.blocks[created_block_id]
                if verbose
                    @info "created_block: $created_block"
                end

                updated_branches = copy(branches)
                created_block_copy_id = first(keys(in_blocks))
                in_branches = keys(get_connected_to(sc.branch_outgoing_blocks, created_block_copy_id))
                for in_branch in in_branches
                    updated_branches[sc.branch_vars[in_branch]] = in_branch
                end
                out_branches = keys(get_connected_to(sc.branch_incoming_blocks, created_block_copy_id))
                for out_branch in out_branches
                    updated_branches[sc.branch_vars[out_branch]] = out_branch
                end
                updated_branches = _fetch_branches_children(sc, updated_branches)
                if verbose
                    @info "updated_branches: $updated_branches"
                end

                updated_vars_mapping = copy(vars_mapping)
                for (original_var, new_var) in zip(bl.input_vars, created_block.input_vars)
                    if !haskey(updated_vars_mapping, original_var)
                        updated_vars_mapping[original_var] = new_var
                    end
                end
                if verbose
                    @info "updated_vars_mapping: $updated_vars_mapping"
                end
                updated_history = vcat(branches_history, [(branches, bl)])

                if isempty(rem_blocks)
                    @test !isempty(found_solutions)
                    for solution_path in found_solutions
                        solution, cost = extract_solution(sc, solution_path)
                        ll = task.log_likelihood_checker(task, solution)
                        @test !isnothing(ll)
                        @test !isinf(ll)
                    end
                end

                return _check_reachable(
                    sc,
                    task,
                    rem_blocks,
                    updated_vars_mapping,
                    updated_branches,
                    updated_history,
                    guiding_model_server,
                    guiding_model_channels,
                    grammar,
                    run_context,
                    mfp,
                    verbose,
                )
            else
                bp, p = peek(q)
                bp = dequeue!(q)
                if verbose
                    @info bp
                end
                if is_on_path(bp.skeleton, bl.p, Dict())
                    if verbose
                        @info "on path"
                    end

                    enumeration_iteration(run_context, sc, mfp, bp, entry_id, true)
                else
                    push!(not_on_path_bp, (bp, p))
                    if verbose
                        @info "not on path"
                    end
                end
            end
        end
        if verbose
            @info "Failed to find block $bl"
        end
        return Set(), Set([(_get_entries(sc, vars_mapping, branches), bl)])
    end

    function _simulate_block_search(
        sc,
        task,
        bl::ReverseProgramBlock,
        rem_blocks,
        branches,
        branches_history,
        vars_mapping,
        guiding_model_server,
        guiding_model_channels,
        grammar,
        run_context,
        mfp,
        verbose,
    )
        if verbose
            @info "Simulating block search for $bl"
        end
        in_branch_id = branches[vars_mapping[bl.input_vars[1]]]
        in_entry_id = sc.branch_entries[in_branch_id]
        if !haskey(sc.entry_queues_reverse, in_entry_id)
            if verbose
                @info "Queue is empty"
            end
            return Set(), Set([(_get_entries(sc, vars_mapping, branches), bl)])
        end
        q = sc.entry_queues_reverse[in_entry_id]

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

        not_on_path = Set()
        @test !isempty(sc.rev_blocks_to_insert) || !isempty(q)
        while !isempty(sc.rev_blocks_to_insert) || !isempty(q)
            if !isempty(sc.rev_blocks_to_insert)
                (br_id, block_info), cost = peek(sc.rev_blocks_to_insert)
                br_id, block_info = dequeue!(sc.rev_blocks_to_insert)

                if br_id != in_branch_id || !is_on_path(block_info[1], bl.p, Dict())
                    push!(not_on_path, (br_id, block_info, cost))
                    continue
                end

                found_solutions =
                    enumeration_iteration_insert_block(sc, true, br_id, block_info, guiding_model_channels, grammar)

                if verbose
                    @info "found end"
                end

                for (br_id_, block_info_, cost_) in not_on_path
                    sc.rev_blocks_to_insert[(br_id_, block_info_)] = cost_
                end

                out_blocks = get_connected_from(sc.branch_outgoing_blocks, in_branch_id)
                if isempty(out_blocks)
                    children = get_connected_from(sc.branch_children, in_branch_id)
                    @test length(children) == 1
                    child_id = first(children)
                    out_blocks = get_connected_from(sc.branch_outgoing_blocks, child_id)
                end
                @test !isempty(out_blocks)
                if verbose
                    @info "out_blocks: $out_blocks"
                end
                updated_branches = copy(branches)
                updated_vars_mapping = copy(vars_mapping)
                for (created_block_copy_id, created_block_id) in out_blocks
                    created_block = sc.blocks[created_block_id]
                    if isa(created_block, ReverseProgramBlock) && is_on_path(created_block.p, bl.p, Dict())
                        if verbose
                            @info "created_block: $created_block"
                            @info "created_block_copy_id: $created_block_copy_id"
                        end

                        out_branches = keys(get_connected_to(sc.branch_incoming_blocks, created_block_copy_id))
                        for out_branch in out_branches
                            updated_branches[sc.branch_vars[out_branch]] = out_branch
                        end
                        updated_branches = _fetch_branches_children(sc, updated_branches)
                        if verbose
                            @info "updated_branches: $updated_branches"
                        end

                        for (original_var, new_var) in zip(bl.output_vars, created_block.output_vars)
                            if !haskey(updated_vars_mapping, original_var)
                                updated_vars_mapping[original_var] = new_var
                            end
                        end
                        if verbose
                            @info "updated_vars_mapping: $updated_vars_mapping"
                        end
                        break
                    end
                end

                updated_history = vcat(branches_history, [(branches, bl)])

                if isempty(rem_blocks)
                    @test !isempty(found_solutions)
                    for solution_path in found_solutions
                        solution, cost = extract_solution(sc, solution_path)
                        ll = task.log_likelihood_checker(task, solution)
                        @test !isnothing(ll)
                        @test !isinf(ll)
                    end
                end

                return _check_reachable(
                    sc,
                    task,
                    rem_blocks,
                    updated_vars_mapping,
                    updated_branches,
                    updated_history,
                    guiding_model_server,
                    guiding_model_channels,
                    grammar,
                    run_context,
                    mfp,
                    verbose,
                )
            else
                bp = dequeue!(q)
                if verbose
                    @info bp
                end
                if is_on_path(bp.skeleton, bl.p, Dict()) ||
                   (wrapped_func !== nothing && is_on_path(bp.skeleton, wrapped_func, Dict()))
                    if verbose
                        @info "on path"
                    end
                    enumeration_iteration(run_context, sc, mfp, bp, in_entry_id, false)
                else
                    if verbose
                        @info "not on path"
                    end
                end
            end
        end
        if verbose
            @info "Failed to find block $bl"
        end
        return Set(), Set([(_get_entries(sc, vars_mapping, branches), bl)])
    end

    function _check_reachable(
        sc,
        task,
        blocks,
        vars_mapping,
        branches,
        branches_history,
        guiding_model_server,
        guiding_model_channels,
        grammar,
        run_context,
        mfp,
        verbose,
    )
        checked_any = false
        if isempty(blocks)
            if verbose
                @info "Found all blocks"
            end
            return Set([Set([(_get_entries(sc, vars_mapping, brs), bl) for (brs, bl) in branches_history])]), Set()
        end
        successful = Set()
        failed = Set()
        if verbose
            @info "Checking blocks $blocks"
        end

        while !isempty(sc.waiting_entries)
            sleep(0.001)
            receive_grammar_weights(sc, guiding_model_channels, grammar)
        end

        has_multiple_options = length([1 for b in blocks if _block_can_be_next(b, vars_mapping)]) > 1
        for bl in blocks
            if _block_can_be_next(bl, vars_mapping)
                checked_any = true
                if has_multiple_options
                    sc_next = deepcopy(sc)
                    sc_next.task_name = sc.task_name * "_$bl"

                    if !isa(guiding_model_server, PythonGuidingModelServer)
                        put!(guiding_model_server.worker_register_channel, sc_next.task_name)
                        task_name, request_channel, result_channel, end_tasks_channel =
                            take!(guiding_model_server.worker_register_result_channel)
                        guiding_model_channels = (request_channel, result_channel, end_tasks_channel)
                    end
                else
                    sc_next = sc
                end
                s, f = try
                    _simulate_block_search(
                        sc_next,
                        task,
                        bl,
                        Any[b for b in blocks if b != bl],
                        branches,
                        branches_history,
                        vars_mapping,
                        guiding_model_server,
                        guiding_model_channels,
                        grammar,
                        run_context,
                        mfp,
                        verbose,
                    )
                finally
                    if has_multiple_options
                        mark_task_finished(guiding_model_channels, sc_next.task_name)
                    end
                end
                union!(successful, s)
                union!(failed, f)
            end
        end
        if verbose
            @info "checked_any: $checked_any"
            @info "blocks: $blocks"
        end
        @test checked_any
        return successful, failed
    end

    function check_reachable(task, guiding_model, task_grammar, target_solution, verbose_test = false)
        empty!(contextual_grammar_cache)

        guiding_model_server = GuidingModelServer(guiding_model)
        start_server(guiding_model_server, true)
        set_current_grammar!(guiding_model, task_grammar)

        try
            mfp = 10
            run_context = Dict{String,Any}("program_timeout" => 1, "timeout" => 40)

            type_weights = Dict(
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

            hyperparameters = Dict(
                "path_cost_power" => 1.0,
                "complexity_power" => 1.0,
                "block_cost_power" => 1.0,
                "explained_penalty_power" => 1.0,
                "explained_penalty_mult" => 5.0,
                "match_duplicates_penalty" => 3.0,
            )

            target_program = parse_program(target_solution)

            ll = task.log_likelihood_checker(task, target_program)
            @test !isnothing(ll) && !isinf(ll)
            if isnothing(ll) || isinf(ll)
                return
            end

            blocks, vars_mapping = _extract_blocks(task, target_program, verbose_test)
            if verbose_test
                @info blocks
                @info vars_mapping
            end

            if isa(guiding_model_server, PythonGuidingModelServer)
                redis_db = guiding_model_server.model.redis_db
                guiding_model_channels = get_redis_connection(redis_db)
            else
                put!(guiding_model_server.worker_register_channel, task.name)
                task_name, request_channel, result_channel, end_tasks_channel =
                    take!(guiding_model_server.worker_register_result_channel)
                guiding_model_channels = (request_channel, result_channel, end_tasks_channel)
            end

            sc = create_starting_context(task, task.name, type_weights, hyperparameters, verbose_test)

            try
                enqueue_updates(sc, guiding_model_channels, task_grammar)
                branches = Dict()
                for br_id in 1:sc.branches_count[]
                    branches[sc.branch_vars[br_id]] = br_id
                end
                if verbose_test
                    @info branches
                end
                save_changes!(sc, 0)

                inner_mapping = Dict{UInt64,UInt64}()
                for (arg, _) in task.task_type.arguments
                    for (v, a) in sc.input_keys
                        if a == arg
                            inner_mapping[v] = vars_mapping[arg]
                        end
                    end
                end
                inner_mapping[vars_mapping["out"]] = sc.branch_vars[sc.target_branch_id]
                if verbose_test
                    @info inner_mapping
                end

                successful, failed = @time _check_reachable(
                    sc,
                    task,
                    blocks,
                    inner_mapping,
                    branches,
                    [],
                    guiding_model_server,
                    guiding_model_channels,
                    task_grammar,
                    run_context,
                    mfp,
                    verbose_test,
                )
                if verbose_test
                    @info "successful: $successful"
                    @info "failed: $failed"
                    @info "length successful: $(length(successful))"
                    @info "length failed: $(length(failed))"
                end
                @test !isempty(successful)
                for f_entries in failed
                    for s_snapshots in successful
                        @test all(s_entries != f_entries for s_entries in s_snapshots)
                        if any(s_entries == f_entries for s_entries in s_snapshots)
                            @info "Found failed case"
                            @info f_entries
                            @info s_snapshots
                        end
                    end
                end
            finally
                mark_task_finished(guiding_model_channels, task.name)
            end
        finally
            set_current_grammar!(guiding_model, grammar)
            stop_server(guiding_model_server)
        end
    end

    grammar = build_grammar(sample_library)
    grammar2 = build_grammar(sample_library2)

    guiding_model = get_guiding_model("dummy")

    @testcase_log "Repeat" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "invert repeated",
                "examples" => Any[
                    Dict{String,Any}(
                        "output" => Any[4, 4, 4, 4, 4],
                        "inputs" => Dict{String,Any}("inp0" => Any[5, 5, 5, 5]),
                    ),
                    Dict{String,Any}("output" => Any[1, 1, 1, 1, 1, 1], "inputs" => Dict{String,Any}("inp0" => Any[6])),
                    Dict{String,Any}("output" => Any[3, 3], "inputs" => Dict{String,Any}("inp0" => Any[2, 2, 2])),
                ],
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )
        target_solution = "let \$v1, \$v2 = rev(\$inp0 = (repeat \$v1 \$v2)) in (repeat \$v2 \$v1)"
        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Find const" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "find const",
                "examples" => Any[
                    Dict{String,Any}(
                        "output" => Any[4, 4, 4, 4, 4],
                        "inputs" => Dict{String,Any}("inp0" => Any[5, 5, 5, 5]),
                    ),
                    Dict{String,Any}("output" => Any[1, 1, 1, 1, 1], "inputs" => Dict{String,Any}("inp0" => Any[6])),
                    Dict{String,Any}(
                        "output" => Any[3, 3, 3, 3, 3],
                        "inputs" => Dict{String,Any}("inp0" => Any[2, 2, 2]),
                    ),
                ],
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )
        target_solution = "let \$v1, \$v2 = rev(\$inp0 = (repeat \$v1 \$v2)) in let \$v3 = Const(int, 5) in (repeat \$v2 \$v3)"
        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Use eithers" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "use eithers",
                "examples" => Any[
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
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )
        target_solution = "let \$v1 = Const(list(int), Any[6, 7, 8, 9, 10]) in (concat \$inp0 \$v1)"
        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Use eithers 2" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "use eithers",
                "examples" => Any[
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
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )
        target_solution = "let \$v1 = (length \$inp0) in let \$v2 = Const(int, 1) in let \$v3 = (repeat \$v1 \$v2) in let \$v4 = (concat \$inp0 \$v3) in let \$v5 = Const(list(int), Any[6, 7, 8, 9, 10]) in (concat \$v4 \$v5)"
        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Use eithers from input" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "use eithers",
                "examples" => Any[
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
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )
        target_solution = "let \$v1, \$v2 = rev(\$inp0 = (rev_fix_param (concat \$v1 \$v2) \$v2 (lambda Const(list(int), Any[10, 9, 8, 7])))) in \$v1"
        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Replace background" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "replace background",
                "examples" => Any[
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
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )
        target_solution = "let \$v1 = Const(int, 1) in let \$v2 = Const(int, 1) in let \$v3, \$v4, \$v5 = rev(\$inp0 = (rev_fix_param (rev_select (lambda (eq? \$0 \$v3)) \$v4 \$v5) \$v3 (lambda Const(int, 3)))) in let \$v6, \$v7 = rev(\$v4 = (repeat \$v6 \$v7)) in let \$v8 = (repeat \$v2 \$v7) in (rev_select (lambda (eq? \$0 \$v1)) \$v8 \$v5)"
        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Add const" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "add const",
                "examples" => Any[
                    Dict{String,Any}("output" => 39, "inputs" => Dict{String,Any}("inp0" => 28)),
                    Dict{String,Any}("output" => 22, "inputs" => Dict{String,Any}("inp0" => 11)),
                    Dict{String,Any}("output" => 5, "inputs" => Dict{String,Any}("inp0" => -6)),
                ],
                "test_examples" => Any[],
                "request" => "inp0:int -> int",
            ),
        )
        target_solution = "let \$v1 = Const(int, 11) in (+ \$v1 \$inp0)"
        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "prepend-index-k with k=3" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "prepend-index-k with k=3",
                "examples" => Any[
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
                    Dict{String,Any}(
                        "output" => Any[6, 11, 3, 6],
                        "inputs" => Dict{String,Any}("inp0" => Any[11, 3, 6]),
                    ),
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
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )

        target_solution = "let \$v1, \$v2 = rev(\$inp0 = (cons \$v1 \$v2)) in let \$v3, \$v4 = rev(\$v2 = (cons \$v3 \$v4)) in let \$v5 = (car \$v4) in let \$v6 = Const(list(int), Any[]) in let \$v7 = (cons \$v5 \$v6) in (concat \$v7 \$inp0)"
        check_reachable(task, guiding_model, grammar2, target_solution)
        # target_solution = "let \$v1 = Const(int, 1) in let \$v2, \$v3 = rev(\$inp0 = (cons \$v2 \$v3)) in let \$v4, \$v5 = rev(\$v3 = (cons \$v4 \$v5)) in let \$v6 = \$v1 in let \$v7 = (index \$v6 \$v5) in let \$v8 = (repeat \$v7 \$v1) in (concat \$v8 \$inp0)"
        # check_reachable(task, guiding_model, grammar, target_solution, true)
    end

    @testcase_log "drop-k with k=5" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "drop-k with k=5",
                "examples" => Any[
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
                    Dict{String,Any}(
                        "output" => Any[12],
                        "inputs" => Dict{String,Any}("inp0" => Any[2, 9, 16, 2, 7, 12]),
                    ),
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
                    Dict{String,Any}(
                        "output" => Any[5],
                        "inputs" => Dict{String,Any}("inp0" => Any[7, 13, 16, 12, 4, 5]),
                    ),
                    Dict{String,Any}(
                        "output" => Any[11, 9],
                        "inputs" => Dict{String,Any}("inp0" => Any[13, 11, 10, 7, 13, 11, 9]),
                    ),
                    Dict{String,Any}(
                        "output" => Any[7, 11],
                        "inputs" => Dict{String,Any}("inp0" => Any[7, 15, 3, 15, 7, 7, 11]),
                    ),
                ],
                "test_examples" => Any[],
                "request" => "inp0:list(int) -> list(int)",
            ),
        )
        target_solution = "let \$v1, \$v2 = rev(\$inp0 = (cons \$v1 \$v2)) in let \$v3, \$v4 = rev(\$v2 = (cons \$v3 \$v4)) in let \$v5, \$v6 = rev(\$v4 = (cons \$v5 \$v6)) in (cdr (cdr \$v6))"

        check_reachable(task, guiding_model, grammar2, target_solution)
    end

    @testcase_log "Select background" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Select background",
                "examples" => Any[Dict{String,Any}(
                    "output" => [
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 9 9 9 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                    ],
                    "inputs" => Dict{String,Any}(
                        "inp0" => [
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        ],
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:grid(color) -> grid(color)",
            ),
        )
        target_solution = "let \$v4 = Const(color, 0) in let \$v6 = (height \$inp0) in let \$v5 = (width \$inp0) in let \$v1 = Const(color, 0) in let \$v2 = (repeat_grid \$v4 \$v5 \$v6) in (rev_select_grid (lambda (eq? \$0 \$v1)) \$v2 \$inp0)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Select background reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Select background",
                "examples" => Any[Dict{String,Any}(
                    "output" => (
                        (20, 20),
                        [
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        ],
                    ),
                    "inputs" => Dict{String,Any}(
                        "inp0" => [
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 9 9 9 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        ],
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:grid(color) -> tuple2(tuple2(int, int), grid(color))",
            ),
        )

        target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$v1)) \$v2 \$v3) \$v1 (lambda Const(color, 0)))) in let \$v4, \$v5, \$v6 = rev(\$v2 = (repeat_grid \$v4 \$v5 \$v6)) in let \$v7 = (tuple2 \$v5 \$v6) in (tuple2 \$v7 \$v3)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Non-background cells" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Non-background cells",
                "examples" => Any[Dict{String,Any}(
                    "output" => [
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing 9 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                    ],
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            ((19, 11), 9),
                            ((5, 3), 7),
                            ((18, 10), 9),
                            ((5, 4), 7),
                            ((11, 11), 2),
                            ((9, 11), 2),
                            ((10, 12), 2),
                            ((5, 5), 7),
                            ((17, 10), 9),
                            ((19, 10), 9),
                            ((18, 9), 9),
                            ((3, 3), 7),
                            ((3, 4), 7),
                            ((18, 11), 9),
                            ((11, 12), 2),
                            ((9, 12), 2),
                            ((11, 13), 2),
                            ((17, 9), 9),
                            ((3, 5), 7),
                            ((4, 4), 7),
                            ((9, 13), 2),
                        ]),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(tuple2(int, int), color)) -> grid(color)",
            ),
        )
        target_solution = "let \$v1 = Const(int, 20) in let \$v2 = Const(int, 20) in (rev_grid_elements \$inp0 \$v1 \$v2)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Non-background cells reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Non-background cells",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        ((19, 11), 9),
                        ((5, 3), 7),
                        ((18, 10), 9),
                        ((5, 4), 7),
                        ((11, 11), 2),
                        ((9, 11), 2),
                        ((10, 12), 2),
                        ((5, 5), 7),
                        ((17, 10), 9),
                        ((19, 10), 9),
                        ((18, 9), 9),
                        ((3, 3), 7),
                        ((3, 4), 7),
                        ((18, 11), 9),
                        ((11, 12), 2),
                        ((9, 12), 2),
                        ((11, 13), 2),
                        ((17, 9), 9),
                        ((3, 5), 7),
                        ((4, 4), 7),
                        ((9, 13), 2),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => [
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        ],
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:grid(color) -> set(tuple2(tuple2(int, int), color))",
            ),
        )
        target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (rev_grid_elements \$v1 \$v2 \$v3)) in \$v1"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Cluster nearby cells" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Cluster nearby cells",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set(
                        Any[
                            ((19, 11), 9),
                            ((5, 3), 7),
                            ((18, 10), 9),
                            ((5, 4), 7),
                            ((11, 11), 2),
                            ((9, 11), 2),
                            ((10, 12), 2),
                            ((5, 5), 7),
                            ((17, 10), 9),
                            ((19, 10), 9),
                            ((18, 9), 9),
                            ((3, 3), 7),
                            ((3, 4), 7),
                            ((18, 11), 9),
                            ((11, 12), 2),
                            ((9, 12), 2),
                            ((11, 13), 2),
                            ((17, 9), 9),
                            ((3, 5), 7),
                            ((4, 4), 7),
                            ((9, 13), 2),
                        ],
                    ),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            Set([
                                ((18, 9), 9),
                                ((19, 11), 9),
                                ((17, 9), 9),
                                ((18, 10), 9),
                                ((18, 11), 9),
                                ((17, 10), 9),
                                ((19, 10), 9),
                            ]),
                            Set([
                                ((11, 12), 2),
                                ((10, 12), 2),
                                ((9, 12), 2),
                                ((11, 13), 2),
                                ((9, 13), 2),
                                ((11, 11), 2),
                                ((9, 11), 2),
                            ]),
                            Set([
                                ((3, 3), 7),
                                ((5, 3), 7),
                                ((3, 4), 7),
                                ((5, 4), 7),
                                ((4, 4), 7),
                                ((3, 5), 7),
                                ((5, 5), 7),
                            ]),
                        ]),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(set(tuple2(tuple2(int, int), color))) -> set(tuple2(tuple2(int, int), color))",
            ),
        )
        target_solution = "(rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) 1)) (not (gt? (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set \$inp0)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Cluster nearby cells reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Cluster nearby cells",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        Set([
                            ((18, 9), 9),
                            ((19, 11), 9),
                            ((17, 9), 9),
                            ((18, 10), 9),
                            ((18, 11), 9),
                            ((17, 10), 9),
                            ((19, 10), 9),
                        ]),
                        Set([
                            ((11, 12), 2),
                            ((10, 12), 2),
                            ((9, 12), 2),
                            ((11, 13), 2),
                            ((9, 13), 2),
                            ((11, 11), 2),
                            ((9, 11), 2),
                        ]),
                        Set([
                            ((3, 3), 7),
                            ((5, 3), 7),
                            ((3, 4), 7),
                            ((5, 4), 7),
                            ((4, 4), 7),
                            ((3, 5), 7),
                            ((5, 5), 7),
                        ]),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set(
                            Any[
                                ((19, 11), 9),
                                ((5, 3), 7),
                                ((18, 10), 9),
                                ((5, 4), 7),
                                ((11, 11), 2),
                                ((9, 11), 2),
                                ((10, 12), 2),
                                ((5, 5), 7),
                                ((17, 10), 9),
                                ((19, 10), 9),
                                ((18, 9), 9),
                                ((3, 3), 7),
                                ((3, 4), 7),
                                ((18, 11), 9),
                                ((11, 12), 2),
                                ((9, 12), 2),
                                ((11, 13), 2),
                                ((17, 9), 9),
                                ((3, 5), 7),
                                ((4, 4), 7),
                                ((9, 13), 2),
                            ],
                        ),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(tuple2(int, int), color)) -> set(set(tuple2(tuple2(int, int), color)))",
            ),
        )
        target_solution = "let \$v1 = rev(\$inp0 = (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) 1)) (not (gt? (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set \$v1)) in \$v1"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Separate colors" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Separate colors",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        Set([
                            ((18, 9), 9),
                            ((19, 11), 9),
                            ((17, 9), 9),
                            ((18, 10), 9),
                            ((18, 11), 9),
                            ((17, 10), 9),
                            ((19, 10), 9),
                        ]),
                        Set([
                            ((11, 12), 2),
                            ((10, 12), 2),
                            ((9, 12), 2),
                            ((11, 13), 2),
                            ((9, 13), 2),
                            ((11, 11), 2),
                            ((9, 11), 2),
                        ]),
                        Set([
                            ((3, 3), 7),
                            ((5, 3), 7),
                            ((3, 4), 7),
                            ((5, 4), 7),
                            ((4, 4), 7),
                            ((3, 5), 7),
                            ((5, 5), 7),
                        ]),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set(
                            Tuple{Set{Tuple{Int64,Int64}},Int64}[
                                (Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]), 9),
                                (Set([(5, 5), (3, 3), (5, 3), (3, 4), (5, 4), (4, 4), (3, 5)]), 7),
                                (Set([(11, 13), (9, 13), (11, 11), (9, 11), (11, 12), (10, 12), (9, 12)]), 2),
                            ],
                        ),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(set(tuple2(int, int)), color)) -> set(set(tuple2(tuple2(int, int), color)))",
            ),
        )
        target_solution = "(map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$inp0)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Separate colors reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Separate colors",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set(
                        Tuple{Set{Tuple{Int64,Int64}},Int64}[
                            (Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]), 9),
                            (Set([(5, 5), (3, 3), (5, 3), (3, 4), (5, 4), (4, 4), (3, 5)]), 7),
                            (Set([(11, 13), (9, 13), (11, 11), (9, 11), (11, 12), (10, 12), (9, 12)]), 2),
                        ],
                    ),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            Set([
                                ((18, 9), 9),
                                ((19, 11), 9),
                                ((17, 9), 9),
                                ((18, 10), 9),
                                ((18, 11), 9),
                                ((17, 10), 9),
                                ((19, 10), 9),
                            ]),
                            Set([
                                ((11, 12), 2),
                                ((10, 12), 2),
                                ((9, 12), 2),
                                ((11, 13), 2),
                                ((9, 13), 2),
                                ((11, 11), 2),
                                ((9, 11), 2),
                            ]),
                            Set([
                                ((3, 3), 7),
                                ((5, 3), 7),
                                ((3, 4), 7),
                                ((5, 4), 7),
                                ((4, 4), 7),
                                ((3, 5), 7),
                                ((5, 5), 7),
                            ]),
                        ]),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(set(tuple2(tuple2(int, int), color))) -> set(tuple2(set(tuple2(int, int)), color))",
            ),
        )
        target_solution = "let \$v1 = rev(\$inp0 = (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$v1)) in \$v1"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Single object coordinates extraction 1" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Single object coordinates extraction",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:tuple2(tuple2(int, int), set(tuple2(int, int))) -> set(tuple2(int, int))",
            ),
        )
        target_solution = "let \$v2, \$v1 = rev(\$inp0 = (tuple2 \$v2 \$v1)) in (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$v2)) (+ (tuple2_second \$0) (tuple2_second \$v2)))) \$v1) \$v2 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Single object coordinates extraction with invented" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Single object coordinates extraction",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:tuple2(tuple2(int, int), set(tuple2(int, int))) -> set(tuple2(int, int))",
            ),
        )

        grammar3 = build_grammar(
            vcat(
                sample_library,
                [
                    "#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0)))",
                    "#(lambda (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))))",
                    "#(lambda (fold (lambda (lambda (#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) \$0 \$1))) \$0 max_int))",
                ],
            ),
        )

        target_solution = "let \$v2, \$v1 = rev(\$inp0 = (tuple2 \$v2 \$v1)) in (rev_fix_param (map_set (lambda (#(lambda (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1))))) \$0 \$v2)) \$v1) \$v2 (lambda (tuple2 (#(lambda (fold (lambda (lambda (#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) \$0 \$1))) \$0 max_int)) (map (lambda (tuple2_first \$0)) (collect \$0))) (#(lambda (fold (lambda (lambda (#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) \$0 \$1))) \$0 max_int)) (map (lambda (tuple2_second \$0)) (collect \$0))))))"

        check_reachable(task, guiding_model, grammar3, target_solution)
    end

    @testcase_log "Single object coordinates extraction reverse 1" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Single object coordinates extraction",
                "examples" => Any[Dict{String,Any}(
                    "output" => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(int, int)) -> tuple2(tuple2(int, int), set(tuple2(int, int)))",
            ),
        )
        target_solution = "let \$v2, \$v1 = rev(\$inp0 = (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$v2)) (+ (tuple2_second \$0) (tuple2_second \$v2)))) \$v1) \$v2 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) in (tuple2 \$v2 \$v1)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Single object coordinates extraction with invented reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Single object coordinates extraction",
                "examples" => Any[Dict{String,Any}(
                    "output" => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(int, int)) -> tuple2(tuple2(int, int), set(tuple2(int, int)))",
            ),
        )

        grammar3 = build_grammar(
            vcat(
                sample_library,
                [
                    "#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0)))",
                    "#(lambda (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))))",
                    "#(lambda (fold (lambda (lambda (#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) \$0 \$1))) \$0 max_int))",
                ],
            ),
        )

        target_solution = "let \$v2, \$v1 = rev(\$inp0 = (rev_fix_param (map_set (lambda (#(lambda (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1))))) \$0 \$v2)) \$v1) \$v2 (lambda (tuple2 (#(lambda (fold (lambda (lambda (#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) \$0 \$1))) \$0 max_int)) (map (lambda (tuple2_first \$0)) (collect \$0))) (#(lambda (fold (lambda (lambda (#(lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) \$0 \$1))) \$0 max_int)) (map (lambda (tuple2_second \$0)) (collect \$0))))))) in (tuple2 \$v2 \$v1)"

        check_reachable(task, guiding_model, grammar3, target_solution)
    end

    @testcase_log "Single object coordinates extraction 2" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Single object coordinates extraction",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:tuple2(tuple2(int, int), set(tuple2(int, int))) -> set(tuple2(int, int))",
            ),
        )

        target_solution = "let \$v2, \$v1 = rev(\$inp0 = (tuple2 \$v2 \$v1)) in ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) \$v2)) \$v1)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Single object coordinates extraction reverse 2" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Single object coordinates extraction",
                "examples" => Any[Dict{String,Any}(
                    "output" => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(int, int)) -> tuple2(tuple2(int, int), set(tuple2(int, int)))",
            ),
        )
        target_solution = "let \$v1, \$v2 = rev(\$inp0 = ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) \$v1)) \$v2)) in (tuple2 \$v1 \$v2)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Get object coordinates" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Get object coordinates",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        (Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]), 9),
                        (Set([(5, 5), (3, 3), (5, 3), (3, 4), (5, 4), (4, 4), (3, 5)]), 7),
                        (Set([(11, 13), (9, 13), (11, 11), (9, 11), (11, 12), (10, 12), (9, 12)]), 2),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            (((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])), 9),
                            (((3, 3), Set([(2, 2), (0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (0, 2)])), 7),
                            (((9, 11), Set([(2, 2), (0, 2), (2, 0), (0, 0), (2, 1), (1, 1), (0, 1)])), 2),
                        ]),
                    ),
                )],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color)) -> set(tuple2(set(tuple2(int, int)), color))",
            ),
        )

        target_solution = "(map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$inp0)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Get object coordinates reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Get object coordinates",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        (((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])), 9),
                        (((3, 3), Set([(2, 2), (0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (0, 2)])), 7),
                        (((9, 11), Set([(2, 2), (0, 2), (2, 0), (0, 0), (2, 1), (1, 1), (0, 1)])), 2),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            (Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]), 9),
                            (Set([(5, 5), (3, 3), (5, 3), (3, 4), (5, 4), (4, 4), (3, 5)]), 7),
                            (Set([(11, 13), (9, 13), (11, 11), (9, 11), (11, 12), (10, 12), (9, 12)]), 2),
                        ]),
                    ),
                ),],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(set(tuple2(int, int)), color)) -> set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))",
            ),
        )

        target_solution = "let \$v1 = rev(\$inp0 = (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v1)) in \$v1"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Select similar shape objects" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Select similar shape objects",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        (((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])), 9),
                        (((3, 3), Set([(2, 2), (0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (0, 2)])), 7),
                        (((9, 11), Set([(2, 2), (0, 2), (2, 0), (0, 0), (2, 1), (1, 1), (0, 1)])), 2),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => (
                            Set([
                                (((9, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                                (((3, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                            ]),
                            Set([(((17, 9), Set([(0, 0), (1, 2), (1, 1), (0, 1), (2, 2), (2, 1), (1, 0)])), 9)]),
                        ),
                    ),
                )],
                "test_examples" => Any[],
                "request" => "inp0:tuple2(set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color)), set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))) -> set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))",
            ),
        )

        target_solution = "let \$v1, \$v2 = rev(\$inp0 = (tuple2 \$v1 \$v2)) in let \$v3 = Const(set(tuple2(int, int)), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])) in (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$v3)) \$v1 \$v2)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Select similar shape objects reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Select similar shape objects",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        (((9, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                        (((3, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            (((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])), 9),
                            (((3, 3), Set([(2, 2), (0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (0, 2)])), 7),
                            (((9, 11), Set([(2, 2), (0, 2), (2, 0), (0, 0), (2, 1), (1, 1), (0, 1)])), 2),
                        ]),
                    ),
                )],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color)) -> set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))",
            ),
        )

        target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (rev_fix_param (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$v1)) \$v2 \$v3) \$v1 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)]))))) in \$v2"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Move objects" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Move objects",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        (((9, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                        (((3, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            (((8, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                            (((2, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                        ]),
                    ),
                )],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color)) -> set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))",
            ),
        )

        target_solution = "let \$v1 = Const(int, 1) in (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) \$v1) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$inp0)"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testcase_log "Move objects reverse" begin
        task = create_task(
            Dict{String,Any}(
                "name" => "Move objects",
                "examples" => Any[Dict{String,Any}(
                    "output" => Set([
                        (((8, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                        (((2, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                    ]),
                    "inputs" => Dict{String,Any}(
                        "inp0" => Set([
                            (((9, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                            (((3, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                        ]),
                    ),
                )],
                "test_examples" => Any[],
                "request" => "inp0:set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color)) -> set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))",
            ),
        )

        target_solution = "let \$v1, \$v2 = rev(\$inp0 = (rev_fix_param (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) \$v1) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v2) \$v1 (lambda 1))) in \$v2"

        check_reachable(task, guiding_model, grammar, target_solution)
    end

    @testset "Guiding model type $model_type" for model_type in ["dummy", "standalone"]
        arc_guiding_model = get_guiding_model(model_type)

        function test_build_manual_trace(task, target_solution, task_grammar, verbose_test = false)
            empty!(contextual_grammar_cache)

            guiding_model_server = GuidingModelServer(arc_guiding_model)
            start_server(guiding_model_server, true)
            set_current_grammar!(arc_guiding_model, task_grammar)

            try
                if model_type == "standalone"
                    redis_db = guiding_model_server.model.redis_db
                    conn = get_redis_connection(redis_db)
                    return @time build_manual_trace(task, task.name, target_solution, conn, task_grammar, verbose_test)
                else
                    register_channel = guiding_model_server.worker_register_channel
                    register_response_channel = guiding_model_server.worker_register_result_channel
                    put!(register_channel, task.name)
                    task_name, request_channel, result_channel, end_tasks_channel = take!(register_response_channel)
                    return @time build_manual_trace(
                        task,
                        task.name,
                        target_solution,
                        (request_channel, result_channel, end_tasks_channel),
                        task_grammar,
                        verbose_test,
                    )
                end
            finally
                set_current_grammar!(arc_guiding_model, grammar)
                stop_server(guiding_model_server)
            end
        end

        @testcase_log "0f39a9d9.json" begin
            task = _create_arc_task("0f39a9d9.json", "sortOfARC/")
            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$v1)) \$v2 \$v3) \$v1 (lambda Const(color, 0)))) in
            let \$v4, \$v5, \$v6 = rev(\$v2 = (repeat_grid \$v4 \$v5 \$v6)) in
            let \$v7, \$v8, \$v9 = rev(\$v3 = (rev_grid_elements \$v7 \$v8 \$v9)) in
            let \$v10 = rev(\$v7 = (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) 1)) (not (gt? (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set \$v10)) in
            let \$v11 = rev(\$v10 = (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$v11)) in
            let \$v12 = rev(\$v11 = (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v12)) in
            let \$v13, \$v14, \$v15 = rev(\$v12 = (rev_fix_param (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$v13)) \$v14 \$v15) \$v13 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)]))))) in
            let \$v16 = Const(int, 1) in
            let \$v17 = (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) \$v16) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v14) in
            let \$v18 = (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$v13)) \$v17 \$v15) in
            let \$v19 = (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v18) in
            let \$v20 = (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$v19) in
            let \$v21 = (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) 1)) (not (gt? (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set \$v20) in
            let \$v22 = (rev_grid_elements \$v21 \$v8 \$v9) in
            let \$v23 = (repeat_grid \$v4 \$v5 \$v6) in
            (rev_select_grid (lambda (eq? \$0 \$v1)) \$v23 \$v22)"

            hit, cost = test_build_manual_trace(task, target_solution, grammar)
            @test !isnothing(hit)
        end

        @testcase_log "0f39a9d9.json_comp" begin
            task = _create_arc_task("0f39a9d9.json", "sortOfARC/")

            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$1)) \$1 \$2)))) \$0 \$1 \$2) \$2 (lambda Const(color, 0)))))) \$v1 \$v2 \$v3)) in
            let \$v4, \$v5, \$v6 = rev(\$v2 = (repeat_grid \$v4 \$v5 \$v6)) in
            let \$v7, \$v8, \$v9 = rev(\$v3 = (rev_grid_elements \$v7 \$v8 \$v9)) in
            let \$v12 = rev(\$v7 = (#(lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster \$2 \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1))))) \$v12 (lambda (lambda (any_set (lambda (and (#(lambda (not (gt? \$0 1))) (#(lambda (lambda (#(lambda (lambda (lambda (abs (- (\$1 (tuple2_first \$0)) (\$1 (tuple2_first \$2))))))) \$0 (lambda (tuple2_first \$0)) \$1))) \$0 \$2)) (#(lambda (not (gt? \$0 1))) (#(lambda (lambda (#(lambda (lambda (lambda (abs (- (\$1 (tuple2_first \$0)) (\$1 (tuple2_first \$2))))))) \$0 (lambda (tuple2_second \$0)) \$1))) \$0 \$2)))) \$0))))) in
            let \$v13, \$v15, \$v14 = rev(\$v12 = (#(lambda (lambda (lambda (rev_fix_param (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$0 \$1) \$2 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)]))))))) \$v13 \$v15 \$v14)) in
            let \$v18 = (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$1)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$2)))) \$v15 \$v14 \$v13) in
            let \$v21 = (#(lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster \$2 \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1))))) \$v18 (lambda (lambda (any_set (lambda (and (#(lambda (not (gt? \$0 1))) (#(lambda (lambda (#(lambda (lambda (lambda (abs (- (\$1 (tuple2_first \$0)) (\$1 (tuple2_first \$2))))))) \$0 (lambda (tuple2_first \$0)) \$1))) \$0 \$2)) (#(lambda (not (gt? \$0 1))) (#(lambda (lambda (#(lambda (lambda (lambda (abs (- (\$1 (tuple2_first \$0)) (\$1 (tuple2_first \$2))))))) \$0 (lambda (tuple2_second \$0)) \$1))) \$0 \$2)))) \$0)))) in
            let \$v22 = (rev_grid_elements \$v21 \$v8 \$v9) in
            let \$v23 = (repeat_grid \$v4 \$v5 \$v6) in
            (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$1)) \$1 \$2)))) \$v22 \$v23 \$v1)"

            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster \$2 \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1)))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$1)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$2))))",
                        "#(lambda (lambda (lambda (abs (- (\$1 (tuple2_first \$0)) (\$1 (tuple2_first \$2)))))))",
                        "#(lambda (columns_to_grid (reverse (columns (rows_to_grid \$0)))))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (not (gt? \$0 1)))",
                        "#(lambda (lambda (rows_to_grid (concat \$0 \$1))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$0 \$1) \$2 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])))))))",
                        "#(lambda (columns_to_grid (concat \$0 (reverse \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (abs (- (\$1 (tuple2_first \$0)) (\$1 (tuple2_first \$2))))))) \$0 (lambda (tuple2_first \$0)) \$1)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (abs (- (\$1 (tuple2_first \$0)) (\$1 (tuple2_first \$2))))))) \$0 (lambda (tuple2_second \$0)) \$1)))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$1)) \$1 \$2))))",
                        "#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) \$0 (reverse \$1))))",
                        "#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1))))",
                        "#(lambda (#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) \$0 (reverse \$1)))) \$0 \$0))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$1)) \$1 \$2)))) \$0 \$1 \$2) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (rows_to_grid (columns \$0)))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) \$0 (reverse \$1)))) (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$1 \$0) (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$0 \$1))))",
                        "#(lambda (#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0))) (rows_to_grid \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$0 (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$1 \$2)))))",
                        "#(lambda (#(lambda (#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) \$0 (reverse \$1)))) \$0 \$0)) (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$0 \$0)))",
                        "#(lambda (lambda (lambda (rows_to_grid (#(lambda (lambda (lambda (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$0 (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$1 \$2))))) \$2 \$0 (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$1 \$2))))))",
                        "#(lambda (lambda (lambda (\$0 (\$1 \$2) (\$1 \$2)))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (rows_to_grid (#(lambda (lambda (lambda (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$0 (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$1 \$2))))) \$2 \$0 (#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$0 \$1)))) (reverse \$0) \$1)))) \$1 \$2)))))) \$0 \$1 \$1)))",
                        "#(lambda (#(lambda (columns_to_grid (concat \$0 (reverse \$0)))) (columns \$0)))",
                        "#(lambda (#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0))) (#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0))) \$0)))",
                        "#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2)))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) \$0 (tuple2_first \$1) \$2))))",
                        "#(lambda (lambda (#(lambda (rows_to_grid (reverse \$0))) (cons \$0 \$1))))",
                        "#(lambda (lambda (lambda (#(lambda (#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0))) (rows_to_grid \$0))) (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) \$0 \$1 \$2)))))",
                        "#(lambda (concat \$0 \$0))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) Const(list(color), Int64[]) \$0 \$1)))",
                        "#(lambda (lambda (lambda (#(lambda (#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0))) (rows_to_grid \$0))) (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) \$0 \$1 \$2)))))",
                        "#(lambda (lambda (lambda (rows_to_grid (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) \$0 \$1 \$2)))))",
                        "#(lambda (lambda (#(lambda (lambda (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) Const(list(color), Int64[]) \$0 \$1))) (car \$0) \$1)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0))) (rows_to_grid \$0))) (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) \$0 \$1 \$2))))) \$0 \$1 Const(list(list(color)), Vector{Int64}[]))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) \$0 (tuple2_first \$1) \$2))))",
                        "#(lambda (lambda (lambda (#(lambda (#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0))) (rows_to_grid \$0))) (#(lambda (lambda (lambda (cons \$0 (cons \$1 \$2))))) \$0 \$1 \$2)))))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "8b6f1472.json" begin
            task = _create_arc_task("8b6f1472.json", "sortOfARC/")
            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$v1)) \$v2 \$v3) \$v1 (lambda Const(color, 0)))) in
            let \$v4, \$v5, \$v6 = rev(\$v2 = (repeat_grid \$v4 \$v5 \$v6)) in
            let \$v7, \$v8, \$v9 = rev(\$v3 = (rev_grid_elements \$v7 \$v8 \$v9)) in
            let \$v10 = rev(\$v7 = (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set \$v10)) in
            let \$v11 = rev(\$v10 = (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$v11)) in
            let \$v12 = rev(\$v11 = (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v12)) in
            let \$v13, \$v14, \$v15 = rev(\$v12 = (rev_fix_param (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$v13)) \$v14 \$v15) \$v13 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)]))))) in
            let \$v16 = Const(int, 1) in
            let \$v17 = (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) \$v16) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v14) in
            let \$v18 = (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$v13)) \$v17 \$v15) in
            let \$v19 = (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$v18) in
            let \$v20 = (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$v19) in
            let \$v21 = (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set \$v20) in
            let \$v22 = (rev_grid_elements \$v21 \$v8 \$v9) in
            let \$v23 = (repeat_grid \$v4 \$v5 \$v6) in
            (rev_select_grid (lambda (eq? \$0 \$v1)) \$v23 \$v22)"

            hit, cost = test_build_manual_trace(task, target_solution, grammar)
            @test !isnothing(hit)
        end

        @testcase_log "67a3c6ac.json" begin
            task = _create_arc_task("67a3c6ac.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in (columns_to_grid \$v2)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "68b16354.json" begin
            task = _create_arc_task("68b16354.json")
            target_solution = "let \$v1 = rev(\$inp0 = (rows_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in (rows_to_grid \$v2)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "74dd1130.json" begin
            task = _create_arc_task("74dd1130.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in (rows_to_grid \$v1)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "ed36ccf7.json" begin
            task = _create_arc_task("ed36ccf7.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in (rows_to_grid \$v2)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "9dfd6313.json" begin
            task = _create_arc_task("9dfd6313.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in (rows_to_grid \$v1)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "6d0aefbc.json" begin
            task = _create_arc_task("6d0aefbc.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in let \$v3 = (concat \$v1 \$v2) in (columns_to_grid \$v3)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "8be77c9e.json" begin
            task = _create_arc_task("8be77c9e.json")
            target_solution = "let \$v1 = rev(\$inp0 = (rows_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in let \$v3 = (concat \$v1 \$v2) in (rows_to_grid \$v3)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "c9e6f938.json" begin
            task = _create_arc_task("c9e6f938.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in let \$v3 = (concat \$v1 \$v2) in (columns_to_grid \$v3)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "25ff71a9.json" begin
            task = _create_arc_task("25ff71a9.json")
            # target_solution = "let \$v1 = rev(\$inp0 = (rows_to_grid \$v1)) in let \$v2 = Const(list(list(color)), Vector{Any}[[0, 0, 0]]) in let \$v3, \$v4 = wrap(let \$v3, \$v4 = rev(\$v1 = (concat \$v3 \$v4)); let \$v4 = \$v2) in let \$v5 = (concat \$v4 \$v3) in (rows_to_grid \$v5)"
            target_solution = "let \$v1 = rev(\$inp0 = (rows_to_grid \$v1)) in let \$v3, \$v4 = rev(\$v1 = (rev_fix_param (concat \$v3 \$v4) \$v4 (lambda Const(list(list(color)), Vector{Any}[[0, 0, 0]])))) in let \$v5 = (concat \$v4 \$v3) in (rows_to_grid \$v5)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "6fa7a44f.json" begin
            task = _create_arc_task("6fa7a44f.json")
            target_solution = "let \$v1 = rev(\$inp0 = (rows_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in let \$v3 = (concat \$v1 \$v2) in (rows_to_grid \$v3)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "a416b8f3.json" begin
            task = _create_arc_task("a416b8f3.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in let \$v3 = \$v1 in let \$v2 = (concat \$v1 \$v3) in (columns_to_grid \$v2)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "a416b8f3_2.json" begin
            task = _create_arc_task("a416b8f3.json")
            target_solution = "let \$v1 = rev(\$inp0 = (columns_to_grid \$v1)) in let \$v2 = (concat \$v1 \$v1) in (columns_to_grid \$v2)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "4c4377d9.json" begin
            task = _create_arc_task("4c4377d9.json")
            target_solution = "let \$v1 = rev(\$inp0 = (rows_to_grid \$v1)) in let \$v2 = rev(\$v1 = (reverse \$v2)) in let \$v3 = (concat \$v2 \$v1) in (rows_to_grid \$v3)"

            check_reachable(task, arc_guiding_model, grammar, target_solution)
        end

        @testcase_log "4c4377d9_inv.json" begin
            task = _create_arc_task("4c4377d9.json")
            target_solution = "let \$v1 = rev(\$inp0 = (rows_to_grid \$v1)) in
                let \$v2 = rev(\$v1 = (reverse \$v2)) in
                (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$v2 \$v1)"

            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (columns_to_grid (reverse \$0)))",
                        "#(lambda (lambda (columns_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (lambda (rows_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (columns_to_grid (rows \$0)))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (rows \$0)))",
                        "#(lambda (tuple2_second (tuple2_second \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (rows_to_grid (rows (columns_to_grid \$0))))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 \$0))",
                        "#(lambda (lambda (map_grid (lambda (tuple2_first \$0)) (zip_grid2 (rows_to_grid \$1) \$0))))",
                    ],
                ),
            )
            # check_reachable(task, arc_guiding_model, grammar3, target_solution)
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "68b16354_2.json" begin
            task = _create_arc_task("68b16354.json")
            target_solution = "let \$v1 = rev(\$inp0 = (#(lambda (rows_to_grid (reverse \$0))) \$v1)) in
                let \$v2, \$v3 = rev(\$v1 = (rev_list_elements \$v2 \$v3)) in
                let \$v4 = rev(\$inp0 = (map_grid (lambda (tuple2_second \$0)) \$v4)) in
                let \$v5, \$v6, \$v7 = rev(\$v4 = (rev_grid_elements \$v5 \$v6 \$v7)) in
                let \$v8 = rev(\$v6 = (tuple2_first \$v8)) in
                let \$v9 = (tuple2_first \$v8) in
                let \$v10 = (rev_list_elements \$v2 \$v9) in
                (rows_to_grid \$v10)"
            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (concat \$0 (reverse \$0)))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (columns_to_grid (concat \$0 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (rows_to_grid (#(lambda (concat \$0 (reverse \$0))) \$0)))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (tuple2_second (tuple2_second \$0)))",
                        "#(lambda (columns_to_grid (#(lambda (concat \$0 (reverse \$0))) \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "3af2c5a8.json" begin
            task = _create_arc_task("3af2c5a8.json")
            target_solution = "let \$v1 = Const(list(list(color)), Vector{Any}[]) in
                let \$v2 = rev(\$inp0 = (rows_to_grid \$v2)) in
                let \$v3 = (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) \$v2) in
                let \$v4 = (rows \$v3) in
                let \$v5 = (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) \$v4) in
                let \$v6 = (columns \$v5) in
                (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$v1 \$v6)"
            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (columns_to_grid (reverse (rows \$0))))",
                        "#(lambda (lambda (columns_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (lambda (rows_to_grid (concat \$1 \$0))))",
                        "#(lambda (columns_to_grid (rows \$0)))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) (columns \$0) (columns \$0)))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 (reverse \$0))))",
                        "#(lambda (#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 (reverse \$0)))) \$0 \$0))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                        "#(lambda (lambda (lambda (\$2 (rows (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$1 \$0))))))",
                        "#(lambda (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) (rows (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) \$0))))",
                        "#(lambda (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) (columns \$0)))",
                        "#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "22d4b83c.json" begin
            task = _create_arc_task("22d4b83c.json", "sortOfARC/")
            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$v1 \$v2 \$v3)) in
                let \$v4, \$v5 = rev(\$v3 = (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$v4 \$v5 \$v5)) in
                let \$v6, \$v7, \$v8 = rev(\$v4 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v6 \$v7 \$v8) \$v6 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (1, 1), (2, 0), (0, 1), (2, 1), (1, 0)]))))) in
                let \$v9 = Const(color, 9) in
                let \$v10, \$v11, \$v12 = rev(\$v3 = (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) \$v10 \$v11 \$v12)) in
                let \$v13 = rev(\$v10 = (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$v13)) in
                let \$v14, \$v15, \$v16 = rev(\$v13 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v14 \$v15 \$v16) \$v14 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (1, 1), (2, 0), (0, 1), (2, 1), (1, 0)]))))) in
                let \$v17, \$v18 = rev(\$v15 = (#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0))) \$v17 \$v18)) in
                let \$v19 = (#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0))) \$v9 \$v18) in
                let \$v20 = (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v6 \$v19 \$v8) in
                let \$v21, \$v22 = rev(\$v3 = (#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))) \$v21 \$v22)) in
                (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) \$2 (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))))) \$inp0 \$v20 \$v22)"
            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (columns_to_grid (reverse (rows \$0))))",
                        "#(lambda (lambda (columns_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (lambda (rows_to_grid (concat \$1 \$0))))",
                        "#(lambda (columns_to_grid (rows \$0)))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) (columns \$0) (columns \$0)))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 (reverse \$0))))",
                        "#(lambda (#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 (reverse \$0)))) \$0 \$0))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                        "#(lambda (lambda (lambda (\$2 (rows (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$1 \$0))))))",
                        "#(lambda (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) (rows (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) \$0))))",
                        "#(lambda (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) (columns \$0)))",
                        "#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) \$2 (repeat_grid Const(color, 0) \$1 \$1) (#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0)))) \$0 \$1 \$1)))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (repeat_grid \$1 \$0 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) \$2 (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "0f39a9d9_3.json" begin
            task = _create_arc_task("0f39a9d9.json", "sortOfARC/")
            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$v1 \$v2 \$v3)) in
                let \$v4, \$v5, \$v6 = rev(\$v2 = (repeat_grid \$v4 \$v5 \$v6)) in
                let \$v7, \$v8, \$v9 = rev(\$v3 = (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$v7 \$v8 \$v9)) in
                let \$v10, \$v11, \$v12 = rev(\$v7 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v10 \$v11 \$v12) \$v10 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (1, 1), (2, 0), (0, 1), (0, 2), (2, 2), (2, 1)]))))) in
                let \$v13, \$v14, \$v15 = rev(\$v3 = (#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0)))) \$v13 \$v14 \$v15)) in
                let \$v16 = rev(\$v13 = (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$v16)) in
                let \$v17, \$v18, \$v19 = rev(\$v16 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v17 \$v18 \$v19) \$v17 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (1, 1), (2, 0), (0, 1), (0, 2), (2, 2), (2, 1)]))))) in
                let \$v20 = (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0))))) \$v10 \$v11 \$v19) in
                (#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$1 \$1) (#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0)))) \$0 \$1 \$1)))) \$v6 \$v20)"
            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (columns_to_grid (reverse (rows \$0))))",
                        "#(lambda (lambda (columns_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (lambda (rows_to_grid (concat \$1 \$0))))",
                        "#(lambda (columns_to_grid (rows \$0)))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) (columns \$0) (columns \$0)))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 (reverse \$0))))",
                        "#(lambda (#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 (reverse \$0)))) \$0 \$0))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                        "#(lambda (lambda (lambda (\$2 (rows (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$1 \$0))))))",
                        "#(lambda (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) (rows (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) \$0))))",
                        "#(lambda (#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 (reverse \$0))) (columns \$0)))",
                        "#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$1 \$1) (#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0)))) \$0 \$1 \$1))))",
                        "#(lambda (columns_to_grid (reverse (columns \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "0f39a9d9_4.json" begin
            task = _create_arc_task("0f39a9d9.json", "sortOfARC/")
            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$v1 \$v2 \$v3)) in
                let \$v4, \$v5 = rev(\$inp0 = (#(lambda (lambda (#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$2) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))))) \$1 \$0 \$1))) \$1 (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$0)))) \$v4 \$v5)) in
                let \$v6 = Const(set(tuple2(int, int)), Set([(0, 0), (2, 0), (0, 2), (0, 1), (1, 1), (2, 2), (2, 1)])) in
                let \$v7, \$v8, \$v9 = rev(\$v5 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v7 \$v8 \$v9) \$v7 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (1, 1), (2, 0), (0, 1), (0, 2), (2, 2), (2, 1)]))))) in
                let \$v10 = (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0))))) \$v6 \$v8 \$v9) in
                (#(lambda (lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$2 (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) \$2 \$1) (\$0 \$1))))) \$2 \$1 (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$2 \$0)))))) \$v1 \$v4 \$v10)"

            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (lambda (columns_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (columns_to_grid (reverse (columns \$0))))",
                        "#(lambda (lambda (rows_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (rows \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 \$0))",
                        "#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) (reverse \$0) \$0))",
                        "#(lambda (columns (#(lambda (rows_to_grid (reverse \$0))) \$0)))",
                        "#(lambda (lambda (lambda (rows_to_grid (cons \$2 (cons \$1 \$0))))))",
                        "#(lambda (columns_to_grid (rows \$0)))",
                        "#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                        "#(lambda (columns_to_grid (reverse \$0)))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) (reverse \$0) \$0))",
                        "#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$2 \$2) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))))",
                        "#(lambda (lambda (#(lambda (rows_to_grid (reverse \$0))) (cons \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (reverse (columns \$0))))",
                        "#(lambda (lambda (repeat_grid \$1 \$0 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$2) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$2) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))))) \$1 \$0 \$1)))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) \$2 (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) \$2 (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))))) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$1) \$0 \$1)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) \$2 (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))))",
                        "#(lambda (reverse (rows (columns_to_grid (reverse \$0)))))",
                        "#(lambda (lambda (#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$2) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))))) \$1 \$0 \$1))) \$1 (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$0))))",
                        "#(lambda (columns (rows_to_grid (reverse \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$1) \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$1) \$0))) \$1 (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$0 \$1 \$1))))",
                        "#(lambda (lambda (lambda (cons \$2 (cons \$1 \$0)))))",
                        "#(lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) (\$1 \$0) (reverse (\$1 \$0)))))",
                        "#(lambda (#(lambda (rows_to_grid (reverse \$0))) (columns (rows_to_grid \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) \$1 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) Const(color, 0) \$2) (\$1 \$0 \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$2 (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) \$2 \$1) (\$0 \$1)))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$2 (#(lambda (lambda (repeat_grid \$1 \$0 \$0))) \$2 \$1) (\$0 \$1))))) \$2 \$1 (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$2 \$0))))))",
                        "#(lambda (lambda (columns_to_grid (rows (\$1 (reverse \$0))))))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "0f39a9d9_5.json" begin
            task = _create_arc_task("0f39a9d9.json", "sortOfARC/")
            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$v1 \$v2 \$v3)) in
                let \$v4, \$v5, \$v6 = rev(\$v3 = (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$v4 \$v5 \$v6)) in
                let \$v7, \$v8, \$v9 = rev(\$v4 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v7 \$v8 \$v9) \$v7 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (1, 1), (2, 0), (0, 1), (0, 2), (2, 2), (2, 1)]))))) in
                (#(lambda (lambda (lambda (#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$1 \$1) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$0 \$1 \$1)))) Const(int, 20) (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0))))) \$2 \$1 \$0))))) \$v7 \$v8 \$v9)"

            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (rows_to_grid (reverse (rows \$0))))",
                        "#(lambda (columns_to_grid (reverse \$0)))",
                        "#(lambda (lambda (columns_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (lambda (rows_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (#(lambda (columns_to_grid (reverse \$0))) (columns \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 \$0))",
                        "#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) (reverse \$0) \$0))",
                        "#(lambda (#(lambda (rows_to_grid (reverse (rows \$0)))) (rows_to_grid (columns (rows_to_grid \$0)))))",
                        "#(lambda (lambda (lambda (\$2 (reverse (columns (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 \$0))) (columns (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 \$0))))))",
                        "#(lambda (columns_to_grid (rows \$0)))",
                        "#(lambda (rows (#(lambda (columns_to_grid (reverse \$0))) \$0)))",
                        "#(lambda (lambda (columns (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 \$0))))",
                        "#(lambda (#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) (reverse \$0) \$0)) (rows \$0)))",
                        "#(lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$0 (reverse \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (\$2 (reverse (columns (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 \$0))) (columns (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$1 \$0)))))) (lambda (lambda (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) \$0 \$1))) \$1 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$2 \$2) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))))",
                        "#(lambda (lambda (repeat_grid \$1 \$0 \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$1 \$1) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$0 \$1 \$1))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$2 \$2) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))))) \$1 \$0 \$1)))",
                        "#(lambda (lambda (rows_to_grid (columns (#(lambda (lambda (rows_to_grid (concat \$1 \$0)))) (columns \$1) \$0)))))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$1 \$1) (\$0 \$1))))",
                        "#(lambda (lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) (columns \$1) \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0))))) Const(set(tuple2(int, int)), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])) \$1 \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$1 \$1) (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$0 \$1 \$1)))) Const(int, 20) (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0))))) \$2 \$1 \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) \$2 (repeat_grid Const(color, 0) \$1 \$1) (\$0 \$1 \$1)))))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end

        @testcase_log "a2965d01.json" begin
            task = _create_arc_task("a2965d01.json", "sortOfARC/")
            target_solution = "let \$v1, \$v2, \$v3 = rev(\$inp0 = (#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0)))))) \$v1 \$v2 \$v3)) in
                let \$v4, \$v5, \$v6 = rev(\$v3 = (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$v4 \$v5 \$v6)) in
                let \$v7 = \$v5 in
                let \$v8, \$v9 = rev(\$v3 = (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$v8 \$v9 \$v9)) in
                let \$v10, \$v11, \$v12 = rev(\$v8 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v10 \$v11 \$v12) \$v10 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)]))))) in
                let \$v13, \$v14, \$v15 = rev(\$v3 = (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$v13 \$v14 \$v15)) in
                let \$v16, \$v17, \$v18 = rev(\$v13 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v16 \$v17 \$v18) \$v16 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)]))))) in
                let \$v19, \$v20 = rev(\$v3 = (#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0))) \$v19 \$v20)) in
                let \$v21, \$v22, \$v23 = rev(\$v19 = (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0)))) \$v21 \$v22 \$v23) \$v21 (lambda Const(set(tuple2(int, int)), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)]))))) in
                let \$v24 = (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0))))) \$v10 \$v17 \$v23) in
                (#(lambda (lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$2 \$2) (\$1 \$0 \$0))))) \$2 (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$3 \$1 \$0))) \$0)))) \$v7 \$v24 \$v5)"

            grammar3 = build_grammar(
                vcat(
                    sample_library,
                    [
                        "#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0))",
                        "#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0)))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) (map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) Const(int, 1)) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$1) \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0)))))))",
                        "#(lambda (lambda (lambda (rev_fix_param (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0) \$2 (lambda Const(color, 0))))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2))))) 1))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$2)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) \$3)) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0))))",
                        "#(lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$2)) \$0))))",
                        "#(lambda (rows_to_grid (reverse \$0)))",
                        "#(lambda (lambda (columns_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (lambda (map_set (lambda (tuple2 \$0 \$2)) \$0)))",
                        "#(lambda (lambda (rows_to_grid (concat \$1 \$0))))",
                        "#(lambda (lambda (lambda (rev_fix_param (#(lambda (lambda (lambda (rev_select_set (lambda (eq? (tuple2_second \$0) \$3)) \$1 \$0)))) \$2 \$1 \$0) \$2 (lambda Const(color, 1))))))",
                        "#(lambda (tuple2_second (tuple2_second \$0)))",
                        "#(lambda (columns_to_grid (reverse \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) (map_set (lambda (tuple2 \$0 \$3)) (map_set (lambda (tuple2 \$0 \$2)) (map_set (lambda (tuple2_first \$0)) \$0))))))) \$1 Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (2, 0), (0, 1), (2, 2), (2, 1), (1, 0)])) \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0))))",
                        "#(lambda (#(lambda (lambda (columns_to_grid (concat \$1 \$0)))) \$0 \$0))",
                        "#(lambda (rows_to_grid (reverse (columns \$0))))",
                        "#(lambda (#(lambda (columns_to_grid (reverse \$0))) (rows \$0)))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$2 \$2) (\$1 \$0 \$0)))))",
                        "#(lambda (lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_select_grid (lambda (eq? \$0 \$3)) \$1 \$0)))) Const(color, 0) (repeat_grid Const(color, 0) \$2 \$2) (\$1 \$0 \$0))))) \$2 (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) \$3 \$1 \$0))) \$0))))",
                        "#(lambda (columns_to_grid (rows \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_first \$0)) (lambda (tuple2_second \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))",
                        "#(lambda (lambda (#(lambda (lambda (lambda (#(lambda (lambda (lambda (rev_grid_elements (#(lambda (lambda (lambda (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (\$7 (tuple2_first \$0)) (\$7 (tuple2_first \$2)))) 1)) (not (gt? (abs (- (\$6 (tuple2_first \$0)) (\$6 (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set (map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) \$0))))) (lambda (tuple2_second \$0)) (lambda (tuple2_first \$0)) \$2) \$1 \$0)))) (#(lambda (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) \$0)) \$2) \$1 \$0)))) \$1 \$0 \$0)))",
                        "#(lambda (lambda (repeat_grid \$1 \$0 \$0)))",
                    ],
                ),
            )
            hit, cost = test_build_manual_trace(task, target_solution, grammar3)
            @test !isnothing(hit)
        end
    end
end
