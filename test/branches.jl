
using solver:
    create_starting_context,
    ProgramBlock,
    FreeVar,
    add_new_block,
    BlockPrototype,
    enumeration_iteration_finished_output,
    unifying_expressions,
    empty_context,
    every_primitive,
    Apply,
    Hole,
    modify_skeleton,
    LeftTurn,
    RightTurn,
    number_of_free_parameters,
    follow_path,
    unwind_path,
    path_environment,
    apply_context,
    SetConst,
    Path,
    get_connected_from,
    get_connected_to,
    CombinedArgChecker,
    SimpleArgChecker,
    instantiate,
    EPSILON,
    _get_custom_arg_checkers,
    step_arg_checker,
    combine_arg_checkers

using DataStructures

@testset "Test branches" begin
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
    grammar = [
        parse_program(p) for p in [
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
        ]
    ]

    function initial_state(sc, branch_id, grammar)
        target_type_id = first(get_connected_from(sc.branch_types, branch_id))
        var_id = sc.branch_vars[branch_id]
        target_type = sc.types[target_type_id]
        context, target_type = instantiate(target_type, empty_context)
        entry_id = sc.branch_entries[branch_id]
        entry = sc.entries[entry_id]

        if !haskey(sc.entry_grammars, (entry_id, false))
            productions = Tuple{Program,Tp,Float64}[(p, p.t, 0.0) for p in grammar]
            g = Grammar(0.0, -3.0, -3.0, productions)
            sc.entry_grammars[(entry_id, false)] = make_dummy_contextual(g)
        end

        BlockPrototype(
            Hole(
                target_type,
                sc.unknown_var_locations[var_id],
                CombinedArgChecker([SimpleArgChecker(false, -1, true)]),
                entry.values,
            ),
            context,
            [],
            EPSILON,
            0,
            target_type,
            nothing,
            (var_id, branch_id),
            false,
        )
    end

    function next_state(sc, bp, target_candidate)
        current_hole = follow_path(bp.skeleton, bp.path)
        if !isa(current_hole, Hole)
            error("Error during following path")
        end
        request = current_hole.t

        context = bp.context
        context, request = apply_context(context, request)

        environment = path_environment(bp.path)

        bp_output_entry_id = sc.branch_entries[bp.output_var[2]]
        cg = sc.entry_grammars[(bp_output_entry_id, bp.reverse)]

        candidates = unifying_expressions(cg, environment, context, current_hole, bp.skeleton, bp.path)

        states = collect(
            skipmissing(
                map(candidates) do (candidate, argument_types, context, ll)
                    if candidate != target_candidate
                        return missing
                    end
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
                                Hole(argument_types[i], [(candidate, i)], arg_checker, nothing),
                            )
                        end
                        new_skeleton = modify_skeleton(bp.skeleton, application_template, bp.path)
                        new_path = vcat(bp.path, [LeftTurn() for _ in 2:length(argument_types)], [RightTurn()])
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
                end,
            ),
        )

        return states[1]
    end

    function create_block_prototype(sc, target_branch_id, steps, grammar)
        bp = initial_state(sc, target_branch_id, grammar)
        for step in steps
            bp = next_state(sc, bp, step)
        end

        return bp
    end

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

    @testcase_log "Exact value match" begin
        task = create_task(
            "copy",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[4, 4, 4, 4, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 4, 4, 4, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[1, 1, 1, 1, 1, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 1, 1, 1, 1, 1]),
                ),
                Dict{String,Any}("output" => Any[3, 3], "inputs" => Dict{String,Any}("inp0" => Any[3, 3])),
            ],
        )

        sc = create_starting_context(task, type_weights, hyperparameters, false)
        inp_var_id::UInt64 = 1
        out_var_id::UInt64 = 2
        inp_branch_id::UInt64 = 1
        out_branch_id::UInt64 = 2
        inp_type_id = first(get_connected_from(sc.branch_types, inp_branch_id))
        new_block = ProgramBlock(
            FreeVar(sc.types[inp_type_id], inp_var_id, nothing),
            sc.types[inp_type_id],
            0.0,
            [inp_var_id],
            out_var_id,
            false,
        )
        new_block_id = push!(sc.blocks, new_block)

        new_solution_paths =
            add_new_block(sc, new_block_id, Dict(inp_var_id => inp_branch_id), Dict(out_var_id => out_branch_id))
        @test new_solution_paths == Set([Path(OrderedDict(out_var_id => new_block_id), Dict(), 0.0)])

        @test isempty(get_connected_from(sc.branch_children, out_branch_id))

        @test sc.branch_is_explained[out_branch_id] == true
        @test sc.branch_is_not_copy[out_branch_id] == false
        @test sc.incoming_paths[out_branch_id] == Set([Path(OrderedDict(out_var_id => new_block_id), Dict(), 0.0)])
        @test length(get_connected_from(sc.branch_incoming_blocks, out_branch_id)) == 1
        @test sc.branch_incoming_blocks[out_branch_id, new_block_id] == 1
        @test length(get_connected_from(sc.branch_outgoing_blocks, out_branch_id)) == 0

        @test sc.unknown_min_path_costs[out_branch_id] == 0.0
        @test sc.explained_min_path_costs[out_branch_id] == 0.0
        @test sc.explained_complexity_factors[out_branch_id] == 16.0
        @test sc.unknown_complexity_factors[out_branch_id] == 16.0
        @test sc.complexities[out_branch_id] == 16.0
        @test sc.added_upstream_complexities[out_branch_id] == 0.0
        @test sc.unused_explained_complexities[out_branch_id] == 0.0
        @test sc.unmatched_complexities[out_branch_id] == 0.0
        @test isempty(get_connected_from(sc.related_unknown_complexity_branches, out_branch_id))
        @test isempty(get_connected_from(sc.related_explained_complexity_branches, out_branch_id))
    end

    @testcase_log "Type only match" begin
        task = create_task(
            "cdr",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[4, 4, 4, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 4, 4, 4, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[1, 1, 1, 1, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 1, 1, 1, 1, 1]),
                ),
                Dict{String,Any}("output" => Any[3], "inputs" => Dict{String,Any}("inp0" => Any[3, 3])),
            ],
        )

        sc = create_starting_context(task, type_weights, hyperparameters, false)
        inp_var_id::UInt64 = 1
        out_var_id::UInt64 = 2
        inp_branch_id::UInt64 = 1
        out_branch_id::UInt64 = 2
        inp_type_id = first(get_connected_from(sc.branch_types, inp_branch_id))
        out_type_id = first(get_connected_from(sc.branch_types, out_branch_id))

        bp = create_block_prototype(
            sc,
            out_branch_id,
            [every_primitive["cdr"], FreeVar(sc.types[out_type_id], nothing, (every_primitive["cdr"], 1))],
            grammar,
        )
        new_block_result, _ = enumeration_iteration_finished_output(sc, bp)
        @test length(new_block_result) == 1
        first_block_id, input_branches, target_output = new_block_result[1]
        new_solution_paths = add_new_block(sc, first_block_id, input_branches, target_output)
        first_block_copy_id = first_block_id
        @test new_solution_paths == Set([])

        connection_var_id::UInt64 = 3
        connection_branch_id::UInt64 = 3

        new_block = ProgramBlock(
            FreeVar(sc.types[inp_type_id], inp_var_id, nothing),
            sc.types[inp_type_id],
            0.0,
            [inp_var_id],
            connection_var_id,
            false,
        )
        new_block_id = push!(sc.blocks, new_block)

        new_solution_paths = add_new_block(
            sc,
            new_block_id,
            Dict(inp_var_id => inp_branch_id),
            Dict(connection_var_id => connection_branch_id),
        )
        @test new_solution_paths ==
              Set([Path(OrderedDict(out_var_id => first_block_id, connection_var_id => new_block_id), Dict(), 0.0)])
        new_block_copy_id = new_block_id

        conn_children = get_connected_from(sc.branch_children, connection_branch_id)
        @test length(conn_children) == 1
        conn_child_id = first(conn_children)
        first_block_known_copy_id = new_block_copy_id + 1

        @test sc.branch_entries[conn_child_id] == sc.branch_entries[inp_branch_id]
        @test sc.branch_vars[conn_child_id] == connection_var_id
        @test get_connected_from(sc.branch_types, conn_child_id) == get_connected_from(sc.branch_types, inp_branch_id)
        @test sc.incoming_paths[conn_child_id] ==
              Set([Path(OrderedDict(connection_var_id => new_block_id), Dict(), 0.0)])
        @test length(get_connected_from(sc.branch_incoming_blocks, conn_child_id)) == 1
        @test sc.branch_incoming_blocks[conn_child_id, new_block_copy_id] == new_block_id
        @test length(get_connected_from(sc.branch_outgoing_blocks, conn_child_id)) == 1
        @test sc.branch_outgoing_blocks[conn_child_id, first_block_known_copy_id] == first_block_id
        @test sc.branch_is_unknown[conn_child_id] == false
        @test sc.branch_is_explained[conn_child_id] == true
        @test sc.branch_is_not_copy[conn_child_id] == false
        @test sc.explained_min_path_costs[conn_child_id] == 0.0
        @test sc.explained_complexity_factors[conn_child_id] == 16.0
        @test sc.complexities[conn_child_id] == 16.0
        @test sc.added_upstream_complexities[conn_child_id] == 0.0
        @test sc.unused_explained_complexities[conn_child_id] == 0.0
        @test sc.unmatched_complexities[conn_child_id] === nothing
        @test isempty(get_connected_from(sc.related_unknown_complexity_branches, conn_child_id))
        @test isempty(get_connected_from(sc.related_explained_complexity_branches, conn_child_id))

        out_children = get_connected_from(sc.branch_children, out_branch_id)
        @test length(out_children) == 0

        @test sc.incoming_paths[out_branch_id] ==
              Set([Path(OrderedDict(out_var_id => first_block_id, connection_var_id => new_block_id), Dict(), 0.0)])
        @test length(get_connected_from(sc.branch_incoming_blocks, out_branch_id)) == 2
        @test sc.branch_incoming_blocks[out_branch_id, first_block_copy_id] == first_block_id
        @test sc.branch_incoming_blocks[out_branch_id, first_block_known_copy_id] == first_block_id
        @test length(get_connected_from(sc.branch_outgoing_blocks, out_branch_id)) == 0
        @test sc.branch_is_unknown[out_branch_id] == true
        @test sc.branch_is_explained[out_branch_id] == true
        @test sc.branch_is_not_copy[out_branch_id] == true
        @test sc.explained_min_path_costs[out_branch_id] == 7.8025402473842975
        @test sc.unknown_min_path_costs[out_branch_id] == 0.0
        @test sc.explained_complexity_factors[out_branch_id] == 13.0
        @test sc.unknown_complexity_factors[out_branch_id] == 13.0
        @test sc.complexities[out_branch_id] == 13.0
        @test sc.added_upstream_complexities[out_branch_id] == 0.0
        @test sc.unused_explained_complexities[out_branch_id] == 0.0
        @test sc.unmatched_complexities[out_branch_id] == 0.0
        @test isempty(get_connected_from(sc.related_unknown_complexity_branches, out_branch_id))
        @test isempty(get_connected_from(sc.related_explained_complexity_branches, out_branch_id))
    end

    @testcase_log "Either match" begin
        task = create_task(
            "concat",
            "inp0:list(int) -> list(int)",
            [
                Dict{String,Any}(
                    "output" => Any[5, 4, 4, 4, 4, 4],
                    "inputs" => Dict{String,Any}("inp0" => Any[4, 4, 4, 4, 4]),
                ),
                Dict{String,Any}(
                    "output" => Any[5, 1, 1, 1, 1, 1, 1],
                    "inputs" => Dict{String,Any}("inp0" => Any[1, 1, 1, 1, 1, 1]),
                ),
                Dict{String,Any}("output" => Any[5, 3, 3], "inputs" => Dict{String,Any}("inp0" => Any[3, 3])),
            ],
        )

        sc = create_starting_context(task, type_weights, hyperparameters, false)
        inp_var_id::UInt64 = 1
        out_var_id::UInt64 = 2
        inp_branch_id::UInt64 = 1
        out_branch_id::UInt64 = 2

        bp = create_block_prototype(sc, out_branch_id, [every_primitive["concat"]], grammar)
        new_block_result, _ = enumeration_iteration_finished_output(sc, bp)
        @test length(new_block_result) == 1
        first_block_id, input_branches, target_output = new_block_result[1]
        new_solution_paths = add_new_block(sc, first_block_id, input_branches, target_output)
        first_block_copy_id::UInt64 = 1
        @test new_solution_paths == Set([])

        v1_var_id::UInt64 = 3
        v2_var_id::UInt64 = 4

        v1_branch_id::UInt64 = 3
        v2_branch_id::UInt64 = 4

        constraint_id::UInt64 = 1
        @test sc.constrained_contexts[constraint_id] === nothing

        @test sc.branch_entries[v1_branch_id] == 3
        @test sc.branch_vars[v1_branch_id] == v1_var_id
        @test get_connected_from(sc.branch_types, v1_branch_id) == get_connected_from(sc.branch_types, inp_branch_id)
        @test isempty(get_connected_from(sc.branch_children, v1_branch_id))
        @test isempty(get_connected_to(sc.branch_children, v1_branch_id))
        @test length(get_connected_from(sc.constrained_branches, v1_branch_id)) == 1
        @test sc.constrained_branches[v1_branch_id, constraint_id] == v1_var_id
        @test length(get_connected_from(sc.constrained_vars, v1_var_id)) == 1
        @test sc.constrained_vars[v1_var_id, constraint_id] == v1_branch_id
        @test sc.incoming_paths[v1_branch_id] == Set([])
        @test length(get_connected_from(sc.branch_incoming_blocks, v1_branch_id)) == 0
        @test length(get_connected_from(sc.branch_outgoing_blocks, v1_branch_id)) == 1
        @test sc.branch_outgoing_blocks[v1_branch_id, first_block_copy_id] == first_block_id
        @test sc.branch_is_unknown[v1_branch_id] == true
        @test sc.branch_is_explained[v1_branch_id] == false
        @test sc.unknown_min_path_costs[v1_branch_id] == 2.49004698910567
        @test sc.unknown_complexity_factors[v1_branch_id] == 20.0
        @test sc.complexities[v1_branch_id] == 10.0
        @test sc.unmatched_complexities[v1_branch_id] == 10.0
        @test length(get_connected_from(sc.related_unknown_complexity_branches, v1_branch_id)) == 1
        @test sc.related_unknown_complexity_branches[v1_branch_id, v2_branch_id] == true

        @test sc.branch_entries[v2_branch_id] == 4
        @test sc.branch_vars[v2_branch_id] == v2_var_id
        @test get_connected_from(sc.branch_types, v2_branch_id) == get_connected_from(sc.branch_types, inp_branch_id)
        @test isempty(get_connected_from(sc.branch_children, v2_branch_id))
        @test isempty(get_connected_to(sc.branch_children, v2_branch_id))
        @test length(get_connected_from(sc.constrained_branches, v2_branch_id)) == 1
        @test sc.constrained_branches[v2_branch_id, constraint_id] == v2_var_id
        @test length(get_connected_from(sc.constrained_vars, v2_var_id)) == 1
        @test sc.constrained_vars[v2_var_id, constraint_id] == v2_branch_id
        @test sc.incoming_paths[v2_branch_id] == Set([])
        @test length(get_connected_from(sc.branch_incoming_blocks, v2_branch_id)) == 0
        @test length(get_connected_from(sc.branch_outgoing_blocks, v2_branch_id)) == 1
        @test sc.branch_outgoing_blocks[v2_branch_id, first_block_copy_id] == first_block_id
        @test sc.branch_is_unknown[v2_branch_id] == true
        @test sc.branch_is_explained[v2_branch_id] == false
        @test sc.unknown_min_path_costs[v2_branch_id] == 2.49004698910567
        @test sc.unknown_complexity_factors[v2_branch_id] == 20.0
        @test sc.complexities[v2_branch_id] == 10.0
        @test sc.unmatched_complexities[v2_branch_id] == 10.0
        @test length(get_connected_from(sc.related_unknown_complexity_branches, v2_branch_id)) == 1
        @test sc.related_unknown_complexity_branches[v2_branch_id, v1_branch_id] == true

        inp_type_id = first(get_connected_from(sc.branch_types, inp_branch_id))
        inp_type = sc.types[inp_type_id]

        new_block = ProgramBlock(FreeVar(inp_type, inp_var_id, nothing), inp_type, 0.0, [inp_var_id], v2_var_id, false)
        new_block_id = push!(sc.blocks, new_block)

        new_solution_paths =
            add_new_block(sc, new_block_id, Dict(inp_var_id => inp_branch_id), Dict(v2_var_id => v2_branch_id))
        new_block_copy_id::UInt64 = 3
        first_block_known_copy_id::UInt64 = 2
        @test new_solution_paths == Set()

        v2_children = get_connected_from(sc.branch_children, v2_branch_id)
        @test length(v2_children) == 1
        v2_child_id = first(v2_children)

        v1_children = get_connected_from(sc.branch_children, v1_branch_id)
        @test length(v1_children) == 1
        v1_child_id = first(v1_children)

        @test sc.branch_entries[v2_child_id] == sc.branch_entries[inp_branch_id]
        @test sc.branch_vars[v2_child_id] == v2_var_id
        @test get_connected_from(sc.branch_types, v2_child_id) == get_connected_from(sc.branch_types, inp_branch_id)
        @test isempty(get_connected_from(sc.branch_children, v2_child_id))
        @test length(get_connected_to(sc.branch_children, v2_child_id)) == 1
        @test sc.branch_children[v2_branch_id, v2_child_id] == true
        @test length(get_connected_from(sc.constrained_branches, v2_child_id)) == 0
        @test length(get_connected_from(sc.constrained_vars, v2_var_id)) == 1
        @test sc.incoming_paths[v2_child_id] == Set([Path(OrderedDict(v2_var_id => new_block_id), Dict(), 0.0)])
        @test length(get_connected_from(sc.branch_incoming_blocks, v2_child_id)) == 1
        @test sc.branch_incoming_blocks[v2_child_id, new_block_copy_id] == new_block_id
        @test length(get_connected_from(sc.branch_outgoing_blocks, v2_child_id)) == 1
        @test sc.branch_outgoing_blocks[v2_child_id, first_block_known_copy_id] == first_block_id
        @test sc.branch_is_unknown[v2_child_id] == false
        @test sc.branch_is_explained[v2_child_id] == true
        @test sc.branch_is_not_copy[v2_child_id] == false
        @test sc.explained_min_path_costs[v2_child_id] == 0.0
        @test sc.explained_complexity_factors[v2_child_id] == 16.0
        @test sc.complexities[v2_child_id] == 16.0
        @test sc.added_upstream_complexities[v2_child_id] == 0.0
        @test sc.unused_explained_complexities[v2_child_id] == 0.0
        @test sc.unmatched_complexities[v2_child_id] == 0.0
        @test isempty(get_connected_from(sc.related_explained_complexity_branches, v2_child_id))
        @test isempty(get_connected_from(sc.related_unknown_complexity_branches, v2_child_id))

        @test sc.branch_entries[v1_child_id] == 5
        @test sc.branch_vars[v1_child_id] == v1_var_id
        @test get_connected_from(sc.branch_types, v1_child_id) == get_connected_from(sc.branch_types, inp_branch_id)
        @test isempty(get_connected_from(sc.branch_children, v1_child_id))
        @test length(get_connected_to(sc.branch_children, v1_child_id)) == 1
        @test sc.branch_children[v1_branch_id, v1_child_id] == true
        @test length(get_connected_from(sc.constrained_branches, v1_child_id)) == 0
        @test length(get_connected_from(sc.constrained_vars, v1_var_id)) == 1
        @test sc.incoming_paths[v1_child_id] == Set([])
        @test length(get_connected_from(sc.branch_incoming_blocks, v1_child_id)) == 0
        @test length(get_connected_from(sc.branch_outgoing_blocks, v1_child_id)) == 1
        @test sc.branch_outgoing_blocks[v1_child_id, first_block_known_copy_id] == first_block_id
        @test sc.branch_is_unknown[v1_child_id] == true
        @test sc.branch_is_explained[v1_child_id] == false
        @test sc.branch_is_not_copy[v1_child_id] == false
        @test sc.unknown_min_path_costs[v1_child_id] == 2.49004698910567
        @test sc.unknown_complexity_factors[v1_child_id] == 6.0
        @test sc.complexities[v1_child_id] == 6.0
        @test sc.unmatched_complexities[v1_child_id] == 6.0
        @test length(get_connected_from(sc.related_unknown_complexity_branches, v1_child_id)) == 1
        @test sc.related_unknown_complexity_branches[v1_child_id, v2_child_id] == true

        const_block = ProgramBlock(SetConst(inp_type, [5]), inp_type, 0.0, [], v1_var_id, false)
        const_block_id = push!(sc.blocks, const_block)
        new_solution_paths = add_new_block(sc, const_block_id, Dict{UInt64,UInt64}(), Dict(v1_var_id => v1_branch_id))
        const_block_copy_id::UInt64 = 4

        @test new_solution_paths == Set([
            Path(
                OrderedDict(out_var_id => first_block_id, v2_var_id => new_block_id, v1_var_id => const_block_id),
                Dict(),
                0.0,
            ),
        ])

        @test isempty(get_connected_from(sc.branch_children, v2_child_id))
        @test length(get_connected_from(sc.constrained_branches, v2_child_id)) == 0

        @test length(get_connected_from(sc.constrained_vars, v2_var_id)) == 1
        @test sc.incoming_paths[v2_child_id] == Set([Path(OrderedDict(v2_var_id => new_block_id), Dict(), 0.0)])
        @test length(get_connected_from(sc.branch_incoming_blocks, v2_child_id)) == 1
        @test sc.branch_incoming_blocks[v2_child_id, new_block_copy_id] == new_block_id
        @test length(get_connected_from(sc.branch_outgoing_blocks, v2_child_id)) == 1
        @test sc.branch_outgoing_blocks[v2_child_id, first_block_known_copy_id] == first_block_id
        @test sc.branch_is_unknown[v2_child_id] == false
        @test sc.branch_is_explained[v2_child_id] == true
        @test sc.branch_is_not_copy[v2_child_id] == false
        @test sc.unknown_min_path_costs[v2_child_id] === nothing
        @test sc.unknown_complexity_factors[v2_child_id] === nothing
        @test sc.complexities[v2_child_id] == 16.0
        @test sc.added_upstream_complexities[v2_child_id] == 0.0
        @test sc.unused_explained_complexities[v2_child_id] == 0.0
        @test sc.unmatched_complexities[v2_child_id] == 0.0
        @test isempty(get_connected_from(sc.related_explained_complexity_branches, v2_child_id))
        @test isempty(get_connected_from(sc.related_unknown_complexity_branches, v2_child_id))

        @test isempty(get_connected_from(sc.branch_children, v1_child_id))
        @test length(get_connected_to(sc.branch_children, v1_child_id)) == 1
        @test sc.branch_children[v1_branch_id, v1_child_id] == true
        @test length(get_connected_from(sc.constrained_vars, v1_var_id)) == 1
        @test sc.incoming_paths[v1_child_id] == Set([Path(OrderedDict(v1_var_id => const_block_id), Dict(), 0.0)])
        @test length(get_connected_from(sc.branch_incoming_blocks, v1_child_id)) == 1
        @test sc.branch_incoming_blocks[v1_child_id, const_block_copy_id] == const_block_id
        @test length(get_connected_from(sc.branch_outgoing_blocks, v1_child_id)) == 1
        @test sc.branch_outgoing_blocks[v1_child_id, first_block_known_copy_id] == first_block_id
        @test sc.branch_is_unknown[v1_child_id] == true
        @test sc.branch_is_explained[v1_child_id] == true
        @test sc.branch_is_not_copy[v1_child_id] == true
        @test sc.unknown_min_path_costs[v1_child_id] == 2.49004698910567
        @test sc.explained_min_path_costs[v1_child_id] === nothing
        @test sc.unknown_complexity_factors[v1_child_id] == 6.0
        @test sc.explained_complexity_factors[v1_child_id] == 16.0
        @test sc.complexities[v1_child_id] == 6.0
        @test sc.added_upstream_complexities[v1_child_id] == 10.0
        @test sc.unused_explained_complexities[v1_child_id] == 0.0
        @test sc.unmatched_complexities[v1_child_id] == 0.0
        @test length(get_connected_from(sc.related_unknown_complexity_branches, v1_child_id)) == 1
        @test sc.related_unknown_complexity_branches[v1_child_id, v2_child_id] == true
        @test isempty(get_connected_from(sc.related_explained_complexity_branches, v1_child_id))

        @test isempty(get_connected_from(sc.branch_children, out_branch_id))

        @test length(get_connected_from(sc.constrained_branches, out_branch_id)) == 0
        @test length(get_connected_from(sc.constrained_vars, out_var_id)) == 0
        @test sc.incoming_paths[out_branch_id] == Set([
            Path(
                OrderedDict(out_var_id => first_block_id, v2_var_id => new_block_id, v1_var_id => const_block_id),
                Dict(),
                0.0,
            ),
        ])
        @test length(get_connected_from(sc.branch_incoming_blocks, out_branch_id)) == 2
        @test sc.branch_incoming_blocks[out_branch_id, first_block_copy_id] == first_block_id
        @test sc.branch_incoming_blocks[out_branch_id, first_block_known_copy_id] == first_block_id
        @test length(get_connected_from(sc.branch_outgoing_blocks, out_branch_id)) == 0
        @test sc.branch_is_unknown[out_branch_id] == true
        @test sc.branch_is_explained[out_branch_id] == true
        @test sc.branch_is_not_copy[out_branch_id] == true
        @test sc.explained_min_path_costs[out_branch_id] == 2.49004698910567
        @test sc.explained_complexity_factors[out_branch_id] == 29.0
        @test sc.complexities[out_branch_id] == 19.0
        @test sc.added_upstream_complexities[out_branch_id] == 10.0
        @test sc.unused_explained_complexities[out_branch_id] == 0.0
        @test sc.unmatched_complexities[out_branch_id] == 0.0
        @test isempty(get_connected_from(sc.related_unknown_complexity_branches, out_branch_id))
        @test isempty(get_connected_from(sc.related_explained_complexity_branches, out_branch_id))
    end
end
