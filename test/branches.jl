
include("../src/solver.jl")

using Test

using solver:
    load_problems,
    create_starting_context,
    ProgramBlock,
    FreeVar,
    add_new_block,
    RedisContext,
    EntryBranch,
    BlockPrototype,
    EnumerationState,
    enumeration_iteration_finished_output,
    unifying_expressions,
    empty_context,
    every_primitive,
    tint,
    tlist,
    get_argument_requests,
    Apply,
    Hole,
    modify_skeleton,
    LeftTurn,
    RightTurn,
    ArgTurn,
    Tp,
    Context,
    block_prototype,
    number_of_free_parameters,
    follow_path,
    unwind_path,
    path_environment,
    apply_context,
    get_entry,
    Constraint,
    SetConst

import Redis
using DataStructures

function initial_state(branch, g)
    EnumerationState(Hole(branch.type, g.no_context), empty_context, [], 0.0, 0, false)
end

function next_state(state, target_candidate, cg)
    current_hole = follow_path(state.skeleton, state.path)
    if !isa(current_hole, Hole)
        error("Error during following path")
    end
    request = current_hole.t
    g = current_hole.grammar

    context = state.context
    context, request = apply_context(context, request)

    environment = path_environment(state.path)
    candidates = unifying_expressions(g, environment, request, context, state.abstractors_only)
    if !isa(state.skeleton, Hole)
        push!(candidates, (FreeVar(request, nothing), [], context, g.log_variable))
    end

    states = collect(
        skipmissing(
            map(candidates) do (candidate, argument_types, context, ll)
                if candidate != target_candidate
                    return missing
                end
                new_free_parameters = number_of_free_parameters(candidate)
                argument_requests = get_argument_requests(candidate, argument_types, cg)

                if isempty(argument_types)
                    new_skeleton = modify_skeleton(state.skeleton, candidate, state.path)
                    new_path = unwind_path(state.path, new_skeleton)
                else
                    application_template = candidate
                    for (a, at) in argument_requests
                        application_template = Apply(application_template, Hole(a, at))
                    end
                    new_skeleton = modify_skeleton(state.skeleton, application_template, state.path)
                    new_path = vcat(state.path, [LeftTurn() for _ = 2:length(argument_types)], [RightTurn()])
                end
                return EnumerationState(
                    new_skeleton,
                    context,
                    new_path,
                    state.cost + ll,
                    state.free_parameters + new_free_parameters,
                    state.abstractors_only,
                )
            end,
        ),
    )

    return states[1]
end

function create_block_prototype(target_branch, steps, g)
    state = initial_state(target_branch, g)
    for step in steps
        state = next_state(state, step, g)
    end

    bp = BlockPrototype(state, target_branch.type, nothing, (target_branch.key, target_branch), false)
    return bp
end

@testset "Test branches" begin
    base_task = Dict(
        "DSL" => Dict{String,Any}(
            "logVariable" => 0.0,
            "productions" => Any[
                Dict{String,Any}("logProbability" => 0.0, "expression" => "map"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "unfold"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "range"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "index"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "fold"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "length"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "if"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "+"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "-"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "empty"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "cons"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "car"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "cdr"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "empty?"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "0"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "1"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "*"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "mod"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "gt?"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "eq?"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "is-prime"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "is-square"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "repeat"),
                Dict{String,Any}("logProbability" => 0.0, "expression" => "concat"),
            ],
        ),
        "type_weights" => Dict{String,Any}("list" => 1.0, "int" => 1.0, "bool" => 1.0, "float" => 1.0),
        "programTimeout" => 1,
        "timeout" => 20,
        "verbose" => false,
        "shatter" => 10,
    )
    run_context = Dict("redis" => RedisContext(Redis.RedisConnection(db = 2)), "program_timeout" => 1, "timeout" => 20)

    @testset "Exact value match" begin
        payload = merge(
            base_task,
            Dict(
                "task" => Dict{String,Any}(
                    "name" => "copy",
                    "maximumFrontier" => 10,
                    "examples" => Any[
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
                    "test_examples" => Any[],
                    "request" => Dict{String,Any}(
                        "arguments" => Dict{String,Any}(
                            "inp0" => Dict{String,Any}(
                                "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                                "constructor" => "list",
                            ),
                        ),
                        "output" => Dict{String,Any}(
                            "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                            "constructor" => "list",
                        ),
                        "constructor" => "->",
                    ),
                ),
                "name" => "copy",
            ),
        )
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        sc = create_starting_context(task, type_weights)
        inp_branch = sc.var_data["inp0"]
        out_branch = sc.var_data["out"]
        new_block = ProgramBlock(
            FreeVar(inp_branch.type, "inp0"),
            inp_branch.type,
            0.0,
            [("inp0", inp_branch)],
            ("out", out_branch),
            false,
        )

        new_solution_paths = add_new_block(run_context, sc, new_block, Dict("inp0" => inp_branch))
        @test new_solution_paths == [OrderedDict("out" => new_block)]
        @test length(out_branch.children) == 1
        @test first(out_branch.children) == EntryBranch(
            1,
            "out",
            out_branch.type,
            Set([out_branch]),
            Set(),
            Set(),
            [OrderedDict("out" => new_block)],
            Set([new_block]),
            Set(),
            true,
            false,
            0.0,
            16.0,
            16.0,
            0.0,
            16.0,
            0.0,
            Set(),
        )
    end

    @testset "Type only match" begin
        payload = merge(
            base_task,
            Dict(
                "task" => Dict{String,Any}(
                    "name" => "cdr",
                    "maximumFrontier" => 10,
                    "examples" => Any[
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
                    "test_examples" => Any[],
                    "request" => Dict{String,Any}(
                        "arguments" => Dict{String,Any}(
                            "inp0" => Dict{String,Any}(
                                "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                                "constructor" => "list",
                            ),
                        ),
                        "output" => Dict{String,Any}(
                            "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                            "constructor" => "list",
                        ),
                        "constructor" => "->",
                    ),
                ),
                "name" => "cdr",
            ),
        )
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        sc = create_starting_context(task, type_weights)
        inp_branch = sc.var_data["inp0"]
        out_branch = sc.var_data["out"]

        bp = create_block_prototype(out_branch, [every_primitive["cdr"], FreeVar(out_branch.type, nothing)], g)
        new_block_result = enumeration_iteration_finished_output(run_context, sc, bp)
        first_block, input_branches = new_block_result
        new_solution_paths = add_new_block(run_context, sc, first_block, input_branches)
        @test new_solution_paths == []

        connection_branch = sc.var_data["v1"]

        new_block = ProgramBlock(
            FreeVar(inp_branch.type, "inp0"),
            inp_branch.type,
            0.0,
            [("inp0", inp_branch)],
            ("v1", connection_branch),
            false,
        )

        new_solution_paths = add_new_block(run_context, sc, new_block, Dict("inp0" => inp_branch))
        @test new_solution_paths == [OrderedDict("out" => first_block, "v1" => new_block)]
        @test length(connection_branch.children) == 1
        @test first(connection_branch.children) == EntryBranch(
            inp_branch.value_index,
            "v1",
            inp_branch.type,
            Set([connection_branch]),
            Set(),
            Set(),
            [OrderedDict("v1" => new_block)],
            Set([new_block]),
            Set([first_block]),
            true,
            false,
            0.0,
            16.0,
            16.0,
            0.0,
            16.0,
            0.0,
            Set(),
        )
        @test length(out_branch.children) == 1
        @test first(out_branch.children) == EntryBranch(
            out_branch.value_index,
            "out",
            out_branch.type,
            Set([out_branch]),
            Set(),
            Set(),
            [OrderedDict("out" => first_block, "v1" => new_block)],
            Set([first_block]),
            Set(),
            true,
            true,
            2.4849066497880004,
            13.0,
            13.0,
            0.0,
            13.0,
            0.0,
            Set(),
        )
    end

    @testset "Either match" begin
        payload = merge(
            base_task,
            Dict(
                "task" => Dict{String,Any}(
                    "name" => "concat",
                    "maximumFrontier" => 10,
                    "examples" => Any[
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
                    "test_examples" => Any[],
                    "request" => Dict{String,Any}(
                        "arguments" => Dict{String,Any}(
                            "inp0" => Dict{String,Any}(
                                "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                                "constructor" => "list",
                            ),
                        ),
                        "output" => Dict{String,Any}(
                            "arguments" => Any[Dict{String,Any}("arguments" => Any[], "constructor" => "int")],
                            "constructor" => "list",
                        ),
                        "constructor" => "->",
                    ),
                ),
                "name" => "concat",
            ),
        )
        task, maximum_frontier, g, type_weights, _mfp, _nc, timeout, verbose, program_timeout = load_problems(payload)
        sc = create_starting_context(task, type_weights)
        inp_branch = sc.var_data["inp0"]
        out_branch = sc.var_data["out"]

        bp = create_block_prototype(out_branch, [every_primitive["concat"]], g)
        new_block_result = enumeration_iteration_finished_output(run_context, sc, bp)
        first_block, input_branches = new_block_result
        new_solution_paths = add_new_block(run_context, sc, first_block, input_branches)
        @test new_solution_paths == []

        v2_branch = sc.var_data["v2"]
        v1_branch = sc.var_data["v1"]

        @test v2_branch == EntryBranch(
            4,
            "v2",
            inp_branch.type,
            Set(),
            Set(),
            Set([Constraint(Dict("v1" => v1_branch, "v2" => v2_branch), Dict(), Dict())]),
            [],
            Set(),
            Set([first_block]),
            false,
            false,
            2.4849066497880004,
            38.0,
            19.0,
            0.0,
            19.0,
            19.0,
            Set([v1_branch]),
        )
        @test v1_branch == EntryBranch(
            3,
            "v1",
            inp_branch.type,
            Set(),
            Set(),
            Set([Constraint(Dict("v1" => v1_branch, "v2" => v2_branch), Dict(), Dict())]),
            [],
            Set(),
            Set([first_block]),
            false,
            false,
            2.4849066497880004,
            38.0,
            19.0,
            0.0,
            19.0,
            19.0,
            Set([v2_branch]),
        )

        new_block = ProgramBlock(
            FreeVar(inp_branch.type, "inp0"),
            inp_branch.type,
            0.0,
            [("inp0", inp_branch)],
            ("v2", v2_branch),
            false,
        )

        new_solution_paths = add_new_block(run_context, sc, new_block, Dict("inp0" => inp_branch))
        @test new_solution_paths == []

        @test length(v2_branch.children) == 1
        v2_known_child = first(v2_branch.children)
        v1_unknown_child = first(v1_branch.children)
        @info v2_known_child
        @test v2_known_child == EntryBranch(
            inp_branch.value_index,
            "v2",
            inp_branch.type,
            Set([v2_branch]),
            Set(),
            Set([Constraint(Dict("v1" => v1_unknown_child, "v2" => v2_known_child), Dict(), Dict())]),
            [OrderedDict("v2" => new_block)],
            Set([new_block]),
            Set([first_block]),
            true,
            false,
            0.0,
            16.0,
            16.0,
            0.0,
            16.0,
            0.0,
            Set(),
        )
        @test length(v1_branch.children) == 1
        @info v1_unknown_child
        @test v1_unknown_child == EntryBranch(
            5,
            "v1",
            inp_branch.type,
            Set([v1_branch]),
            Set(),
            Set([Constraint(Dict("v1" => v1_unknown_child, "v2" => v2_known_child), Dict(), Dict())]),
            [],
            Set(),
            Set([first_block]),
            false,
            false,
            0.0,
            16.0,
            16.0,
            0.0,
            16.0,
            0.0,
            Set([v2_known_child]),
        )

        const_block = ProgramBlock(SetConst(inp_branch.type, [5]), inp_branch.type, 0.0, [], ("v1", v1_branch), false)
        new_solution_paths = add_new_block(run_context, sc, const_block, Dict())

        @test length(v1_unknown_child.children) == 1
        v1_known_child = first(v1_unknown_child.children)
        v2_unknown_child = first(v2_branch.children)
        @test v2_known_child.parents == Set([v2_unknown_child])
        @test v2_branch.children == Set([v2_unknown_child])
        @test v1_known_child == EntryBranch(
            5,
            "v1",
            inp_branch.type,
            Set([v1_unknown_child]),
            Set(),
            Set([
                Constraint(Dict("v1" => v1_known_child, "v2" => v2_unknown_child), Dict(), Dict()),
                Constraint(Dict("v1" => v1_known_child, "v2" => v2_known_child), Dict(), Dict()),
            ]),
            [OrderedDict("v1" => const_block)],
            Set([const_block]),
            Set([first_block]),
            true,
            true,
            0.0,
            16.0,
            16.0,
            0.0,
            16.0,
            0.0,
            Set(),
        )
        @test v2_unknown_child == EntryBranch(
            inp_branch.value_index,
            "v2",
            inp_branch.type,
            Set([v2_branch]),
            Set([v2_known_child]),
            Set([Constraint(Dict("v1" => v1_known_child, "v2" => v2_unknown_child), Dict(), Dict())]),
            [],
            Set(),
            Set([first_block]),
            false,
            false,
            0.0,
            16.0,
            16.0,
            0.0,
            16.0,
            0.0,
            Set([v1_known_child]),
        )
        @test v2_known_child.constraints == Set([
            Constraint(Dict("v1" => v1_unknown_child, "v2" => v2_known_child), Dict(), Dict()),
            Constraint(Dict("v1" => v1_known_child, "v2" => v2_known_child), Dict(), Dict()),
        ])

        @test new_solution_paths == [OrderedDict("out" => first_block, "v2" => new_block, "v1" => const_block)]

        @test length(out_branch.children) == 1
        @test first(out_branch.children) == EntryBranch(
            out_branch.value_index,
            "out",
            out_branch.type,
            Set([out_branch]),
            Set(),
            Set(),
            [OrderedDict("out" => first_block, "v2" => new_block, "v1" => const_block)],
            Set([first_block]),
            Set(),
            true,
            true,
            0.0,
            16.0,
            16.0,
            0.0,
            16.0,
            0.0,
            Set(),
        )
    end
end
