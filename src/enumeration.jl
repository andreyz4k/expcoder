
using DataStructures


get_enumeration_timeout(timeout) = time() + timeout
enumeration_timed_out(timeout) = time() > timeout

abstract type Entry end

struct ValueEntry <: Entry
    type::Tp
    values::Vector
end

get_matching_seq(entry::ValueEntry) = [(rv -> rv == v ? Strict : NoMatch) for v in entry.values]

match_with_task_val(entry::ValueEntry, other::ValueEntry, key) =
    if entry.type == other.type && entry.values == other.values
        (key, Strict, copy_field)
    else
        missing
    end

struct NoDataEntry <: Entry
    type::Tp
end

get_matching_seq(entry::NoDataEntry) = Iterators.repeated(_ -> TypeOnly)
match_with_task_val(entry::NoDataEntry, other::ValueEntry, key) =
    entry.type == other.type ? (key, TypeOnly, copy_field) : missing

abstract type Turn end

struct LeftTurn <: Turn end
struct RightTurn <: Turn end
struct ArgTurn <: Turn
    type::Tp
end

struct EnumerationState
    skeleton::Program
    context::Context
    path::Vector{Turn}
    cost::Float64
    free_parameters::Int64
end


struct BlockPrototype
    state::EnumerationState
    input_vals::Vector{String}
    output_vals::Vector{String}
end

mutable struct SolutionBranch
    known_vars::Dict{String,ValueEntry}
    unknown_vars::Dict{String,Entry}
    fill_percentages::Dict{String,Float64}
    operations::Vector{ProgramBlock}
    parent::Union{Nothing,SolutionBranch}
    children::Vector{SolutionBranch}
    example_count::Int64
    created_vars::Int64
    ops_by_input::MultiDict{String,ProgramBlock}
    ops_by_output::MultiDict{String,ProgramBlock}
end


function create_start_solution(task::Task)::SolutionBranch
    known_vars = Dict{String,ValueEntry}()
    fill_percentages = Dict{String,Float64}()
    argument_types = arguments_of_type(task.task_type)
    for (i, (t, values)) in enumerate(zip(argument_types, zip(task.train_inputs...)))
        key = "\$$i"
        known_vars[key] = ValueEntry(t, collect(values))
        fill_percentages[key] = 1.0
    end
    unknown_vars = Dict{String,Entry}("out" => ValueEntry(return_of_type(task.task_type), task.train_outputs))
    fill_percentages["out"] = 0.0
    example_count = length(task.train_outputs)
    SolutionBranch(
        known_vars,
        unknown_vars,
        fill_percentages,
        [],
        nothing,
        [],
        example_count,
        0,
        MultiDict{String,ProgramBlock}(),
        MultiDict{String,ProgramBlock}(),
    )
end

function create_next_var(solution_ctx)
    solution_ctx.created_vars += 1
    solution_ctx.created_vars - 1
end

iter_unknown_vars(solution_ctx) = solution_ctx.unknown_vars

primitive_unknown(t, g) = Primitive("??", t, g; skip_saving = true)

initial_enumeration_state(request, g::Grammar) =
    EnumerationState(primitive_unknown(request, g), empty_context, [], 0.0, 0)


initial_block_prototype(request, g::Grammar, inputs, outputs) =
    BlockPrototype(initial_enumeration_state(request, g), inputs, outputs)


get_candidates_for_unknown_var(sol_ctx, key, value, g) = [initial_block_prototype(value.type, g.no_context, [], [key])]


get_argument_requests(::Index, argument_types, cg) = [(at, cg.variable_context) for at in argument_types]
get_argument_requests(candidate::Primitive, argument_types, cg) =
    if candidate.name == "FREE_VAR"
        []
    else
        invoke(get_argument_requests, Tuple{Any,Any,Any}, candidate, argument_types, cg)
    end

get_argument_requests(candidate, argument_types, cg) = zip(argument_types, cg.contextual_library[candidate])


follow_path(skeleton::Apply, path) =
    if isa(path[1], LeftTurn)
        follow_path(skeleton.f, view(path, 2:length(path)))
    elseif isa(path[1], RightTurn)
        follow_path(skeleton.x, view(path, 2:length(path)))
    else
        error("Wrong path")
    end

follow_path(skeleton::Abstraction, path) =
    if isa(path[1], ArgTurn)
        follow_path(skeleton.b, view(path, 2:length(path)))
    else
        error("Wrong path")
    end

follow_path(skeleton::Primitive, path) =
    if skeleton.name == "??" && isempty(path)
        skeleton
    else
        error("Wrong path")
    end

follow_path(::Any, path) = error("Wrong path")

path_environment(path) = reverse([t.type for t in path if isa(t, ArgTurn)])

modify_skeleton(skeleton::Abstraction, template, path) =
    if isa(path[1], ArgTurn)
        Abstraction(modify_skeleton(skeleton.b, template, view(path, 2:length(path))))
    else
        error("Wrong path")
    end

modify_skeleton(skeleton::Primitive, template, path) =
    if skeleton.name == "??" && isempty(path)
        template
    else
        error("Wrong path")
    end

modify_skeleton(skeleton::Apply, template, path) =
    if isa(path[1], LeftTurn)
        Apply(modify_skeleton(skeleton.f, template, view(path, 2:length(path))), skeleton.x)
    elseif isa(path[1], RightTurn)
        Apply(skeleton.f, modify_skeleton(skeleton.x, template, view(path, 2:length(path))))
    else
        error("Wrong path")
    end


function unwind_path(path)
    k = length(path)
    while k > 0
        if isa(path[k], LeftTurn)
            break
        end
        k -= 1
    end
    if k > 0
        vcat(path[1:k-1], [RightTurn()])
    else
        []
    end
end

violates_symmetry(::Program, a, n) = false
function violates_symmetry(f::Primitive, a, n)
    a = application_function(a)
    if !isa(a, Primitive)
        return false
    end
    return in(
        (n, f.name, a.name),
        Set([
            #  McCarthy primitives
            (0, "car", "cons"),
            (0, "car", "empty"),
            (0, "cdr", "cons"),
            (0, "cdr", "empty"),
            (1, "-", "0"),
            (0, "+", "+"),
            (0, "*", "*"),
            (0, "empty?", "cons"),
            (0, "empty?", "empty"),
            (0, "zero?", "0"),
            (0, "zero?", "1"),
            (0, "zero?", "-1"),
            #  bootstrap target
            (1, "map", "empty"),
            (0, "fold", "empty"),
            (1, "index", "empty"),
        ]),
    ) || in(
        (f.name, a.name),
        Set([
            ("+", "0"),
            ("*", "0"),
            ("*", "1"),
            ("zip", "empty"),
            ("left", "left"),
            ("left", "right"),
            ("right", "right"),
            ("right", "left"),
            #   ("tower_embed","tower_embed")
        ]),
    )
end


block_state_violates_symmetry(state::EnumerationState) =
    if isa(state.skeleton, Primitive) && state.skeleton.name == "FREE_VAR"
        true
    else
        state_violates_symmetry(state.skeleton)
    end

state_violates_symmetry(p::Abstraction) = state_violates_symmetry(p.b)
function state_violates_symmetry(p::Apply)
    (f, a) = application_parse(p)
    return state_violates_symmetry(f) ||
           any(state_violates_symmetry, a) ||
           any(violates_symmetry(f, x, n) for (n, x) in enumerate(a))
end
state_violates_symmetry(::Program) = false





function block_state_successors(
    maxFreeParameters,
    cg::ContextualGrammar,
    state::EnumerationState,
)::Vector{EnumerationState}
    current_hole = follow_path(state.skeleton, state.path)
    if !isa(current_hole, Primitive) || current_hole.name != "??"
        error("Error during following path")
    end
    request = current_hole.t
    g = current_hole.code

    context = state.context
    context, request = apply_context(context, request)
    if isarrow(request)
        return [
            EnumerationState(
                modify_skeleton(state.skeleton, (Abstraction(primitive_unknown(request.arguments[2], g))), state.path),
                context,
                vcat(state.path, [ArgTurn(request.arguments[1])]),
                state.cost,
                state.free_parameters,
            ),
        ]
    else
        environment = path_environment(state.path)
        candidates = unifying_expressions(g, environment, request, context)
        push!(
            candidates,
            (Primitive("FREE_VAR", request, length(environment); skip_saving = true), [], context, g.log_variable),
        )

        states = map(candidates) do (candidate, argument_types, context, ll)
            new_free_parameters = number_of_free_parameters(candidate)
            argument_requests = get_argument_requests(candidate, argument_types, cg)

            if isempty(argument_types)
                return EnumerationState(
                    modify_skeleton(state.skeleton, candidate, state.path),
                    context,
                    unwind_path(state.path),
                    state.cost - ll,
                    state.free_parameters + new_free_parameters,
                )
            else
                application_template = candidate
                for (a, at) in argument_requests
                    application_template = Apply(application_template, primitive_unknown(a, at))
                end
                return EnumerationState(
                    modify_skeleton(state.skeleton, application_template, state.path),
                    context,
                    vcat(state.path, [LeftTurn() for _ = 2:length(argument_types)], [RightTurn()]),
                    state.cost - ll,
                    state.free_parameters + new_free_parameters,
                )
            end

        end
        return filter(
            (new_state -> !block_state_violates_symmetry(new_state) && new_state.free_parameters <= maxFreeParameters),
            states,
        )
    end

end

state_finished(state::EnumerationState) =
    if isa(state.skeleton, Primitive) && state.skeleton.name == "??"
        false
    else
        isempty(state.path)
    end

function replace_free_vars(p::Apply, captured, types)
    f, captured, types = replace_free_vars(p.f, captured, types)
    x, captured, types = replace_free_vars(p.x, captured, types)
    (Apply(f, x), captured, types)
end

function replace_free_vars(p::Abstraction, captured, types)
    b, captured, types = replace_free_vars(p.b, captured, types)
    (Abstraction(b), captured, types)
end

replace_free_vars(p::Primitive, captured, types) =
    if p.name == "FREE_VAR"
        (Index(p.code + captured), captured + 1, vcat([p.t], types))
    else
        (p, captured, types)
    end
replace_free_vars(p::Program, captured, types) = (p, captured, types)

function capture_free_vars(p)
    p, free_c, ts = replace_free_vars(p, 0, [])
    for _ = 1:free_c
        p = Abstraction(p)
    end
    (p, ts)
end

function try_evaluate_program(p, xs)
    try
        [run_analyzed_with_arguments(p, xs)]
        #    TODO: allow several return values from the block s
    catch e
        #  We have to be a bit careful with exceptions if the
        #     synthesized program generated an exception, then we just
        #     terminate w/ false but if the enumeration timeout was
        #     triggered during program evaluation, we need to pass the
        #     exception on
        if isa(e, UnknownPrimitive)
            error("Unknown primitive: $(e.name)")
        else
            return nothing
        end
    end
end

function try_run_block(sc::SolutionBranch, block::ProgramBlock, inputs)
    input_vals = zip(inputs...)
    expected_outputs = [sc.unknown_vars[k] for k in block.outputs]

    out_matchers = zip([get_matching_seq(exp) for exp in expected_outputs]...)

    p = analyze_evaluation(block.p)

    bm = Strict
    outs = []
    for (xs, matchers) in zip(input_vals, out_matchers)
        v = try_evaluate_program(p, xs)
        if isnothing(v)
            return NoMatch, []
        end
        for (out_value, matcher) in zip(v, matchers)
            m = matcher(out_value)
            if m == NoMatch
                return NoMatch, []
            else
                bm = min(bm, m)
            end
        end
        push!(outs, v)
    end
    return bm, zip(outs...)
end

function try_run_block_with_downstream(sc::SolutionBranch, block::ProgramBlock)
    blocks = Queue{ProgramBlock}()
    enqueue!(blocks, block)
    bm = Strict
    outs = Dict()
    while !isempty(blocks)
        bl = dequeue!(blocks)
        if any(!haskey(outs, key) && !haskey(sc.known_vars, key) for key in bl.inputs)
            continue
        end
        inputs = [haskey(outs, key) ? outs[key] : sc.known_vars[key].values for key in bl.inputs]
        mv, outputs = try_run_block(sc, bl, inputs)
        if mv == NoMatch
            return (NoMatch, nothing)
        else
            for (key, out_values) in zip(bl.outputs, outputs)
                outs[key] = out_values
                for b in sc.ops_by_input[key]
                    enqueue!(blocks, b)
                end
            end
            bm = min(mv, bm)
        end
    end
    (bm, outs)
end

function add_new_block(sc::SolutionBranch, block::ProgramBlock)
    unknown_inputs = filter((key -> haskey(sc.unknown_vars, key)), block.inputs)

    if isempty(unknown_inputs)
        best_match, outputs = try_run_block_with_downstream(sc, block)
        if best_match == NoMatch
            sc
        elseif best_match == Strict
            #  TODO: move variable to known ones and create a branch
            push!(sc.operations, block)
            for key in block.inputs
                insert!(sc.ops_by_input, key, block)
            end
            for key in block.outputs
                insert!(sc.ops_by_output, key, block)
            end
            sc
        else
            #  TODO: move variable to known ones and create a branch
            push!(sc.operations, block)
            for key in block.inputs
                insert!(sc.ops_by_input, key, block)
            end
            for key in block.outputs
                insert!(sc.ops_by_output, key, block)
            end
            sc
        end
    else
        push!(sc.operations, block)
        for key in block.inputs
            insert!(sc.ops_by_input, key, block)
        end
        for key in block.outputs
            insert!(sc.ops_by_output, key, block)
        end
        sc
    end
end

function get_matches(sc::SolutionBranch, keys)
    for key in keys
        kv = sc.unknown_vars[key]
        matched_inputs = skipmissing(match_with_task_val(kv, inp_value, k) for (k, inp_value) in sc.known_vars)

        new_branches = map(matched_inputs) do (k, m, pr)
            new_block = ProgramBlock(pr, [k], [key])
            add_new_block(sc, new_block)
        end
    end

end

function enumerate_for_task(g::ContextualGrammar, timeout, task, maximum_frontier, verbose = true)
    #    Returns, for each task, (program,logPrior) as well as the total number of enumerated programs
    enumeration_timeout = get_enumeration_timeout(timeout)

    start_solution_ctx = create_start_solution(task)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue()


    total_number_of_enumerated_programs = 0
    maxFreeParameters = 2

    pq = PriorityQueue()

    #   SolutionCtx.iter_known_vars start_solution_ctx ~f:(fun ~key ~data ->
    #       List.iter (get_candidates_for_known_var start_solution_ctx key data g) ~f:(fun candidate ->
    #           Heap.add pq (start_solution_ctx, candidate)));
    for (key, var) in iter_unknown_vars(start_solution_ctx)
        for candidate in get_candidates_for_unknown_var(start_solution_ctx, key, var, g)
            pq[(start_solution_ctx, candidate)] = 0
        end
    end

    while (!(enumeration_timed_out(enumeration_timeout))) && !isempty(pq) && length(hits) < maximum_frontier
        (s_ctx, bp), pr = peek(pq)
        dequeue!(pq)
        for child in block_state_successors(maxFreeParameters, g, bp.state)

            if state_finished(child)
                @info(child.skeleton)
                p, ts = capture_free_vars(child.skeleton)

                new_vars = map(ts) do t
                    ntv = NoDataEntry(t)
                    key = "v$(create_next_var(s_ctx))"
                    s_ctx.unknown_vars[key] = ntv
                    key
                end

                new_block = ProgramBlock(p, new_vars, bp.output_vals)
                new_sctx = add_new_block(s_ctx, new_block)
                matches = get_matches(new_sctx, new_block.inputs)

            else

                pq[(s_ctx, BlockPrototype(child, bp.input_vals, bp.output_vals))] = child.cost
            end
        end
    end

    (collect(keys(hits)), total_number_of_enumerated_programs)

end
