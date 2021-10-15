
using DataStructures


get_enumeration_timeout(timeout) = time() + timeout
enumeration_timed_out(timeout) = time() > timeout


get_argument_requests(::Index, argument_types, cg) = [(at, cg.variable_context) for at in argument_types]
get_argument_requests(::FreeVar, argumet_types, cg) = []
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

follow_path(skeleton::Hole, path) =
    if isempty(path)
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

modify_skeleton(::Hole, template, path) =
    if isempty(path)
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
    if isa(state.skeleton, FreeVar)
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
    if !isa(current_hole, Hole)
        error("Error during following path")
    end
    request = current_hole.t
    g = current_hole.grammar

    context = state.context
    context, request = apply_context(context, request)
    if isarrow(request)
        return [
            EnumerationState(
                modify_skeleton(state.skeleton, (Abstraction(Hole(request.arguments[2], g))), state.path),
                context,
                vcat(state.path, [ArgTurn(request.arguments[1])]),
                state.cost,
                state.free_parameters,
            ),
        ]
    else
        environment = path_environment(state.path)
        candidates = unifying_expressions(g, environment, request, context)
        push!(candidates, (FreeVar(request, nothing), [], context, g.log_variable))

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
                    application_template = Apply(application_template, Hole(a, at))
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


capture_free_vars(sc::SolutionBranch, p::Program, context) = p, []

function capture_free_vars(sc::SolutionBranch, p::Apply, context)
    new_f, new_keys_f = capture_free_vars(sc, p.f, context)
    new_x, new_keys_x = capture_free_vars(sc, p.x, context)
    Apply(new_f, new_x), vcat(new_keys_f, new_keys_x)
end

function capture_free_vars(sc::SolutionBranch, p::Abstraction, context)
    new_b, new_keys = capture_free_vars(sc, p.b, context)
    Abstraction(new_b), new_keys
end

function capture_free_vars(sc::SolutionBranch, p::FreeVar, context)
    _, t = apply_context(context, p.t)
    ntv = NoDataEntry(t)
    key = "\$v$(create_next_var(sc))"
    set_unknown(sc, key, ntv)
    FreeVar(t, key), [(key, t)]
end


function try_evaluate_program(p, xs, workspace)
    try
        run_analyzed_with_arguments(p, xs, workspace)
    catch e
        #  We have to be a bit careful with exceptions if the
        #     synthesized program generated an exception, then we just
        #     terminate w/ false but if the enumeration timeout was
        #     triggered during program evaluation, we need to pass the
        #     exception on
        if isa(e, InterruptException)
            rethrow()
        elseif isa(e, UnknownPrimitive)
            error("Unknown primitive: $(e.name)")
        elseif isa(e, MethodError)
            @error(xs)
            @error(workspace)
            rethrow()
        else
            # @error e
            return nothing
        end
    end
end

function try_run_block(sc::SolutionBranch, block::ProgramBlock, inputs)
    input_vals = zip(inputs...)
    expected_output = sc[block.output]

    out_matcher = get_matching_seq(expected_output)

    p = analyze_evaluation(block.p)

    bm = Strict
    outs = []
    for (xs, matcher) in zip(input_vals, out_matcher)
        out_value = try
            try_evaluate_program(p, [], Dict(k => v for (k, v) in zip(block.inputs, xs)))
        catch e
            @error xs
            @error block.p
            @error Dict(k => sc[k] for k in block.inputs)
            rethrow()
        end
        if isnothing(out_value)
            # @error block.p
            # @error Dict(k => v for (k, v) in zip(block.inputs, xs))
            return NoMatch, []
        end
        m = matcher(out_value)
        if m == NoMatch
            return NoMatch, []
        else
            bm = min(bm, m)
        end
        push!(outs, out_value)
    end
    return bm, outs
end

function try_run_block_with_downstream(sc::SolutionBranch, block::ProgramBlock, timeout, redis)
    blocks = Queue{ProgramBlock}()
    enqueue!(blocks, block)
    bm = Strict
    outs = Dict()
    while !isempty(blocks)
        bl = dequeue!(blocks)
        if any(!haskey(outs, key) && !isknown(sc, key) for key in bl.inputs)
            continue
        end
        inputs = [haskey(outs, key) ? outs[key][1] : sc[key].values for key in bl.inputs]
        result = @run_with_timeout timeout redis try_run_block(sc, bl, inputs)
        if isnothing(result) || result[1] == NoMatch
            return (NoMatch, nothing)
        else
            mv, outputs = result
            return_type = return_of_type(block.type)
            if is_polymorphic(return_type)
                @warn "returning polymorphic type"
                # TODO: handle polymorphic types
            end
            # TODO: update expected types for downstream blocks
            outs[bl.output] = collect(outputs), return_type
            for b in downstream_ops(sc, bl.output)
                enqueue!(blocks, b)
            end
            bm = min(mv, bm)
        end
    end
    (bm, outs)
end

function add_new_block(sc::SolutionBranch, block::ProgramBlock, timeout, redis)
    if all(isknown(sc, key) for key in block.inputs)
        best_match, outputs = try_run_block_with_downstream(sc, block, timeout, redis)
        if best_match == NoMatch
            nothing
        elseif best_match == Strict
            # @info "Strict match"
            insert_operation(sc, block)
            for (key, (out_values, t)) in outputs
                known_updates, unknown_updates = value_updates(sc, key, out_values, t)
                for (k, v) in known_updates
                    move_to_known(sc, k, v)
                end
                for (k, v) in unknown_updates
                    set_unknown(sc, k, v)
                end
            end
            # TODO: compute downstream partial fill percentages
            sc
        else
            # @info "Non strict match"
            new_branch = SolutionBranch(
                Dict{String,ValueEntry}(),
                Dict{String,Entry}(),
                Dict{String,Float64}(),
                [],
                sc,
                [],
                sc.example_count,
                0,
                MultiDict{String,ProgramBlock}(),
                MultiDict{String,ProgramBlock}(),
                sc.updated_keys,
                sc.target_key,
                sc.input_keys,
            )
            for (key, (out_values, t)) in outputs
                known_updates, unknown_updates = value_updates(sc, key, out_values, t)
                for (k, v) in known_updates
                    set_known(new_branch, k, v)
                end
                for (k, v) in unknown_updates
                    set_unknown(new_branch, k, v)
                end
            end
            # TODO: compute downstream partial fill percentages
            insert_operation(new_branch, block)
            new_branch
        end
    else
        insert_operation(sc, block)
        sc
    end
end

include("extract_solution.jl")

struct HitResult
    hit_program::String
    hit_prior::Any
    hit_likelihood::Any
    hit_time::Any
end

Base.hash(r::HitResult, h::UInt64) = hash(r.hit_program, h)

function enumerate_for_task(g::ContextualGrammar, timeout, task, maximum_frontier, program_timeout, redis, verbose = true)
    #    Returns, for each task, (program,logPrior) as well as the total number of enumerated programs
    enumeration_timeout = get_enumeration_timeout(timeout)

    start_solution_ctx = create_start_solution(task)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue()

    total_number_of_enumerated_programs = 0
    maxFreeParameters = 2

    pq = PriorityQueue()
    start_time = time()

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

            reset_updated_keys(s_ctx)
            if state_finished(child)
                # @info(child.skeleton)
                p, new_vars = capture_free_vars(s_ctx, child.skeleton, child.context)
                # @info(p)
                arg_types = [v[2] for v in new_vars]
                if isempty(arg_types)
                    p_type = return_of_type(bp.request)
                else
                    p_type = arrow(arg_types..., return_of_type(bp.request))
                end

                new_block = ProgramBlock(p, p_type, [v[1] for v in new_vars], bp.output_val)
                new_sctx = add_new_block(s_ctx, new_block, program_timeout, redis)
                if isnothing(new_sctx)
                    continue
                end
                matches = get_matches(new_sctx, program_timeout, redis)
                for branch in matches
                    if is_solved(branch)
                        solution = extract_solution(branch)
                        ll = @run_with_timeout program_timeout redis task.log_likelihood_checker(task, solution)
                        # @info(solution)
                        if !isnothing(ll) && !isinf(ll)
                            dt = time() - start_time
                            hits[HitResult(join(show_program(solution, false)), -child.cost, ll, dt)] = -child.cost + ll
                            while length(hits) > maximum_frontier
                                dequeue!(hits)
                            end
                        end
                    else
                    end
                end

            else

                pq[(s_ctx, BlockPrototype(child, bp.request, bp.input_vals, bp.output_val))] = child.cost
            end
        end
    end

    @info(collect(keys(hits)))

    (collect(keys(hits)), total_number_of_enumerated_programs)

end
