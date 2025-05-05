
using ArgParse
using JSON
using Random

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
    arc_folder = normpath(joinpath(@__DIR__, "..", "data"))
    dirs = [joinpath(arc_folder, "sortOfARC"), joinpath(arc_folder, "ARC/data/training")]
    concept_arc_dir = joinpath(arc_folder, "ConceptARC/corpus")
    for category_dir in readdir(concept_arc_dir; join = true)
        push!(dirs, category_dir)
    end
    for dir in dirs
        for fname in readdir(dir; join = true)
            if endswith(fname, ".json")
                task = create_arc_task(fname, tp)
                push!(tasks, task)
            end
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
    elseif model == "standalone"
        return PythonStandaloneGuidingModel()
    end
    error("Unknown model: $model")
end

function enqueue_updates(sc::SolutionContext, guiding_model_channels, grammar)
    new_unknown_branches = Set(get_new_values(sc.branch_is_unknown))
    new_explained_branches = Set(get_new_values(sc.branch_is_not_copy))
    updated_factors_unknown_branches = Set(get_new_values(sc.unknown_complexity_factors))
    updated_factors_explained_branches = Set(get_new_values(sc.explained_complexity_factors))
    if sc.verbose
        @info "New unknown branches: $new_unknown_branches"
        @info "New explained branches: $new_explained_branches"
        @info "Updated factors unknown branches: $updated_factors_unknown_branches"
        @info "Updated factors explained branches: $updated_factors_explained_branches"
    end
    for branch_id in new_explained_branches
        if !sc.branch_is_not_copy[branch_id]
            continue
        end
        enqueue_known_var(sc, branch_id, guiding_model_channels, grammar)
    end
    updated_known_entries = Set{UInt64}()
    for branch_id in updated_factors_explained_branches
        if branch_id == sc.target_branch_id
            for (bl_info, cost) in sc.duplicate_copies_queue
                sc.copies_queue[bl_info] = cost
            end
            empty!(sc.duplicate_copies_queue)
        end
        if !sc.branch_is_not_copy[branch_id] ||
           in(branch_id, new_explained_branches) ||
           branch_id == sc.target_branch_id
            continue
        end
        push!(updated_known_entries, sc.branch_entries[branch_id])
    end
    for entry_id in updated_known_entries
        update_entry_priority(sc, entry_id, true)
    end

    for branch_id in new_unknown_branches
        enqueue_unknown_var(sc, branch_id, guiding_model_channels, grammar)
    end
    updated_unknown_entries = Set{UInt64}()
    for branch_id in updated_factors_unknown_branches
        if !in(branch_id, new_unknown_branches)
            push!(updated_unknown_entries, sc.branch_entries[branch_id])
        end
    end
    for entry_id in updated_unknown_entries
        update_entry_priority(sc, entry_id, false)
    end
end

function allow_vars_only(p::Apply)
    return Apply(allow_vars_only(p.f), allow_vars_only(p.x))
end

function allow_vars_only(p::Abstraction)
    return Abstraction(allow_vars_only(p.b))
end

function allow_vars_only(p::Hole)
    candidates_filter = combine_arg_checkers(p.candidates_filter, SimpleArgChecker(nothing, nothing, nothing, true))
    return Hole(p.t, p.root_t, p.locations, candidates_filter, p.possible_values)
end

function allow_vars_only(p::Program)
    return p
end

function block_state_successors(sc::SolutionContext, max_free_parameters, bp::BlockPrototype)::Vector{BlockPrototype}
    current_hole = follow_path(bp.skeleton, bp.path)
    if !isa(current_hole, Hole)
        error("Error during following path")
    end
    request = current_hole.t
    root_request = current_hole.root_t

    context = bp.context
    context, request = apply_context(context, request)
    context, root_request = apply_context(context, root_request)
    if isarrow(request)
        return [
            BlockPrototype(
                modify_skeleton(
                    bp.skeleton,
                    (Abstraction(
                        Hole(
                            request.arguments[2],
                            root_request.arguments[2],
                            current_hole.locations,
                            step_arg_checker(
                                current_hole.candidates_filter,
                                ArgTurn(request.arguments[1], root_request.arguments[1]),
                            ),
                            current_hole.possible_values,
                        ),
                    )),
                    bp.path,
                ),
                context,
                vcat(bp.path, [ArgTurn(request.arguments[1], root_request.arguments[1])]),
                bp.cost,
                bp.free_parameters,
                bp.request,
                bp.root_request,
                bp.root_entry,
                bp.reverse,
            ),
        ]
    else
        environment = path_environment(bp.path)

        cg = sc.entry_grammars[(bp.root_entry, bp.reverse)]

        candidates = unifying_expressions(cg, environment, context, current_hole, bp.skeleton, bp.path)

        bps = map(candidates) do (candidate, argument_types, root_argument_types, context, ll)
            if isa(candidate, Abstraction)
                new_free_parameters = 0
                application_template = Apply(
                    candidate,
                    Hole(argument_types[1], root_argument_types[1], [], current_hole.candidates_filter, nothing),
                )
                new_skeleton = modify_skeleton(bp.skeleton, application_template, bp.path)
                new_path = vcat(bp.path, [LeftTurn(), ArgTurn(argument_types[1], root_argument_types[1])])
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
                            Hole(argument_types[i], root_argument_types[i], [(candidate, i)], arg_checker, nothing),
                        )
                    end
                    new_skeleton = modify_skeleton(bp.skeleton, application_template, bp.path)
                    new_path = vcat(bp.path, [LeftTurn() for _ in 2:length(argument_types)], [RightTurn()])
                end
            end
            context, new_request = apply_context(context, bp.request)
            context, new_root_request = apply_context(context, bp.root_request)
            if is_reversible(new_skeleton) && !isa(sc.entries[bp.root_entry], AbductibleEntry)
                new_skeleton = allow_vars_only(new_skeleton)
            end
            return BlockPrototype(
                new_skeleton,
                context,
                new_path,
                bp.cost + ll,
                bp.free_parameters + new_free_parameters,
                new_request,
                new_root_request,
                bp.root_entry,
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
    output_entry = sc.entries[bp.root_entry]
    is_reverse =
        is_reversible(bp.skeleton) &&
        !isa(output_entry, AbductibleEntry) &&
        !(isa(output_entry, PatternEntry) && all(v == PatternWrapper(any_object) for v in output_entry.values))

    p = bp.skeleton

    arg_types = _get_free_vars(p)
    _, return_type = apply_context(bp.context, bp.root_request)
    if !isempty(arg_types)
        new_arg_types = OrderedDict{Union{String,UInt64},Tp}()
        for (var_id, (t, fix_t)) in arg_types
            _, t = apply_context(bp.context, t)
            new_arg_types[var_id] = t
        end
        p_type = TypeNamedArgsConstructor(ARROW, new_arg_types, return_type)
    else
        p_type = return_type
    end
    fix_context = unify(bp.context, return_type, bp.request)
    _, p_fix_type = apply_context(fix_context, p_type)

    if is_reverse
        # @info "Try get reversed for $bp"
        input_vars, _, has_eithers, has_abductibles = try_get_reversed_values(sc, p, p_type, p_fix_type, bp.root_entry)
    else
        input_vars = []
        for (var_id, t) in arguments_of_type(p_fix_type)
            _, t_norm = instantiate(t, empty_context)
            t_norm_id = push!(sc.types, t_norm)
            entry = NoDataEntry(t_norm_id)
            entry_index = push!(sc.entries, entry)
            t_root = p_type.arguments[var_id]
            push!(input_vars, (var_id, entry_index, (t, t_root)))
        end

        has_eithers = false
        has_abductibles = false
    end

    block_info = (p, p_type, p_fix_type, bp.cost, input_vars, has_eithers, has_abductibles, is_reverse)

    if !haskey(sc.found_blocks_forward, bp.root_entry)
        sc.found_blocks_forward[bp.root_entry] = []
    end
    push!(sc.found_blocks_forward[bp.root_entry], block_info)
    sc.blocks_found += 1

    for branch_id in get_connected_to(sc.branch_entries, bp.root_entry)
        if sc.branch_is_unknown[branch_id]
            foll_entries = get_connected_from(sc.branch_foll_entries, branch_id)
            if sc.traced || all(!in(entry_id, foll_entries) for (_, entry_id, _) in input_vars)
                if sc.verbose
                    @info "Adding $((false, branch_id, block_info)) to insert queue"
                end
                sc.blocks_to_insert[(branch_id, block_info)] = sc.unknown_min_path_costs[branch_id] + block_info[4]
            else
                if sc.verbose
                    @info "Skipping $((false, branch_id, block_info)) because of following entries $foll_entries"
                end
            end
        end
    end
end

function insert_block(sc::SolutionContext, output_branch_id::UInt64, block_info)
    output_var_id = sc.branch_vars[output_branch_id]
    p, p_type, p_fix_type, cost, input_vars, has_eithers, has_abductibles, is_reverse = block_info
    if !check_valid_program_location(sc, p, output_var_id, true)
        return nothing
    end

    related_branches = union(get_all_parents(sc, output_branch_id), get_all_children(sc, output_branch_id))
    related_blocks = Set([
        bl_id for related_branch_id in related_branches for
        (_, bl_id) in get_connected_from(sc.branch_incoming_blocks, related_branch_id)
    ])

    block_id = nothing
    block = nothing
    for bl_id in related_blocks
        bl = sc.blocks[bl_id]
        if isa(bl, ReverseProgramBlock) || isa(bl.p, FreeVar)
            continue
        end
        if is_on_path(p, bl.p, Dict())
            if sc.verbose
                @info "Found matching parent block $bl"
                @info "Bp $p"
            end
            # p = bl.p
            block_id = bl_id
            block = bl
            break
        end
    end

    if isnothing(block_id)
        new_p, new_vars = capture_new_free_vars(sc, p)

        if !isempty(new_vars)
            arg_types = OrderedDict{Union{String,UInt64},Tp}(
                new_var => p_type.arguments[old_var] for (old_var, new_var) in new_vars
            )
            new_p_type = TypeNamedArgsConstructor(ARROW, arg_types, return_of_type(p_type))
        else
            new_p_type = p_type
        end

        _, new_p_type = instantiate(new_p_type, empty_context)

        block =
            ProgramBlock(new_p, new_p_type, cost, [new_vars[v] for (v, _, _) in input_vars], output_var_id, is_reverse)
        block_id = push!(sc.blocks, block)
        sc.block_root_branches[block_id] = output_branch_id

        var_locations = collect_var_locations(new_p)
        for (var_id, locations) in var_locations
            sc.unknown_var_locations[var_id] = collect(locations)
        end
    end

    input_branches = Dict{UInt64,UInt64}()
    if is_reverse
        if has_eithers
            input_vars, _, _, _ =
                try_get_reversed_values(sc, p, p_type, p_fix_type, sc.branch_entries[output_branch_id], block_id)
        end

        out_entry = sc.entries[sc.branch_entries[output_branch_id]]
        complexity_factor = sc.unknown_complexity_factors[output_branch_id]
        if !has_abductibles
            complexity_factor -=
                out_entry.complexity -
                sum(sc.entries[entry_id].complexity for (_, entry_id, _) in input_vars; init = 0.0)
        end

        either_branch_ids = UInt64[]
        either_var_ids = UInt64[]
        out_related_complexity_branches = get_connected_from(sc.related_unknown_complexity_branches, output_branch_id)

        for (var_id, (_, entry_index, _)) in zip(block.input_vars, input_vars)
            entry = sc.entries[entry_index]
            exact_match, parents_children = find_related_branches(sc, var_id, entry, entry_index)

            if !isnothing(exact_match)
                branch_id = exact_match
            else
                branch_id = increment!(sc.branches_count)
                sc.branch_entries[branch_id] = entry_index
                sc.branch_vars[branch_id] = var_id
                sc.branch_types[branch_id] = entry.type_id
                if sc.verbose
                    @info "Created new branch $branch_id $entry"
                    @info "Parents children $parents_children"
                end
                for (parent, children) in parents_children
                    if !isnothing(parent)
                        deleteat!(sc.branch_children, [parent], children)
                        sc.branch_children[parent, branch_id] = true
                    end
                    sc.branch_children[branch_id, children] = true
                end
            end

            sc.branch_is_unknown[branch_id] = true
            sc.branch_unknown_from_output[branch_id] = sc.branch_unknown_from_output[output_branch_id]
            sc.unknown_min_path_costs[branch_id] = cost + sc.unknown_min_path_costs[output_branch_id]
            sc.unknown_complexity_factors[branch_id] = complexity_factor
            sc.unmatched_complexities[branch_id] = entry.complexity
            sc.related_unknown_complexity_branches[branch_id, out_related_complexity_branches] = true
            sc.complexities[branch_id] = entry.complexity

            if isa(entry, EitherEntry)
                push!(either_branch_ids, branch_id)
                push!(either_var_ids, var_id)
            end

            input_branches[var_id] = branch_id
        end

        if length(input_branches) > 1
            for (_, branch_id) in input_branches
                inds = [b_id for (_, b_id) in input_branches if b_id != branch_id]
                sc.related_unknown_complexity_branches[branch_id, inds] = true
            end
        end
        if length(either_branch_ids) >= 1
            active_constraints = keys(get_connected_from(sc.constrained_branches, output_branch_id))
            if length(active_constraints) == 0
                new_constraint_id = increment!(sc.constraints_count)
                # @info "Added new constraint with either $new_constraint_id"
                active_constraints = UInt64[new_constraint_id]
            end
            for constraint_id in active_constraints
                sc.constrained_branches[either_branch_ids, constraint_id] = either_var_ids
                sc.constrained_vars[either_var_ids, constraint_id] = either_branch_ids
            end
        end
    else
        min_path_cost = sc.unknown_min_path_costs[output_branch_id] + cost
        complexity_factor = sc.unknown_complexity_factors[output_branch_id]
        for (var_id, (_, entry_index, _)) in zip(block.input_vars, input_vars)
            entry = sc.entries[entry_index]
            exact_match, parents_children = find_related_branches(sc, var_id, entry, entry_index)

            if !isnothing(exact_match)
                branch_id = exact_match
            else
                branch_id = increment!(sc.branches_count)
                sc.branch_entries[branch_id] = entry_index
                sc.branch_vars[branch_id] = var_id
                sc.branch_types[branch_id] = entry.type_id
                for (parent, children) in parents_children
                    if !isnothing(parent)
                        deleteat!(sc.branch_children, [parent], children)
                        sc.branch_children[parent, branch_id] = true
                    end
                    sc.branch_children[branch_id, children] = true
                end
            end

            sc.branch_is_unknown[branch_id] = true
            sc.branch_unknown_from_output[branch_id] = sc.branch_unknown_from_output[output_branch_id]
            sc.unknown_min_path_costs[branch_id] = min_path_cost
            sc.unknown_complexity_factors[branch_id] = complexity_factor

            input_branches[var_id] = branch_id
        end
    end

    sc.blocks_inserted += 1
    return block_id, input_branches, Dict{UInt64,UInt64}(output_var_id => output_branch_id)
end

function create_wrapping_program_prototype(sc::SolutionContext, bp::BlockPrototype, output_vars, var_id::UInt64)
    var_ind = findfirst(v_info -> v_info[1] == var_id, output_vars)

    cg = sc.entry_grammars[(bp.root_entry, true)]

    candidate_functions = unifying_expressions(
        cg,
        Tuple{Tp,Tp}[],
        bp.context,
        Hole(
            bp.request,
            bp.root_request,
            [],
            CombinedArgChecker([SimpleArgChecker(true, -1, false, nothing)]),
            nothing,
        ),
        Hole(
            bp.request,
            bp.root_request,
            [],
            CombinedArgChecker([SimpleArgChecker(true, -1, false, nothing)]),
            nothing,
        ),
        [],
    )

    wrapper, arg_types, arg_root_types, new_context, wrap_cost =
        first(v for v in candidate_functions if v[1] == every_primitive["rev_fix_param"])

    unknown_entry = sc.entries[output_vars[var_ind][2]]
    unknown_type, unknown_root_type = output_vars[var_ind][3]
    new_context = unify(new_context, unknown_type, arg_types[2])
    new_context = unify(new_context, unknown_root_type, arg_root_types[2])
    if isnothing(new_context)
        error("Can't unify $(unknown_type) with $(arg_types[2])")
    end
    new_context, fixer_type = apply_context(new_context, arg_types[3])
    new_context, fixer_root_type = apply_context(new_context, arg_root_types[3])

    custom_arg_checkers = _get_custom_arg_checkers(wrapper)

    wrapped_p = Apply(
        Apply(Apply(wrapper, bp.skeleton), FreeVar(unknown_root_type, unknown_type, var_id, nothing)),
        Hole(
            fixer_type,
            fixer_root_type,
            [(wrapper, 3)],
            CombinedArgChecker([custom_arg_checkers[3]]),
            unknown_entry.values,
        ),
    )

    new_bp = BlockPrototype(
        wrapped_p,
        new_context,
        [RightTurn()],
        bp.cost + wrap_cost + 0.001,
        number_of_free_parameters(bp.skeleton),
        bp.request,
        bp.root_request,
        bp.root_entry,
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

function create_reversed_block(sc::SolutionContext, bp::BlockPrototype)
    p = bp.skeleton
    arg_types = _get_free_vars(p)
    _, return_type = apply_context(bp.context, bp.root_request)
    if !isempty(arg_types)
        new_arg_types = OrderedDict{Union{String,UInt64},Tp}()
        for (var_id, (t, fix_t)) in arg_types
            _, t = apply_context(bp.context, t)
            new_arg_types[var_id] = t
        end
        p_type = TypeNamedArgsConstructor(ARROW, new_arg_types, return_type)
    else
        p_type = return_type
    end
    fix_context = unify(bp.context, return_type, bp.request)
    _, p_fix_type = apply_context(fix_context, p_type)

    output_vars, unfixed_vars, has_eithers, has_abductibles =
        try_get_reversed_values(sc, p, p_type, p_fix_type, bp.root_entry)

    if isempty(output_vars)
        throw(EnumerationException())
    end
    if isempty(unfixed_vars)
        block_info = (p, p_type, bp.cost, output_vars, has_eithers, has_abductibles)

        if !haskey(sc.found_blocks_reverse, bp.root_entry)
            sc.found_blocks_reverse[bp.root_entry] = []
        end
        push!(sc.found_blocks_reverse[bp.root_entry], block_info)
        sc.rev_blocks_found += 1

        for branch_id in get_connected_to(sc.branch_entries, bp.root_entry)
            if sc.branch_is_explained[branch_id] &&
               sc.branch_is_not_copy[branch_id] &&
               !isnothing(sc.explained_min_path_costs[branch_id]) &&
               sc.branch_is_not_const[branch_id]
                prev_entries = get_connected_from(sc.branch_prev_entries, branch_id)
                if sc.traced || all(!in(entry_id, prev_entries) for (_, entry_id, _) in output_vars)
                    if sc.verbose
                        @info "Adding $((true, branch_id, block_info)) to insert queue"
                    end
                    sc.rev_blocks_to_insert[(branch_id, block_info)] =
                        sc.explained_min_path_costs[branch_id] + block_info[3]
                else
                    if sc.verbose
                        @info "Skipping $((true, branch_id, block_info)) because of previous entries $prev_entries"
                    end
                end
            end
        end
        return []
    else
        unfinished_prototypes = []
        for var_id in unfixed_vars
            push!(unfinished_prototypes, create_wrapping_program_prototype(sc, bp, output_vars, var_id))
        end
        drop_changes!(sc, sc.transaction_depth - 1)
        start_transaction!(sc, sc.transaction_depth + 1)
        return unfinished_prototypes
    end
end

function insert_reverse_block(sc::SolutionContext, input_branch_id::UInt64, block_info)
    input_var_id = sc.branch_vars[input_branch_id]

    p, p_type, cost, output_vars, has_eithers, has_abductibles = block_info
    if !check_valid_program_location(sc, p, input_var_id, false)
        return nothing
    end

    related_branches = union(get_all_parents(sc, input_branch_id), get_all_children(sc, input_branch_id))
    related_blocks = Set([
        bl_id for related_branch_id in related_branches for
        (_, bl_id) in get_connected_from(sc.branch_outgoing_blocks, related_branch_id)
    ])
    block_id = nothing
    block = nothing
    for bl_id in related_blocks
        bl = sc.blocks[bl_id]
        if !isa(bl, ReverseProgramBlock)
            continue
        end

        if is_on_path(p, bl.p, Dict())
            if sc.verbose
                @info "Found matching parent block $bl"
                @info "Bp $p"
            end
            block_id = bl_id
            block = bl
            break
        end
    end

    if isnothing(block_id)
        new_p, new_vars = capture_new_free_vars(sc, p)

        arg_types = OrderedDict{Union{String,UInt64},Tp}(
            new_var => p_type.arguments[old_var] for (old_var, new_var) in new_vars
        )
        p_type = TypeNamedArgsConstructor(ARROW, arg_types, return_of_type(p_type))

        block = ReverseProgramBlock(new_p, p_type, cost, [input_var_id], [new_vars[v] for (v, _, _) in output_vars])
        var_locations = collect_var_locations(new_p)
        for (var_id, locations) in var_locations
            sc.known_var_locations[var_id] = collect(locations)
        end
        block_id = push!(sc.blocks, block)
        sc.block_root_branches[block_id] = input_branch_id
    end

    if has_eithers
        @error "Reverse block with eithers"
        @error "Input branch id $input_branch_id"
        @error output_vars
        throw(EnumerationException())
        # _, output_vars, _, _, _ = try_get_reversed_values(sc, p, context, sc.branch_entries[input_branch_id], block_id)
    end

    input_entry = sc.entries[sc.branch_entries[input_branch_id]]
    complexity_factor = sc.explained_complexity_factors[input_branch_id]
    if !has_abductibles
        complexity_factor -=
            input_entry.complexity -
            sum(sc.entries[entry_id].complexity for (_, entry_id, _) in output_vars; init = 0.0)
    end
    new_branches = Dict{UInt64,UInt64}()
    out_related_complexity_branches = get_connected_from(sc.related_explained_complexity_branches, input_branch_id)

    for (var_id, (_, entry_index, _)) in zip(block.output_vars, output_vars)
        entry = sc.entries[entry_index]
        exact_match, parents_children = find_related_branches(sc, var_id, entry, entry_index)

        if !isnothing(exact_match)
            branch_id = exact_match
        else
            branch_id = increment!(sc.branches_count)
            sc.branch_entries[branch_id] = entry_index
            sc.branch_vars[branch_id] = var_id
            sc.branch_types[branch_id] = entry.type_id
            if sc.verbose
                @info "Created new branch $branch_id $entry"
                @info "Parents children $parents_children"
            end
            for (parent, children) in parents_children
                if !isnothing(parent)
                    deleteat!(sc.branch_children, [parent], children)
                    sc.branch_children[parent, branch_id] = true
                end
                sc.branch_children[branch_id, children] = true
            end
        end

        sc.explained_min_path_costs[branch_id] = cost + sc.explained_min_path_costs[input_branch_id]
        sc.explained_complexity_factors[branch_id] = complexity_factor
        sc.unused_explained_complexities[branch_id] = entry.complexity
        sc.added_upstream_complexities[branch_id] = sc.added_upstream_complexities[input_branch_id]
        sc.related_explained_complexity_branches[branch_id, out_related_complexity_branches] = true

        sc.complexities[branch_id] = entry.complexity

        new_branches[var_id] = branch_id
    end

    if length(new_branches) > 1
        for (_, branch_id) in new_branches
            inds = [b_id for (_, b_id) in new_branches if b_id != branch_id]
            sc.related_explained_complexity_branches[branch_id, inds] = true
        end
    end

    sc.rev_blocks_inserted += 1
    return block_id, Dict{UInt64,UInt64}(input_var_id => input_branch_id), new_branches
end

function enumeration_iteration_finished(sc::SolutionContext, bp::BlockPrototype)
    if bp.reverse
        return create_reversed_block(sc, bp)
    else
        enumeration_iteration_finished_output(sc, bp)
        return []
    end
end

function enumeration_iteration_insert_block(
    sc::SolutionContext,
    is_reverse,
    br_id,
    block_info,
    guiding_model_channels,
    grammar,
)
    if sc.verbose
        @info "Inserting block $((is_reverse, br_id, block_info))"
    end
    found_solutions = transaction(sc) do
        new_block_result = if is_reverse
            insert_reverse_block(sc, br_id, block_info)
        else
            insert_block(sc, br_id, block_info)
        end
        if !isnothing(new_block_result)
            new_block_id, input_branches, target_output = new_block_result
            found_solutions = add_new_block(sc, new_block_id, input_branches, target_output)
            if sc.verbose
                @info "Got results $found_solutions"
            end
        else
            found_solutions = []
        end

        enqueue_updates(sc, guiding_model_channels, grammar)
        return found_solutions
    end
    if isnothing(found_solutions)
        found_solutions = []
    end
    return found_solutions
end

function enumeration_iteration_insert_copy_block(sc::SolutionContext, block_info, guiding_model_channels, grammar)
    if sc.verbose
        @info "Inserting copy block $(block_info)"
    end
    found_solutions = transaction(sc) do
        block, input_branches, output_branches = block_info
        if is_block_loops(sc, block)
            return []
        end
        block_id = push!(sc.blocks, block)
        sc.block_root_branches[block_id] = output_branches[block.output_var]

        new_solution_paths = add_new_block(sc, block_id, input_branches, output_branches)
        if sc.verbose
            @info "Got results $new_solution_paths"
        end
        sc.copy_blocks_inserted += 1
        enqueue_updates(sc, guiding_model_channels, grammar)
        return new_solution_paths
    end
    if isnothing(found_solutions)
        found_solutions = []
    end
    return found_solutions
end

function enumeration_iteration(
    run_context,
    sc::SolutionContext,
    max_free_parameters::Int,
    bp::BlockPrototype,
    entry_id::UInt64,
    is_forward::Bool,
)
    q = (is_forward ? sc.entry_queues_forward : sc.entry_queues_reverse)[entry_id]
    if state_finished(bp)
        if sc.verbose
            @info "Checking finished $bp"
        end
        transaction(sc) do
            unfinished_prototypes =
                @run_with_timeout run_context "program_timeout" enumeration_iteration_finished(sc, bp)
            if isnothing(unfinished_prototypes)
                throw(EnumerationException())
            end
            for new_bp in unfinished_prototypes
                if sc.verbose
                    @info "Enqueing $new_bp"
                end
                q[new_bp] = new_bp.cost
            end
        end
    else
        if sc.verbose
            @info "Checking unfinished $bp"
        end
        new_bps = block_state_successors(sc, max_free_parameters, bp)
        for new_bp in new_bps
            if sc.verbose
                @info "Enqueing $new_bp"
            end
            q[new_bp] = new_bp.cost
        end
    end
    update_entry_priority(sc, entry_id, !is_forward)
end

function solve_task(
    task,
    task_name,
    guiding_model_channels,
    grammar,
    previous_traces,
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

    sc = create_starting_context(task, task_name, type_weights, hyperparameters, verbose)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue{HitResult,Float64}()

    max_free_parameters = 10

    start_time = time()
    try
        enqueue_updates(sc, guiding_model_channels, grammar)
        save_changes!(sc, 0)

        phase = 4

        while (!(enumeration_timed_out(enumeration_timeout))) &&
                  (
                      !isempty(sc.pq_forward) ||
                      !isempty(sc.pq_reverse) ||
                      !isempty(sc.copies_queue) ||
                      !isempty(sc.blocks_to_insert) ||
                      !isempty(sc.rev_blocks_to_insert) ||
                      !isempty(sc.waiting_entries)
                  ) &&
                  length(hits) < maximum_solutions
            receive_grammar_weights(sc, guiding_model_channels, grammar)

            phase = (phase + 1) % 5

            if phase == 2
                if isempty(sc.blocks_to_insert)
                    continue
                end
                br_id, block_info = dequeue!(sc.blocks_to_insert)

                found_solutions =
                    enumeration_iteration_insert_block(sc, false, br_id, block_info, guiding_model_channels, grammar)
            elseif phase == 3
                if isempty(sc.rev_blocks_to_insert)
                    continue
                end
                br_id, block_info = dequeue!(sc.rev_blocks_to_insert)

                found_solutions =
                    enumeration_iteration_insert_block(sc, true, br_id, block_info, guiding_model_channels, grammar)
            elseif phase == 4
                if isempty(sc.copies_queue)
                    continue
                end
                block_info = dequeue!(sc.copies_queue)

                found_solutions =
                    enumeration_iteration_insert_copy_block(sc, block_info, guiding_model_channels, grammar)
            else
                if phase == 0
                    pq = sc.pq_forward
                    is_forward = true
                else
                    pq = sc.pq_reverse
                    is_forward = false
                end
                if isempty(pq)
                    sleep(0.0001)
                    continue
                end
                entry_id = draw(pq)
                q = (is_forward ? sc.entry_queues_forward : sc.entry_queues_reverse)[entry_id]
                bp = dequeue!(q)

                enumeration_iteration(run_context, sc, max_free_parameters, bp, entry_id, is_forward)
                found_solutions = []
            end

            sc.iterations_count += 1

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
            export_solution_context(sc, previous_traces)
        end
    catch
        export_solution_context(sc)
        rethrow()
    finally
        mark_task_finished(guiding_model_channels, task_name)
    end

    hits
end

function try_solve_task(
    task,
    task_name,
    guiding_model_channels,
    grammar,
    previous_traces,
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
            task_name,
            guiding_model_channels,
            grammar,
            previous_traces,
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
        @error "Failed to solve task $(task.name)" exception = (e, bt)
        rethrow()
    end
    return Dict("task" => task, "traces" => traces)
end

function try_solve_tasks(
    worker_pool,
    tasks,
    guiding_model_server::GuidingModelServer,
    grammar,
    previous_traces,
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
        task_name = "$(task.name)_$(randstring(6))"
        put!(register_channel, task_name)
        prev_traces = get(previous_traces, task.name, nothing)
        while true
            reg_task_name, request_channel, result_channel, end_tasks_channel = take!(register_response_channel)
            if reg_task_name == task_name
                return @time try_solve_task(
                    task,
                    task_name,
                    (request_channel, result_channel, end_tasks_channel),
                    grammar,
                    prev_traces,
                    timeout_containers,
                    timeout,
                    program_timeout,
                    type_weights,
                    hyperparameters,
                    maximum_solutions,
                    verbose,
                )
            else
                put!(register_response_channel, (reg_task_name, request_channel, result_channel, end_tasks_channel))
                sleep(0.01)
            end
        end
    end
    filter!(tr -> !isempty(tr["traces"]), new_traces)
    @info "Got new solutions for $(length(new_traces))/$(length(tasks)) tasks"
    return new_traces
end

function try_solve_tasks(
    worker_pool,
    tasks,
    guiding_model_server::PythonGuidingModelServer,
    grammar,
    previous_traces,
    timeout,
    program_timeout,
    type_weights,
    hyperparameters,
    maximum_solutions,
    verbose,
)
    timeout_containers = worker_pool.timeout_containers
    redis_db = guiding_model_server.model.redis_db
    new_traces = pmap(
        worker_pool,
        tasks;
        retry_check = (s, e) -> isa(e, ProcessExitedException),
        retry_delays = zeros(5),
    ) do task
        # new_traces = map(tasks) do task
        task_name = "$(task.name)_$(randstring(6))"
        conn = get_redis_connection(redis_db)
        prev_traces = get(previous_traces, task.name, nothing)
        result = @time try_solve_task(
            task,
            task_name,
            conn,
            grammar,
            prev_traces,
            timeout_containers,
            timeout,
            program_timeout,
            type_weights,
            hyperparameters,
            maximum_solutions,
            verbose,
        )
        Redis.disconnect(conn)
        return result
    end
    filter!(tr -> !isempty(tr["traces"]), new_traces)
    @info "Got new solutions for $(length(new_traces))/$(length(tasks)) tasks"
    return new_traces
end

function get_manual_traces(domain, tasks, grammar, grammar_hash, worker_pool, guiding_model_server, traces)
    if domain == "arc"
        @info "Getting manual traces"
        if haskey(traces, grammar_hash)
            tr = build_manual_traces(tasks, guiding_model_server, grammar, worker_pool, traces[grammar_hash][2])
        else
            tr = build_manual_traces(tasks, guiding_model_server, grammar, worker_pool, nothing)
        end
        log_traces(tr)
        traces[grammar_hash] = (grammar, tr)
    end
    return traces
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
    traces_to_save = Dict{UInt64,Any}(h => ([string(p) for p in g], t) for (h, (g, t)) in traces)
    Serialization.serialize(joinpath(path, "traces.jls"), traces_to_save)
    Serialization.serialize(joinpath(path, "grammar.jls"), [string(p) for p in grammar])
    save_guiding_model(guiding_model, joinpath(path, "guiding_model.jld2"))
    @info "Saved checkpoint for iteration $(iteration-1) to $path"
end

function load_checkpoint(path)
    args, iteration = Serialization.deserialize(joinpath(path, "args.jls"))
    loaded_traces = Serialization.deserialize(joinpath(path, "traces.jls"))
    traces = Dict{UInt64,Any}()
    for (grammar_strs, gr_traces) in values(loaded_traces)
        grammar = [parse_program(p_str) for p_str in grammar_strs]
        grammar_hash = hash(grammar)
        traces[grammar_hash] = (grammar, gr_traces)
    end
    grammar_strs = Serialization.deserialize(joinpath(path, "grammar.jls"))
    grammar = [parse_program(p_str) for p_str in grammar_strs]
    guiding_model = load_guiding_model(joinpath(path, "guiding_model.jld2"))
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

    hyperparameters = Dict{String,Any}(
        "path_cost_power" => 3.0,
        "complexity_power" => 2.0,
        "block_cost_power" => 6.0,
        "explained_penalty_power" => 8.0,
        "explained_penalty_mult" => 5.0,
        "match_duplicates_penalty" => 80.0,
        "type_var_penalty_mult" => 8.0,
        "type_var_penalty_power" => 8.0,
    )

    grammar_hash = hash(grammar)
    guiding_model_server = GuidingModelServer(guiding_model)
    start_server(guiding_model_server)
    send_wandb_config(guiding_model_server, hyperparameters)
    set_current_grammar!(guiding_model, grammar)
    worker_pool = ReplenishingWorkerPool(parsed_args[:workers])

    type_weights = Dict{String,Any}(
        "int" => 1.0,
        "list" => 2.0,
        "color" => 4.0,
        "bool" => 1.0,
        "grid" => 0.5,
        "tuple2" => 2.0,
        "set" => 1.0,
        "any" => 0.1,
        "either" => 0.5,
    )

    # tasks = tasks[begin:10]

    try
        while i <= parsed_args[:iterations]
            traces = get_manual_traces(
                parsed_args[:domain],
                tasks,
                grammar,
                grammar_hash,
                worker_pool,
                guiding_model_server,
                traces,
            )
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
            if !haskey(traces, grammar_hash)
                traces[grammar_hash] = (grammar, Dict{String,Any}())
            end
            send_wandb_log(guiding_model_server, Dict("solved_tasks" => length(new_traces)))
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

            cur_traces, grammar = compress_traces(tasks, cur_traces, grammar)
            grammar_hash = hash(grammar)
            traces[grammar_hash] = (grammar, cur_traces)

            @info "Got total solutions for $(length(cur_traces))/$(length(tasks)) tasks"
            log_traces(cur_traces)
            log_grammar(i, grammar)

            clear_model_cache(guiding_model)
            i += 1
            guiding_model = update_guiding_model(guiding_model, traces)
            save_checkpoint(parsed_args, i, traces, grammar, guiding_model)
            set_current_grammar!(guiding_model, grammar)
        end
    finally
        stop(worker_pool)
        stop_server(guiding_model_server, true)
    end
end
