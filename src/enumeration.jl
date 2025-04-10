
using DataStructures

get_enumeration_timeout(timeout)::Float64 = time() + timeout
enumeration_timed_out(timeout)::Bool = time() > timeout

struct WrongPath <: Exception end

function follow_path(skeleton::Apply, path)
    if isempty(path)
        skeleton
    elseif isa(path[1], LeftTurn)
        follow_path(skeleton.f, view(path, 2:length(path)))
    elseif isa(path[1], RightTurn)
        follow_path(skeleton.x, view(path, 2:length(path)))
    else
        throw(WrongPath())
    end
end

function follow_path(skeleton::Abstraction, path)
    if isempty(path)
        skeleton
    elseif isa(path[1], ArgTurn)
        follow_path(skeleton.b, view(path, 2:length(path)))
    else
        throw(WrongPath())
    end
end

follow_path(skeleton::Hole, path) =
    if isempty(path)
        skeleton
    else
        throw(WrongPath())
    end

follow_path(skeleton::Program, path) =
    if isempty(path)
        skeleton
    else
        throw(WrongPath())
    end

path_environment(path) = reverse(Tp[t.type for t in path if isa(t, ArgTurn)])

modify_skeleton(skeleton::Abstraction, template, path) =
    if isa(path[1], ArgTurn)
        Abstraction(modify_skeleton(skeleton.b, template, view(path, 2:length(path))))
    else
        throw(WrongPath())
    end

modify_skeleton(::Hole, template, path) =
    if isempty(path)
        template
    else
        throw(WrongPath())
    end

modify_skeleton(skeleton::Apply, template, path) =
    if isa(path[1], LeftTurn)
        Apply(modify_skeleton(skeleton.f, template, view(path, 2:length(path))), skeleton.x)
    elseif isa(path[1], RightTurn)
        Apply(skeleton.f, modify_skeleton(skeleton.x, template, view(path, 2:length(path))))
    else
        throw(WrongPath())
    end

function _unwind_path(path)
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

function unwind_path(path, skeleton)
    new_path = _unwind_path(path)
    if !isempty(new_path)
        try
            follow_path(skeleton, new_path)
        catch e
            if isa(e, WrongPath)
                return unwind_path(new_path, skeleton)
            else
                rethrow()
            end
        end
    end
    return new_path
end

violates_symmetry(::Program, a, n) = false

const illegal_combinations1 = Set([
    #  McCarthy primitives
    (1, "car", "cons"),
    (1, "car", "empty"),
    (1, "car", "repeat"),
    (1, "cdr", "cons"),
    (1, "cdr", "empty"),
    (2, "-", "0"),
    (1, "+", "+"),
    (1, "*", "*"),
    (1, "empty?", "cons"),
    (1, "empty?", "empty"),
    (1, "zero?", "0"),
    (1, "zero?", "1"),
    (1, "zero?", "-1"),
    #  bootstrap target
    (2, "map", "empty"),
    (2, "fold", "empty"),
    (2, "index", "empty"),
    (2, "index", "repeat"),
    (3, "index2", "repeat_grid"),
])

const illegal_combinations2 = Set([
    ("+", "0"),
    ("*", "0"),
    ("*", "1"),
    ("zip", "empty"),
    ("left", "left"),
    ("left", "right"),
    ("right", "right"),
    ("right", "left"),
    ("abs", "abs"),
    ("tuple2_first", "tuple2"),
    ("tuple2_second", "tuple2"),
    #   ("tower_embed","tower_embed")
])

function violates_symmetry(f::Primitive, a, n)
    a = application_function(a)
    if !isa(a, Primitive)
        return false
    end
    return in((n, f.name, a.name), illegal_combinations1) || in((f.name, a.name), illegal_combinations2)
end

has_index(p::Index, i) = p.n == i
has_index(p::Hole, i) = p.candidates_filter.max_index >= i
has_index(p::Primitive, i) = false
has_index(p::Invented, i) = false
has_index(p::Apply, i) = has_index(p.f, i) || has_index(p.x, i)
has_index(p::FreeVar, i) = false
has_index(p::Abstraction, i) = has_index(p.b, i + 1)

new_free_vars_count(p::FreeVar) = isnothing(p.var_id) ? 1 : 0
new_free_vars_count(p::Abstraction) = new_free_vars_count(p.b)
new_free_vars_count(p::Apply) = new_free_vars_count(p.f) + new_free_vars_count(p.x)
new_free_vars_count(p) = 0

subprograms_equal(p1, p2, var_shift) = p1 == p2
subprograms_equal(p1::Apply, p2::Apply, var_shift) =  # TODO: new free vars count can be optimized
    subprograms_equal(p1.f, p2.f, var_shift) && subprograms_equal(p1.x, p2.x, var_shift + new_free_vars_count(p1.f))

subprograms_equal(p1::Abstraction, p2::Abstraction, var_shift) = subprograms_equal(p1.b, p2.b, var_shift)

function subprograms_equal(p1::FreeVar, p2::FreeVar, var_shift)
    if !isnothing(p1.var_id)
        return p1.var_id == p2.var_id
    end
    if !isnothing(p2.var_id)
        return p2.var_id == "r$(var_shift + 1)"
    end
    return false
end

state_violates_symmetry(p::Abstraction, var_shift = 0)::Bool =
    state_violates_symmetry(p.b, var_shift) || !has_index(p.b, 0)

function state_violates_symmetry(p::Apply, var_shift = 0)::Bool
    (f, a) = application_parse(p)
    if f == every_primitive["rev_fix_param"]
        if isa(a[1], FreeVar) || isa(a[1], Index)
            return true
        end
        if isa(a[3], Abstraction)
            a[3] = a[3].b
        end
    end
    if state_violates_symmetry(f, var_shift)
        return true
    end
    if f == every_primitive["eq?"] && _has_no_holes(a[1]) && _has_no_holes(a[2])
        if subprograms_equal(a[1], a[2], var_shift)
            return true
        end
    end
    if f == every_primitive["if"] && _has_no_holes(a[2]) && _has_no_holes(a[3])
        cond_var_shift = new_free_vars_count(a[1])
        if subprograms_equal(a[2], a[3], var_shift + cond_var_shift)
            return true
        end
    end
    var_shift += new_free_vars_count(f)
    for (n, x) in enumerate(a)
        if state_violates_symmetry(x, var_shift) || violates_symmetry(f, x, n)
            return true
        end
        var_shift += new_free_vars_count(x)
    end
    return false
end
state_violates_symmetry(::Program, var_shift = 0)::Bool = false

function check_valid_program_location(sc, p, var_id, is_forward)
    root_locations = is_forward ? sc.unknown_var_locations[var_id] : sc.known_var_locations[var_id]
    for (f, ind) in root_locations
        if violates_symmetry(f, p, ind)
            return false
        end
    end
    return true
end

capture_free_vars(p::Program, context) = _capture_free_vars(p, context, [])

_capture_free_vars(p::Program, context, captured_vars) = p, captured_vars

function _capture_free_vars(p::Apply, context, captured_vars)
    new_f, captured_vars = _capture_free_vars(p.f, context, captured_vars)
    new_x, captured_vars = _capture_free_vars(p.x, context, captured_vars)
    Apply(new_f, new_x), captured_vars
end

function _capture_free_vars(p::Abstraction, context, captured_vars)
    new_b, captured_vars = _capture_free_vars(p.b, context, captured_vars)
    Abstraction(new_b), captured_vars
end

function _capture_free_vars(p::Hole, context, captured_vars)
    _, t = apply_context(context, p.t)
    var_id = UInt64(length(captured_vars) + 1)
    push!(captured_vars, (var_id, t))

    FreeVar(t, var_id, isempty(p.locations) ? nothing : p.locations[1]), captured_vars
end

function _capture_free_vars(p::FreeVar, context, captured_vars)
    if isnothing(p.var_id)
        _, t = apply_context(context, p.t)
        var_id = UInt64(length(captured_vars) + 1)
        push!(captured_vars, (var_id, t))
    elseif isa(p.var_id, UInt64)
        var_id = p.var_id
        t = p.t
        if !in((var_id, t), captured_vars)
            push!(captured_vars, (var_id, t))
        end
    else
        i = parse(Int, p.var_id[2:end])
        var_id, t = captured_vars[i]
    end
    FreeVar(t, var_id, p.location), captured_vars
end

capture_new_free_vars(sc, p) = _capture_new_free_vars(sc, p, Dict(), [])

_capture_new_free_vars(sc, p::Program, captured_vars_mapping, captured_vars) = p, captured_vars

function _capture_new_free_vars(sc, p::FreeVar, captured_vars_mapping, captured_vars)
    if haskey(captured_vars_mapping, p.var_id)
        return FreeVar(p.t, captured_vars_mapping[p.var_id], p.location), captured_vars
    else
        var_id = create_next_var(sc)
        push!(captured_vars, var_id)
        captured_vars_mapping[p.var_id] = var_id
        return FreeVar(p.t, var_id, p.location), captured_vars
    end
end

function _capture_new_free_vars(sc, p::Apply, captured_vars_mapping, captured_vars)
    new_f, captured_vars = _capture_new_free_vars(sc, p.f, captured_vars_mapping, captured_vars)
    new_x, captured_vars = _capture_new_free_vars(sc, p.x, captured_vars_mapping, captured_vars)
    Apply(new_f, new_x), captured_vars
end

function _capture_new_free_vars(sc, p::Abstraction, captured_vars_mapping, captured_vars)
    new_b, captured_vars = _capture_new_free_vars(sc, p.b, captured_vars_mapping, captured_vars)
    Abstraction(new_b), captured_vars
end

function check_reversed_program_forward(p, vars, inputs, expected_output)
    if any(isa(v, EitherOptions) for v in inputs)
        either_val = first(v for v in inputs if isa(v, EitherOptions))
        hashes = keys(either_val.options)
        for (i, h) in enumerate(hashes)
            if i > 10
                break
            end
            inps = [fix_option_hashes([h], v) for v in inputs]
            exp_out = fix_option_hashes([h], expected_output)
            check_reversed_program_forward(p, vars, inps, exp_out)
        end
    elseif any(isa(v, PatternWrapper) for v in inputs)
        inps = [isa(v, PatternWrapper) ? v.value : v for v in inputs]
        check_reversed_program_forward(p, vars, inps, expected_output)
    else
        output = try
            try_evaluate_program(p, [], Dict(v_id => v for ((v_id, _), v) in zip(vars, inputs)))
        catch e
            if isa(e, InterruptException)
                rethrow()
            end
            @error(p)
            @error(vars)
            @error inputs
            @error expected_output
            @error e
            error("Can't run reversed program forward")
        end
        if output != expected_output
            @error(p)
            @error(vars)
            @error inputs
            @error output
            @error expected_output
            # error("Can't run reversed program forward")
        end
    end
end

function try_get_reversed_values(sc::SolutionContext, p::Program, context, root_entry, block_id = UInt64(0))
    out_entry = sc.entries[root_entry]

    new_p, new_vars = capture_free_vars(p, context)
    new_vars_count = length(new_vars)

    calculated_values = DefaultDict(() -> [])
    for value in out_entry.values
        calculated_value = try_run_function(run_in_reverse, [new_p, value, block_id])
        if length(calculated_value) != new_vars_count
            @warn p
            @warn new_p
            @warn new_vars
            @warn value
            @warn calculated_value
        end
        # check_reversed_program_forward(new_p, new_vars, calculated_value, value)
        for (k, v) in calculated_value
            push!(calculated_values[k], v)
        end
    end

    new_entries = []
    has_eithers = false
    has_abductibles = false
    unfixed_vars = []

    for (var_id, t) in new_vars
        vals = calculated_values[var_id]
        complexity_summary, max_summary, options_count = get_complexity_summary(vals, t)
        t_id = push!(sc.types, t)
        if any(isa(value, EitherOptions) for value in vals)
            has_eithers = true
            new_entry = EitherEntry(
                t_id,
                vals,
                complexity_summary,
                max_summary,
                options_count,
                get_complexity(sc, complexity_summary),
            )
            push!(unfixed_vars, var_id)
        elseif any(isa(value, PatternWrapper) for value in vals)
            new_entry = PatternEntry(
                t_id,
                vals,
                complexity_summary,
                max_summary,
                options_count,
                get_complexity(sc, complexity_summary),
            )
        elseif any(isa(value, AbductibleValue) for value in vals)
            has_abductibles = true
            new_entry = AbductibleEntry(
                t_id,
                vals,
                complexity_summary,
                max_summary,
                options_count,
                get_complexity(sc, complexity_summary),
            )
            push!(unfixed_vars, var_id)
        else
            new_entry = ValueEntry(
                t_id,
                vals,
                complexity_summary,
                max_summary,
                options_count,
                get_complexity(sc, complexity_summary),
            )
        end
        if !sc.traced && new_entry == out_entry
            throw(EnumerationException())
        end
        entry_index = push!(sc.entries, new_entry)
        push!(new_entries, (var_id, entry_index, t_id))
    end

    return new_p, new_entries, unfixed_vars, has_eithers, has_abductibles
end

function _fill_holes(p::Hole, context)
    new_context, t = apply_context(context, p.t)
    FreeVar(t, nothing, isempty(p.locations) ? nothing : p.locations[1]), new_context
end
function _fill_holes(p::Apply, context)
    new_f, new_context = _fill_holes(p.f, context)
    new_x, new_context = _fill_holes(p.x, new_context)
    Apply(new_f, new_x), new_context
end
function _fill_holes(p::Abstraction, context)
    new_b, new_context = _fill_holes(p.b, context)
    Abstraction(new_b), new_context
end
_fill_holes(p::Program, context) = p, context

function try_run_function(f::Function, xs)
    try
        f(xs...)
    catch e
        #  We have to be a bit careful with exceptions if the
        #     synthesized program generated an exception, then we just
        #     terminate w/ false but if the enumeration timeout was
        #     triggered during program evaluation, we need to pass the
        #     exception on
        if isa(e, InterruptException)
            @warn "Interrupted running $f with $xs"
            rethrow()
        elseif isa(e, UnknownPrimitive)
            error("Unknown primitive: $(e.name)")
        elseif isa(e, MethodError)
            @error f
            @error(xs)
            rethrow()
        else
            # @error "Error while running $f with $xs" exception = (e, catch_backtrace())
            throw(EnumerationException())
        end
    end
end

function try_evaluate_program(p, xs, workspace)
    try_run_function(run_with_arguments, [p, xs, workspace])
end

function _update_block_type(block_type, input_types)
    if !is_polymorphic(block_type)
        return block_type
    end
    context, block_type = instantiate(block_type, empty_context)
    for (arg_type, inp_type) in zip(arguments_of_type(block_type), input_types)
        context, inp_type = instantiate(inp_type, context)
        context = unify(context, arg_type, inp_type)
        if isnothing(context)
            error("Can't unify $arg_type with $inp_type")
        end
    end
    context, block_type = apply_context(context, block_type)
    return block_type
end

function _update_block_output_type(block_type, output_type)
    return block_type
    if !is_polymorphic(block_type)
        return block_type
    end

    context, block_type = instantiate(block_type, empty_context)
    context, output_type = instantiate(output_type, context)
    context = unify(context, return_of_type(block_type), output_type)
    if isnothing(context)
        error("Can't unify $(return_of_type(block_type)) with $output_type")
    end
    context, block_type = apply_context(context, block_type)
    return block_type
end

function try_run_block(
    sc::SolutionContext,
    block::ProgramBlock,
    block_id,
    fixed_branches,
    target_output,
    is_new_block,
    created_paths,
)
    inputs = []
    for _ in 1:sc.example_count
        push!(inputs, Dict())
    end
    input_types = []
    has_non_consts = false
    for var_id in block.input_vars
        fixed_branch_id = fixed_branches[var_id]
        if sc.branch_is_not_const[fixed_branch_id]
            has_non_consts = true
        end
        entry = sc.entries[sc.branch_entries[fixed_branch_id]]
        push!(input_types, sc.types[entry.type_id])
        for i in 1:sc.example_count
            inputs[i][var_id] = entry.values[i]
        end
    end
    if !has_non_consts && length(block.input_vars) > 0 && !isa(block.p, FreeVar)
        if sc.verbose
            @info "Aborting $block_id $(block.p) because all inputs are const"
        end
        throw(EnumerationException())
    end

    out_branch_id = target_output[block.output_var]
    expected_output = sc.entries[sc.branch_entries[out_branch_id]]

    outs = []
    for i in 1:sc.example_count
        xs = inputs[i]
        out_value = try
            try_evaluate_program(block.p, [], xs)
        catch e
            if !isa(e, EnumerationException)
                @error e
                @error xs
                @error block.p
            end
            rethrow()
        end
        if isnothing(out_value) || !match_at_index(expected_output, i, out_value)
            if sc.verbose
                if isnothing(out_value)
                    @info "Got nothing for $(block.p) $xs"
                else
                    @info "Can't match $out_value for $(block.p) with $expected_output at $i"
                end
            end
            throw(EnumerationException())
        end
        push!(outs, out_value)
    end
    return value_updates(
        sc,
        block,
        block_id,
        _update_block_type(block.type, input_types),
        target_output,
        outs,
        fixed_branches,
        is_new_block,
        created_paths,
    )
end

function try_run_block(
    sc::SolutionContext,
    block::ReverseProgramBlock,
    block_id,
    fixed_branches,
    target_output,
    is_new_block,
    created_paths,
)
    inputs = []
    input_types = []
    for _ in 1:sc.example_count
        push!(inputs, [])
    end
    for var_id in block.input_vars
        fixed_branch_id = fixed_branches[var_id]
        entry = sc.entries[sc.branch_entries[fixed_branch_id]]
        push!(input_types, sc.types[entry.type_id])
        for i in 1:sc.example_count
            push!(inputs[i], entry.values[i])
        end
    end

    out_entries = Dict(var_id => sc.entries[sc.branch_entries[target_output[var_id]]] for var_id in block.output_vars)

    outs = DefaultDict(() -> [])

    for i in 1:sc.example_count
        xs = inputs[i]
        out_values = try
            try_run_function(run_in_reverse, vcat([block.p], xs, [block_id]))
        catch e
            @error xs
            @error block.p
            rethrow()
        end
        if isnothing(out_values)
            throw(EnumerationException())
        end
        for (v_id, v) in out_values
            if !match_at_index(out_entries[v_id], i, v)
                throw(EnumerationException())
            end
            push!(outs[v_id], v)
        end
    end
    return value_updates(
        sc,
        block,
        block_id,
        _update_block_output_type(block.type, input_types[1]),
        target_output,
        [outs[v_id] for v_id in block.output_vars],
        fixed_branches,
        is_new_block,
        created_paths,
    )
end

function try_run_block_with_downstream(
    sc::SolutionContext,
    block_id,
    fixed_branches,
    target_output,
    is_new_block,
    created_paths,
)
    if sc.verbose
        inputs = Dict(
            var_id => (
                fixed_branches[var_id],
                sc.branch_entries[fixed_branches[var_id]],
                sc.types[sc.entries[sc.branch_entries[fixed_branches[var_id]]].type_id],
                sc.branch_is_not_const[fixed_branches[var_id]],
                sc.entries[sc.branch_entries[fixed_branches[var_id]]],
            ) for var_id in sc.blocks[block_id].input_vars
        )
        outputs = Dict(
            var_id => (
                br_id,
                sc.branch_entries[br_id],
                sc.types[sc.entries[sc.branch_entries[br_id]].type_id],
                sc.entries[sc.branch_entries[br_id]],
            ) for (var_id, br_id) in target_output
        )
        @info "Running $block_id $(sc.blocks[block_id]) with inputs $inputs and output $outputs"
    end
    # @info fixed_branches
    block = sc.blocks[block_id]

    out_branches, is_new_out_branch, is_new_next_block, allow_fails, next_blocks, set_explained, block_created_paths =
        try_run_block(sc, block, block_id, fixed_branches, target_output, is_new_block, created_paths)
    # @info target_output
    # @info out_branches

    if sc.verbose
        @info "Is new block $is_new_block is new next block $is_new_next_block set explained $set_explained"
        @info "Created paths for $block_id: $block_created_paths"
        @info "Next blocks: $next_blocks"
    end
    new_paths = merge(created_paths, block_created_paths)

    if is_new_block || is_new_out_branch
        _save_block_branch_connections(sc, block_id, block, fixed_branches, UInt64[b_id for (_, b_id) in out_branches])
    end
    if is_new_block || set_explained
        update_complexity_factors_known(sc, block, fixed_branches, out_branches)
        for (v_id, _) in out_branches
            if isnothing(sc.known_var_locations[v_id])
                sc.known_var_locations[v_id] = []
            end
        end
    end

    for (b_id, downstream_branches, downstream_target) in next_blocks
        next_block = sc.blocks[b_id]
        if !have_valid_paths(sc, [downstream_branches[v_id] for v_id in next_block.input_vars])
            continue
        end
        if allow_fails
            transaction(sc) do
                try_run_block_with_downstream(
                    sc,
                    b_id,
                    downstream_branches,
                    downstream_target,
                    is_new_next_block,
                    new_paths,
                )
            end
        else
            try_run_block_with_downstream(
                sc,
                b_id,
                downstream_branches,
                downstream_target,
                is_new_next_block,
                new_paths,
            )
        end
    end
end

function add_new_block(sc::SolutionContext, block_id, inputs, target_output)
    # assert_context_consistency(sc)
    if sc.verbose
        @info "Adding block $block_id $(sc.blocks[block_id]) $inputs $target_output"
    end
    update_prev_follow_vars(sc, block_id)
    if all(sc.branch_is_explained[branch_id] for (var_id, branch_id) in inputs)
        # if length(inputs) > 1
        #     error("Not implemented, fix active constraints")
        # end
        try_run_block_with_downstream(sc, block_id, inputs, target_output, true, Dict())
        # assert_context_consistency(sc)
    else
        block = sc.blocks[block_id]
        _save_block_branch_connections(sc, block_id, block, inputs, UInt64[b_id for (_, b_id) in target_output])
        if all(sc.branch_is_unknown[branch_id] for (var_id, branch_id) in inputs)
            update_complexity_factors_unknown(sc, inputs, target_output[block.output_var])
        else
            # error("Not implemented")
        end
    end
    if sc.verbose
        @info "Inserted block $block_id"
    end
    result = update_context(sc)
    return result
end

include("extract_solution.jl")

struct HitResult
    hit_program::String
    hit_prior::Any
    hit_likelihood::Any
    hit_time::Any
    trace_values::Any
end

Base.hash(r::HitResult, h::UInt64) = hash(r.hit_program, h)
Base.:(==)(r1::HitResult, r2::HitResult) = r1.hit_program == r2.hit_program

function log_results(sc, hits)
    @info(collect(keys(hits)))

    if sc.verbose
        @info "Branches with incoming paths $(length(sc.incoming_paths.values_stack[1]))"
        @info "Total incoming paths $(sum(length(v) for v in values(sc.incoming_paths.values_stack[1])))"
        @info "Incoming paths counts $([length(v) for v in values(sc.incoming_paths.values_stack[1])])"
        @info "Entries for incoming paths "
        for (br_id, v) in sc.incoming_paths.values_stack[1]
            @info (
                length(v),
                length(unique(v)),
                br_id,
                sc.branch_vars[br_id],
                sc.branch_entries[br_id],
                sc.entries[sc.branch_entries[br_id]],
                [sc.blocks[b_id] for (_, b_id) in get_connected_from(sc.branch_incoming_blocks, br_id)],
            )
            if length(v) != length(unique(v))
                @warn "Incoming paths for branch $br_id"
                @warn v
            end
        end
        @info "Total incoming paths length $(sum(sum(length(path.main_path) + length(path.side_vars) for path in paths; init=0) for paths in values(sc.incoming_paths.values_stack[1]); init=0))"
    end

    @info "Iterations count $(sc.iterations_count)"
    @info "Total number of valid blocks $(sc.total_number_of_enumerated_programs)"

    if !isempty(sc.stats)
        @info "Got $(length(sc.stats["run"])) guidance responses"
    end
    for (k, ts) in sc.stats
        @info "Average model $k time $(mean(ts))"
        @info "Maximum model $k time $(maximum(ts))"
        @info "Total model $k time $(sum(ts))"
    end
end
