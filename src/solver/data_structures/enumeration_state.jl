
abstract type Turn end

struct LeftTurn <: Turn end
struct RightTurn <: Turn end
struct ArgTurn <: Turn
    type::Tp
end

Base.:(==)(a::ArgTurn, b::ArgTurn) = a.type == b.type

Base.hash(a::ArgTurn, h::UInt) = hash(a.type, h)

struct BlockPrototype
    skeleton::Program
    context::Context
    path::Vector{Turn}
    cost::Float64
    free_parameters::Int64
    request::Tp
    input_vars::Union{Dict{UInt64,UInt64},Nothing}
    output_var::Tuple{UInt64,UInt64}
    reverse::Bool
end

Base.:(==)(a::BlockPrototype, b::BlockPrototype) =
    a.skeleton == b.skeleton &&
    a.context == b.context &&
    a.path == b.path &&
    a.cost == b.cost &&
    a.free_parameters == b.free_parameters &&
    a.request == b.request &&
    a.input_vars == b.input_vars &&
    a.output_var == b.output_var &&
    a.reverse == b.reverse

Base.hash(a::BlockPrototype, h::UInt) = hash(
    a.skeleton,
    hash(
        a.context,
        hash(
            a.path,
            hash(
                a.cost,
                hash(a.free_parameters, hash(a.request, hash(a.input_vars, hash(a.output_var, hash(a.reverse, h))))),
            ),
        ),
    ),
)

EPSILON = 1e-3
MATCH_DUPLICATES_PENALTY = 3

function block_prototype(pr, inputs, output_var_id, output_branch_id, output_type, prev_matches_count)
    BlockPrototype(
        pr,
        empty_context,
        [],
        EPSILON + MATCH_DUPLICATES_PENALTY * prev_matches_count,
        0,
        output_type,
        inputs,
        (output_var_id, output_branch_id),
        false,
    )
end

function get_candidates_for_unknown_var(sc, branch_id, guiding_model_channels, grammar)::Vector{BlockPrototype}
    var_id = sc.branch_vars[branch_id]
    type_id = first(get_connected_from(sc.branch_types, branch_id))
    type = sc.types[type_id]
    entry_id = sc.branch_entries[branch_id]
    entry = sc.entries[entry_id]
    prototypes = []
    if !isa(entry, NoDataEntry) && sc.complexities[branch_id] > 0
        context, type = instantiate(type, empty_context)
        if !haskey(sc.entry_grammars, (entry_id, false))
            g = generate_grammar(sc, guiding_model_channels, grammar, entry_id, false)
            sc.entry_grammars[(entry_id, false)] = g
        end
        push!(
            prototypes,
            BlockPrototype(
                Hole(
                    type,
                    nothing,
                    sc.unknown_var_locations[var_id],
                    CombinedArgChecker([SimpleArgChecker(false, -1, true)]),
                    entry.values,
                ),
                context,
                [],
                EPSILON,
                0,
                type,
                nothing,
                (var_id, branch_id),
                false,
            ),
        )
    end
    for (pr, inputs, out_type, prev_matches_count) in matching_with_unknown_candidates(sc, entry, branch_id)
        push!(prototypes, block_prototype(pr, inputs, var_id, branch_id, out_type, prev_matches_count))
    end
    prototypes
end

function get_candidates_for_known_var(sc, branch_id, guiding_model_channels, grammar)
    prototypes = []
    var_id = sc.branch_vars[branch_id]
    entry_id = sc.branch_entries[branch_id]
    entry = sc.entries[entry_id]
    if !isnothing(sc.explained_min_path_costs[branch_id]) && entry.complexity > 0
        type_id = first(get_connected_from(sc.branch_types, branch_id))
        type = sc.types[type_id]
        context, type = instantiate(type, empty_context)

        if !haskey(sc.entry_grammars, (entry_id, true))
            g = generate_grammar(sc, guiding_model_channels, grammar, entry_id, true)
            sc.entry_grammars[(entry_id, true)] = g
        end

        push!(
            prototypes,
            BlockPrototype(
                Hole(
                    type,
                    nothing,
                    sc.known_var_locations[var_id],
                    CombinedArgChecker([SimpleArgChecker(true, -1, true)]),
                    nothing,
                ),
                context,
                [],
                EPSILON,
                0,
                type,
                nothing,
                (var_id, branch_id),
                true,
            ),
        )
    end
    for (pr, output_var_id, output_br_id, out_type, prev_matches_count) in
        matching_with_known_candidates(sc, entry, branch_id)
        push!(
            prototypes,
            block_prototype(pr, Dict(var_id => branch_id), output_var_id, output_br_id, out_type, prev_matches_count),
        )
    end
    prototypes
end

function enqueue_known_var(sc, branch_id, guiding_model_channels, grammar)
    if branch_id == sc.target_branch_id
        return
    end
    prototypes = get_candidates_for_known_var(sc, branch_id, guiding_model_channels, grammar)
    if haskey(sc.branch_queues_explained, branch_id)
        q = sc.branch_queues_explained[branch_id]
    else
        q = PriorityQueue{BlockPrototype,Float64}()
    end
    for bp in prototypes
        if sc.verbose
            @info "enqueueing $bp"
        end
        if (isnothing(bp.input_vars) || all(br -> sc.branch_is_explained[br[2]], bp.input_vars)) &&
           !isnothing(sc.explained_min_path_costs[branch_id])
            q[bp] = bp.cost
        else
            out_branch_id = bp.output_var[2]
            if !haskey(sc.branch_queues_unknown, out_branch_id)
                sc.branch_queues_unknown[out_branch_id] = PriorityQueue{BlockPrototype,Float64}()
            end
            out_q = sc.branch_queues_unknown[out_branch_id]
            out_q[bp] = bp.cost
            update_branch_priority(sc, out_branch_id, false)
        end
    end
    sc.branch_queues_explained[branch_id] = q
    if !isempty(q)
        update_branch_priority(sc, branch_id, true)
    end
end

function enqueue_unknown_var(sc, branch_id, guiding_model_channels, grammar)
    prototypes = get_candidates_for_unknown_var(sc, branch_id, guiding_model_channels, grammar)
    if haskey(sc.branch_queues_unknown, branch_id)
        q = sc.branch_queues_unknown[branch_id]
    else
        q = PriorityQueue{BlockPrototype,Float64}()
    end
    for bp in prototypes
        if sc.verbose
            @info "enqueueing $bp"
        end
        if !isnothing(bp.input_vars) &&
           !isempty(bp.input_vars) &&
           all(br -> sc.branch_is_explained[br[2]], bp.input_vars) &&
           !isnothing(sc.explained_min_path_costs[first(bp.input_vars)[2]])
            inp_branch_id = first(bp.input_vars)[2]
            if !haskey(sc.branch_queues_explained, inp_branch_id)
                sc.branch_queues_explained[inp_branch_id] = PriorityQueue{BlockPrototype,Float64}()
            end
            in_q = sc.branch_queues_explained[inp_branch_id]
            in_q[bp] = bp.cost
            update_branch_priority(sc, inp_branch_id, true)
        else
            q[bp] = bp.cost
        end
    end
    if !isempty(q)
        sc.branch_queues_unknown[branch_id] = q
        update_branch_priority(sc, branch_id, false)
    end
end

state_finished(bp::BlockPrototype) =
    if isa(bp.skeleton, Hole)
        false
    else
        isempty(bp.path)
    end
