
abstract type Turn end

struct LeftTurn <: Turn end
struct RightTurn <: Turn end
struct ArgTurn <: Turn
    type::Tp
end

Base.:(==)(a::ArgTurn, b::ArgTurn) = a.type == b.type

Base.hash(a::ArgTurn, h::UInt) = hash(a.type, h)

struct EnumerationState
    skeleton::Program
    context::Context
    path::Vector{Turn}
    cost::Float64
    free_parameters::Int64
    abstractors_only::Bool
end

Base.:(==)(a::EnumerationState, b::EnumerationState) =
    a.skeleton == b.skeleton &&
    a.context == b.context &&
    a.path == b.path &&
    a.cost == b.cost &&
    a.free_parameters == b.free_parameters &&
    a.abstractors_only == b.abstractors_only

Base.hash(a::EnumerationState, h::UInt) =
    hash(a.skeleton, hash(a.context, hash(a.path, hash(a.cost, hash(a.free_parameters, hash(a.abstractors_only, h))))))

struct BlockPrototype
    state::EnumerationState
    request::Tp
    input_vars::Union{Dict{Int,Int},Nothing}
    output_var::Tuple{Int,Int}
    reverse::Bool
end

Base.:(==)(a::BlockPrototype, b::BlockPrototype) =
    a.state == b.state &&
    a.request == b.request &&
    a.input_vars == b.input_vars &&
    a.output_var == b.output_var &&
    a.reverse == b.reverse

Base.hash(a::BlockPrototype, h::UInt) =
    hash(a.state, hash(a.request, hash(a.input_vars, hash(a.output_var, hash(a.reverse, h)))))

EPSILON = 1e-3

function block_prototype(pr, inputs, output_var_id, output_branch_id, output_type)
    BlockPrototype(
        EnumerationState(pr, empty_context, [], EPSILON, 0, false),
        output_type,
        inputs,
        (output_var_id, output_branch_id),
        false,
    )
end

function get_const_options(sc, unknown_entry)
    candidates = const_options(unknown_entry)
    if isempty(candidates)
        return []
    end
    matching_seq = get_matching_seq(unknown_entry)
    for matcher in matching_seq
        filter!(c -> matcher(c), candidates)
        if isempty(candidates)
            return []
        end
    end
    t = sc.types[unknown_entry.type_id]
    return [SetConst(t, candidate) for candidate in candidates]
end

function get_candidates_for_unknown_var(sc, branch_id, g)::Vector{BlockPrototype}
    var_id = sc.branch_vars[branch_id]
    type_id = nonzeroinds(sc.branch_types[branch_id, :])[1]
    type = sc.types[type_id]
    entry = sc.entries[sc.branch_entries[branch_id]]
    prototypes = []
    if !isa(entry, NoDataEntry)
        push!(prototypes, block_prototype(Hole(type, g.no_context), nothing, var_id, branch_id, type))
    end
    for (pr, inputs, out_type) in matching_with_unknown_candidates(sc, entry, var_id)
        push!(prototypes, block_prototype(pr, inputs, var_id, branch_id, out_type))
    end
    entry_type = sc.types[entry.type_id]
    for pr in get_const_options(sc, entry)
        push!(prototypes, block_prototype(pr, Dict(), var_id, branch_id, entry_type))
    end
    prototypes
end

function get_candidates_for_known_var(sc, branch_id, g::ContextualGrammar)
    prototypes = []
    var_id = sc.branch_vars[branch_id]
    if !isnothing(sc.explained_min_path_costs[branch_id])
        type_id = nonzeroinds(sc.branch_types[branch_id, :])[1]
        type = sc.types[type_id]
        push!(
            prototypes,
            BlockPrototype(
                EnumerationState(Hole(type, g.no_context), empty_context, [], EPSILON, 0, true),
                type,
                nothing,
                (var_id, branch_id),
                true,
            ),
        )
    end
    entry = sc.entries[sc.branch_entries[branch_id]]
    for (pr, output_var_id, output_br_id, out_type) in matching_with_known_candidates(sc, entry, branch_id)
        push!(prototypes, block_prototype(pr, Dict(var_id => branch_id), output_var_id, output_br_id, out_type))
    end
    prototypes
end

function enqueue_known_var(sc, branch_id, g)
    if branch_id == sc.target_branch_id
        return
    end
    prototypes = get_candidates_for_known_var(sc, branch_id, g)
    if haskey(sc.branch_queues_explained, branch_id)
        q = sc.branch_queues_explained[branch_id]
    else
        q = PriorityQueue()
    end
    for bp in prototypes
        if sc.verbose
            @info "enqueueing $bp"
        end
        if (isnothing(bp.input_vars) || all(br -> sc.branch_is_explained[br[2]], bp.input_vars)) &&
           !isnothing(sc.explained_min_path_costs[branch_id])
            q[bp] = bp.state.cost
        else
            out_branch_id = bp.output_var[2]
            if !haskey(sc.branch_queues_unknown, out_branch_id)
                sc.branch_queues_unknown[out_branch_id] = PriorityQueue()
            end
            out_q = sc.branch_queues_unknown[out_branch_id]
            out_q[bp] = bp.state.cost
            update_branch_priority(sc, out_branch_id, false)
        end
    end
    sc.branch_queues_explained[branch_id] = q
    if !isempty(q)
        update_branch_priority(sc, branch_id, true)
    end
end

function enqueue_unknown_var(sc, branch_id, g)
    prototypes = get_candidates_for_unknown_var(sc, branch_id, g)
    if haskey(sc.branch_queues_unknown, branch_id)
        q = sc.branch_queues_unknown[branch_id]
    else
        q = PriorityQueue()
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
                sc.branch_queues_explained[inp_branch_id] = PriorityQueue()
            end
            in_q = sc.branch_queues_explained[inp_branch_id]
            in_q[bp] = bp.state.cost
            update_branch_priority(sc, inp_branch_id, true)
        else
            q[bp] = bp.state.cost
        end
    end
    if !isempty(q)
        sc.branch_queues_unknown[branch_id] = q
        update_branch_priority(sc, branch_id, false)
    end
end

state_finished(state::EnumerationState) =
    if isa(state.skeleton, Hole)
        false
    else
        isempty(state.path)
    end
