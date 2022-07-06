

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
    abstractors_only::Bool
end


struct BlockPrototype
    state::EnumerationState
    request::Tp
    input_vars::Union{Vector{Tuple{String,EntryBranch}},Nothing}
    output_var::Union{Tuple{String,EntryBranch},Nothing}
    reverse::Bool
end


function block_prototype(pr, inputs, output_branch, output_type)
    BlockPrototype(
        EnumerationState(pr, empty_context, [], 0.0, 0, false),
        output_type,
        inputs,
        (output_branch.key, output_branch),
        false,
    )
end

function get_const_options(unknown_entry)
    candidates = const_options(unknown_entry)
    if isempty(candidates)
        return []
    end
    matching_seq = get_matching_seq(unknown_entry)
    for matcher in matching_seq
        filter!(c -> matcher(c) != NoMatch, candidates)
        if isempty(candidates)
            return []
        end
    end
    return [SetConst(unknown_entry.type, candidate) for candidate in candidates]

end

function get_candidates_for_unknown_var(sc, branch::EntryBranch, g)::Vector{BlockPrototype}
    entry = get_entry(sc.entries_storage, branch.value_index)
    prototypes = []
    if !isa(entry, NoDataEntry)
        push!(prototypes, block_prototype(Hole(branch.type, g.no_context), nothing, branch, branch.type))
    end
    for (pr, inputs, out_type) in matching_with_unknown_candidates(sc, entry, branch.key)
        push!(prototypes, block_prototype(pr, inputs, branch, out_type))
    end
    for pr in get_const_options(entry)
        push!(prototypes, block_prototype(pr, [], branch, entry.type))
    end
    prototypes
end

function get_candidates_for_known_var(sc, branch, g::ContextualGrammar)
    prototypes = []
    entry = get_entry(sc.entries_storage, branch.value_index)
    if !isnothing(branch.min_path_cost)
        push!(
            prototypes,
            BlockPrototype(
                EnumerationState(Hole(branch.type, g.no_context), empty_context, [], 0.0, 0, true),
                branch.type,
                nothing,
                (branch.key, branch),
                true,
            ),
        )
    end
    for (pr, output, out_type) in matching_with_known_candidates(sc, entry, branch)
        push!(prototypes, block_prototype(pr, [(branch.key, branch)], output, out_type))
    end
    prototypes
end

function enqueue_known_var(sc, branch::EntryBranch, g)
    if !branch.is_meaningful
        return
    end
    prototypes = get_candidates_for_known_var(sc, branch, g)
    if haskey(sc.branch_queues, branch)
        q = sc.branch_queues[branch]
    else
        q = PriorityQueue()
    end
    for bp in prototypes
        # @info "enqueueing $bp"
        if (isnothing(bp.input_vars) || all(br -> br[2].is_known, bp.input_vars)) && !isnothing(branch.min_path_cost)
            q[bp] = bp.state.cost
        else
            out_branch = bp.output_var[2]
            if !haskey(sc.branch_queues, out_branch)
                sc.branch_queues[out_branch] = PriorityQueue()
            end
            out_q = sc.branch_queues[out_branch]
            out_q[bp] = bp.state.cost
            min_cost = peek(out_q)[2]
            sc.pq_output[out_branch] = (out_branch.min_path_cost + min_cost) * out_branch.complexity_factor
        end
    end
    if !isempty(q)
        sc.branch_queues[branch] = q
        min_cost = peek(q)[2]
        sc.pq_input[branch] = (branch.min_path_cost + min_cost) * branch.complexity_factor
    end
end

function enqueue_unknown_var(sc, branch, g)
    prototypes = get_candidates_for_unknown_var(sc, branch, g)
    if haskey(sc.branch_queues, branch)
        q = sc.branch_queues[branch]
    else
        q = PriorityQueue()
    end
    for bp in prototypes
        # @info "enqueueing $bp"
        if !isnothing(bp.input_vars) && !isempty(bp.input_vars) &&
           all(br -> br[2].is_known, bp.input_vars) &&
           !isnothing(bp.input_vars[1][2].min_path_cost)
            inp_branch = bp.input_vars[1][2]
            if !haskey(sc.branch_queues, inp_branch)
                sc.branch_queues[inp_branch] = PriorityQueue()
            end
            in_q = sc.branch_queues[inp_branch]
            in_q[bp] = bp.state.cost
            min_cost = peek(in_q)[2]
            sc.pq_input[inp_branch] = (inp_branch.min_path_cost + min_cost) * inp_branch.complexity_factor
        else
            q[bp] = bp.state.cost
        end
    end
    if !isempty(q)
        sc.branch_queues[branch] = q
        min_cost = peek(q)[2]
        sc.pq_output[branch] = (branch.min_path_cost + min_cost) * branch.complexity_factor
    end
end

state_finished(state::EnumerationState) =
    if isa(state.skeleton, Hole)
        false
    else
        isempty(state.path)
    end
