
abstract type Turn end

struct LeftTurn <: Turn end
struct RightTurn <: Turn end
struct ArgTurn <: Turn
    type::Tp
    root_type::Tp
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
    root_request::Tp
    root_entry::UInt64
    reverse::Bool
end

Base.:(==)(a::BlockPrototype, b::BlockPrototype) =
    a.skeleton == b.skeleton &&
    a.context == b.context &&
    a.path == b.path &&
    a.cost == b.cost &&
    a.free_parameters == b.free_parameters &&
    a.request == b.request &&
    a.root_request == b.root_request &&
    a.root_entry == b.root_entry &&
    a.reverse == b.reverse

Base.hash(a::BlockPrototype, h::UInt) = hash(
    a.skeleton,
    hash(
        a.context,
        hash(
            a.path,
            hash(
                a.cost,
                hash(a.free_parameters, hash(a.request, hash(a.root_request, hash(a.root_entry, hash(a.reverse, h))))),
            ),
        ),
    ),
)

EPSILON = 1e-3

function enqueue_matches_with_known_var(sc, branch_id)
    var_id = sc.branch_vars[branch_id]
    entry_id = sc.branch_entries[branch_id]
    entry = sc.entries[entry_id]
    tp = sc.types[sc.branch_types[branch_id]]
    for (pr, output_var_id, output_br_id, prev_matches_count) in matching_with_known_candidates(sc, entry, branch_id)
        type_id =
            push!(sc.types, TypeNamedArgsConstructor(ARROW, OrderedDict{Union{String,UInt64},Tp}(var_id => tp), tp))
        bl = ProgramBlock(pr, type_id, EPSILON, [var_id], output_var_id, false)
        if isnothing(sc.explained_min_path_costs[branch_id])
            if isnothing(sc.unknown_min_path_costs[branch_id])
                cost = sc.unknown_min_path_costs[output_br_id]
            else
                cost = sc.unknown_min_path_costs[branch_id] + sc.unknown_min_path_costs[output_br_id]
            end
        else
            cost = sc.explained_min_path_costs[branch_id] + sc.unknown_min_path_costs[output_br_id]
        end

        if prev_matches_count > 0 && !sc.branch_is_explained[sc.target_branch_id]
            if sc.verbose
                @info "Adding $((bl, Dict(var_id => branch_id), Dict(output_var_id => output_br_id))) to duplicate copies queue"
            end
            sc.duplicate_copies_queue[(bl, Dict(var_id => branch_id), Dict(output_var_id => output_br_id))] =
                cost + bl.cost + sc.hyperparameters["match_duplicates_penalty"] * prev_matches_count
        else
            if sc.verbose
                @info "Adding $((bl, Dict(var_id => branch_id), Dict(output_var_id => output_br_id))) to copies queue"
            end
            sc.copies_queue[(bl, Dict(var_id => branch_id), Dict(output_var_id => output_br_id))] = cost + bl.cost
        end
    end
end

function enqueue_known_bp(sc, bp, q, branch_id)
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

entry_has_data(entry::NoDataEntry) = false
entry_has_data(entry::PatternEntry) = any(_value_has_data, entry.values)
entry_has_data(entry::AbductibleEntry) = any(_value_has_data, entry.values)
entry_has_data(entry::ValueEntry) = true
entry_has_data(entry::EitherEntry) = true

_value_has_data(v::AbductibleValue) = _value_has_data(v.value)
_value_has_data(v::PatternWrapper) = _value_has_data(v.value)
_value_has_data(v::Array) = isempty(v) || any(_value_has_data, v)
_value_has_data(v::Set) = isempty(v) || any(_value_has_data, v)
_value_has_data(v::Tuple) = isempty(v) || any(_value_has_data, v)
_value_has_data(v::Nothing) = false
_value_has_data(v::AnyObject) = false
_value_has_data(v) = true

function enqueue_known_var(sc, branch_id, guiding_model_channels, grammar)
    if branch_id == sc.target_branch_id
        return
    end
    enqueue_matches_with_known_var(sc, branch_id)
    entry_id = sc.branch_entries[branch_id]
    entry = sc.entries[entry_id]
    if !isnothing(sc.explained_min_path_costs[branch_id]) && entry_has_data(entry) && sc.branch_is_not_const[branch_id]
        if !haskey(sc.entry_grammars, (entry_id, true))
            generate_grammar(sc, guiding_model_channels, entry_id, true, branch_id)
        else
            if haskey(sc.found_blocks_reverse, entry_id)
                for block_info in sc.found_blocks_reverse[entry_id]
                    prev_entries = get_connected_from(sc.branch_prev_entries, branch_id)
                    if sc.traced || all(!in(entry_id, prev_entries) for (_, entry_id, _) in block_info[4])
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
        end
    end
end

function enqueue_unknown_bp(sc, bp, q)
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

function enqueue_matches_with_unknown_var(sc, branch_id)
    var_id = sc.branch_vars[branch_id]
    entry_id = sc.branch_entries[branch_id]
    entry = sc.entries[entry_id]
    for (pr, in_var_id, in_branch_id, in_type, prev_matches_count) in
        matching_with_unknown_candidates(sc, entry, branch_id)
        type_id = push!(
            sc.types,
            TypeNamedArgsConstructor(ARROW, OrderedDict{Union{String,UInt64},Tp}(in_var_id => in_type), in_type),
        )
        bl = ProgramBlock(pr, type_id, EPSILON, [in_var_id], var_id, false)
        if isnothing(sc.explained_min_path_costs[in_branch_id])
            if isnothing(sc.unknown_min_path_costs[in_branch_id])
                cost = sc.unknown_min_path_costs[branch_id]
            else
                cost = sc.unknown_min_path_costs[branch_id] + sc.unknown_min_path_costs[in_branch_id]
            end
        else
            cost = sc.unknown_min_path_costs[branch_id] + sc.explained_min_path_costs[in_branch_id]
        end

        if prev_matches_count > 0 && !sc.branch_is_explained[sc.target_branch_id]
            if sc.verbose
                @info "Adding $((bl, Dict(in_var_id => in_branch_id), Dict(var_id => branch_id))) to duplicate copies queue"
            end
            sc.duplicate_copies_queue[(bl, Dict(in_var_id => in_branch_id), Dict(var_id => branch_id))] =
                cost + bl.cost + sc.hyperparameters["match_duplicates_penalty"] * prev_matches_count
        else
            if sc.verbose
                @info "Adding $((bl, Dict(in_var_id => in_branch_id), Dict(var_id => branch_id))) to copies queue"
            end
            sc.copies_queue[(bl, Dict(in_var_id => in_branch_id), Dict(var_id => branch_id))] = cost + bl.cost
        end
    end
end

function enqueue_unknown_var(sc, branch_id, guiding_model_channels, grammar)
    enqueue_matches_with_unknown_var(sc, branch_id)

    entry_id = sc.branch_entries[branch_id]
    entry = sc.entries[entry_id]
    if entry_has_data(entry)
        if !haskey(sc.entry_grammars, (entry_id, false))
            generate_grammar(sc, guiding_model_channels, entry_id, false, branch_id)
        else
            if haskey(sc.found_blocks_forward, entry_id)
                for block_info in sc.found_blocks_forward[entry_id]
                    foll_entries = get_connected_from(sc.branch_foll_entries, branch_id)
                    if sc.traced || all(!in(entry_id, foll_entries) for (_, entry_id, _) in block_info[5])
                        if sc.verbose
                            @info "Adding $((false, branch_id, block_info)) to insert queue"
                        end
                        sc.blocks_to_insert[(branch_id, block_info)] =
                            sc.unknown_min_path_costs[branch_id] + block_info[4]
                    else
                        if sc.verbose
                            @info "Skipping $((false, branch_id, block_info)) because of following entries $foll_entries"
                        end
                    end
                end
            end
        end
    elseif isa(entry, PatternEntry)
        if !haskey(sc.found_blocks_forward, entry_id)
            sc.found_blocks_forward[entry_id] = []
            block_info = (
                SetConst(sc.types[entry.type_id], entry.values[1]),
                sc.types[entry.type_id],
                sc.types[entry.type_id],
                0.001,
                [],
                false,
                false,
                true,
            )
            push!(sc.found_blocks_forward[entry_id], block_info)
        end
        for block_info in sc.found_blocks_forward[entry_id]
            foll_entries = get_connected_from(sc.branch_foll_entries, branch_id)
            if sc.traced || all(!in(entry_id, foll_entries) for (_, entry_id, _) in block_info[5])
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

state_finished(bp::BlockPrototype) =
    if isa(bp.skeleton, Hole)
        false
    else
        isempty(bp.path)
    end
