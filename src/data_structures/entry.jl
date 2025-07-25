
abstract type Entry end

struct ValueEntry <: Entry
    type_id::UInt64
    values::Vector
    complexity_summary::Accumulator
    max_summary::Accumulator
    options_count::Int
    complexity::Float64
end

Base.hash(v::ValueEntry, h::UInt64) = hash(v.type_id, hash(v.values, h))
Base.:(==)(v1::ValueEntry, v2::ValueEntry) = v1.type_id == v2.type_id && v1.values == v2.values

match_at_index(entry::ValueEntry, index::Int, value) = entry.values[index] == value

match_with_entry(sc, entry::ValueEntry, other::ValueEntry) = entry == other

function matching_with_unknown_candidates(sc, entry::ValueEntry, branch_id)
    results = []
    unknown_entry_id = sc.branch_entries[branch_id]

    branches = get_connected_to(sc.branch_types, entry.type_id)
    var_id = sc.branch_vars[branch_id]

    for known_branch_id in branches
        if !sc.branch_is_not_copy[known_branch_id]
            continue
        end
        if known_branch_id == sc.target_branch_id
            continue
        end
        known_var_id = sc.branch_vars[known_branch_id]
        if vars_in_loop(sc, known_var_id, var_id)
            # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
            continue
        end
        known_entry_id = sc.branch_entries[known_branch_id]
        if known_entry_id == unknown_entry_id
            known_type = sc.types[sc.branch_types[known_branch_id]]
            prev_matches_count = _get_prev_matches_count(sc, var_id, known_entry_id)
            push!(
                results,
                (
                    FreeVar(known_type, known_type, known_var_id, nothing),
                    known_var_id,
                    known_branch_id,
                    known_type,
                    prev_matches_count,
                ),
            )
        end
    end
    results
end

struct NoDataEntry <: Entry
    type_id::UInt64
end
Base.hash(v::NoDataEntry, h::UInt64) = hash(v.type_id, h)
Base.:(==)(v1::NoDataEntry, v2::NoDataEntry) = v1.type_id == v2.type_id

match_at_index(entry::NoDataEntry, index::Int, value) = true

match_with_entry(sc, entry::NoDataEntry, other::ValueEntry) = in(other.type_id, get_sub_types(sc.types, entry.type_id))

function matching_with_unknown_candidates(sc, entry::NoDataEntry, branch_id)
    results = []
    types = get_sub_types(sc.types, entry.type_id)
    if sc.verbose
        @info "Sub types for $(sc.types[entry.type_id]) are $([sc.types[t] for t in types])"
    end
    var_id = sc.branch_vars[branch_id]
    for tp_id in types
        for known_branch_id in get_connected_to(sc.branch_types, tp_id)
            if !sc.branch_is_not_copy[known_branch_id]
                continue
            end
            if known_branch_id == sc.target_branch_id
                continue
            end
            if sc.complexities[known_branch_id] == 0
                continue
            end
            known_var_id = sc.branch_vars[known_branch_id]
            if vars_in_loop(sc, known_var_id, var_id)
                # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                continue
            end
            tp = sc.types[tp_id]
            prev_matches_count = _get_prev_matches_count(sc, var_id, sc.branch_entries[known_branch_id])

            push!(
                results,
                (FreeVar(tp, tp, known_var_id, nothing), known_var_id, known_branch_id, tp, prev_matches_count),
            )
        end
    end

    results
end

function _get_prev_matches_count(sc, var_id, entry_id)
    old_count = sc.var_incoming_matches_counts[var_id, entry_id]
    if isnothing(old_count)
        old_count = UInt64(0)
    end
    sc.var_incoming_matches_counts[var_id, entry_id] = old_count + 1
    return old_count
end

function matching_with_known_candidates(sc, entry::ValueEntry, known_branch_id)
    results = []
    types = get_super_types(sc.types, entry.type_id)
    if sc.verbose
        @info "Super types for $(sc.types[entry.type_id]) are $([sc.types[t] for t in types])"
    end
    entry_type = sc.types[entry.type_id]

    known_var_id = sc.branch_vars[known_branch_id]
    known_entry_id = sc.branch_entries[known_branch_id]
    for tp_id in types
        for unknown_branch_id in get_connected_to(sc.branch_types, tp_id)
            if !sc.branch_is_unknown[unknown_branch_id]
                continue
            end
            unknown_var_id = sc.branch_vars[unknown_branch_id]
            if vars_in_loop(sc, known_var_id, unknown_var_id)
                # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                continue
            end
            unknown_entry_id = sc.branch_entries[unknown_branch_id]
            unknown_entry = sc.entries[unknown_entry_id]
            if unknown_entry_id == known_entry_id || (
                !isa(unknown_entry, ValueEntry) &&
                (!isa(unknown_entry, PatternEntry) || entry_has_data(unknown_entry)) &&
                match_with_entry(sc, unknown_entry, entry)
            )
                prev_matches_count = _get_prev_matches_count(sc, unknown_var_id, known_entry_id)
                push!(
                    results,
                    (
                        FreeVar(entry_type, entry_type, known_var_id, nothing),
                        unknown_var_id,
                        unknown_branch_id,
                        prev_matches_count,
                    ),
                )
            end
        end
    end

    results
end

struct TooManyOptionsException <: Exception end

struct EitherOptions
    options::Dict{UInt64,Any}
    hash_value::UInt64
    options_count::Int
    function EitherOptions(options)
        if isempty(options)
            error("No options")
        end
        if length(options) > 100
            throw(TooManyOptionsException())
        end
        first_value = first(values(options))
        if all(v -> v == first_value, values(options))
            return first_value
        end
        options_count = sum(get_options_count(v) for v in values(options))
        if options_count > 100
            throw(TooManyOptionsException())
        end
        return new(options, hash(options), options_count)
    end
end

# EitherOptions(options, _, _) = EitherOptions(options)

Base.:(==)(v1::EitherOptions, v2::EitherOptions) = v1.hash_value == v2.hash_value && v1.options == v2.options
Base.hash(v::EitherOptions, h::UInt64) = hash(v.hash_value, h)

get_options_count(value::EitherOptions) = value.options_count
get_options_count(value) = 1

function _get_fixed_hashes(options::EitherOptions, value)
    out_hashes = Set()
    for (h, option) in options.options
        found, hashes = _get_fixed_hashes(option, value)
        if found
            union!(out_hashes, hashes)
            push!(out_hashes, h)
        end
    end
    return !isempty(out_hashes), out_hashes
end

function _get_fixed_hashes(options, value)
    _try_unify_values(options, value, false, rand(UInt64))[1], Set()
end

function get_fixed_hashes(options, value)
    found, hashes = _get_fixed_hashes(options, value)
    if !found
        throw(EnumerationException("Inconsistent match"))
    end
    return hashes
end

function fix_option_hashes(fixed_hashes, value::EitherOptions)
    filter_level = any(haskey(value.options, h) for h in fixed_hashes)
    out_options = Dict()
    for (h, option) in value.options
        if filter_level && !in(h, fixed_hashes)
            continue
        end
        out_options[h] = fix_option_hashes(fixed_hashes, option)
    end
    if isempty(out_options)
        @info value
        @info fixed_hashes
        error("No options left after filtering")
    elseif length(out_options) == 1
        return first(out_options)[2]
    else
        return EitherOptions(out_options)
    end
end

function fix_option_hashes(fixed_hashes, value)
    return value
end

struct AnyObject end
any_object = AnyObject()

Base.show(io::IO, ::AnyObject) = print(io, "any_object")

struct PatternWrapper
    value::Any
end

Base.:(==)(v1::PatternWrapper, v2::PatternWrapper) = v1.value == v2.value
Base.hash(v::PatternWrapper, h::UInt64) = hash(v.value, h)

struct AbductibleValue
    value::Any
end

Base.:(==)(v1::AbductibleValue, v2::AbductibleValue) = v1.value == v2.value
Base.hash(v::AbductibleValue, h::UInt64) = hash(v.value, h)

struct EitherEntry <: Entry
    type_id::UInt64
    values::Vector
    complexity_summary::Accumulator
    max_summary::Accumulator
    options_count::Int
    complexity::Float64
end

Base.hash(v::EitherEntry, h::UInt64) = hash(v.type_id, hash(v.values, h))
Base.:(==)(v1::EitherEntry, v2::EitherEntry) = v1.type_id == v2.type_id && v1.values == v2.values

function matching_with_unknown_candidates(sc, entry::EitherEntry, branch_id)
    results = []
    types = get_sub_types(sc.types, entry.type_id)
    var_id = sc.branch_vars[branch_id]

    for tp_id in types
        for known_branch_id in get_connected_to(sc.branch_types, tp_id)
            if !sc.branch_is_not_copy[known_branch_id]
                continue
            end
            if known_branch_id == sc.target_branch_id
                continue
            end
            if sc.complexities[known_branch_id] == 0
                continue
            end
            known_var_id = sc.branch_vars[known_branch_id]
            known_entry_id = sc.branch_entries[known_branch_id]
            if vars_in_loop(sc, known_var_id, var_id) || !match_with_entry(sc, entry, sc.entries[known_entry_id])
                # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                continue
            end
            tp = sc.types[tp_id]
            prev_matches_count = _get_prev_matches_count(sc, var_id, known_entry_id)
            push!(
                results,
                (FreeVar(tp, tp, known_var_id, nothing), known_var_id, known_branch_id, tp, prev_matches_count),
            )
        end
    end

    results
end

all_options(entry::EitherOptions) = union([all_options(op) for (_, op) in entry.options]...)
all_options(value) = Set([value])

function filter_const_options(current_candidates, value::EitherOptions, next_candidates)
    for (_, option) in value.options
        filter_const_options(current_candidates, option, next_candidates)
    end
end

function filter_const_options(current_candidates, value, next_candidates)
    if in(value, current_candidates)
        push!(next_candidates, value)
    end
end

function filter_const_options(current_candidates, value::Union{PatternWrapper,AbductibleValue}, next_candidates) end

function _const_options(options::EitherOptions)
    return union([_const_options(op) for (_, op) in options.options]...)
end

function _const_options(value)
    return Set([value])
end

function _const_options(value::PatternWrapper)
    return Set()
end

function _const_options(value::AbductibleValue)
    return Set()
end

match_at_index(entry::EitherEntry, index::Int, value) = _match_value(entry.values[index], value)

function match_with_entry(sc, entry::EitherEntry, other::ValueEntry)
    return all(match_at_index(entry, i, other.values[i]) for i in 1:sc.example_count)
end

is_subeither(wide::EitherOptions, narrow) = any(is_subeither(op, narrow) for (h, op) in wide.options)
is_subeither(wide, narrow::EitherOptions) = false
is_subeither(wide, narrow) = _match_value(wide, narrow)
is_subeither(wide::AbductibleValue, narrow::AbductibleValue) = _match_value(wide.value, narrow.value)

function is_subeither(wide::EitherOptions, narrow::EitherOptions)
    check_level = any(haskey(wide.options, k) for k in keys(narrow.options))
    if check_level
        all(haskey(wide.options, k) && is_subeither(wide.options[k], n_op) for (k, n_op) in narrow.options)
    else
        any(is_subeither(op, narrow) for (_, op) in wide.options)
    end
end

struct PatternEntry <: Entry
    type_id::UInt64
    values::Vector
    complexity_summary::Accumulator
    max_summary::Accumulator
    options_count::Int
    complexity::Float64
end

Base.hash(v::PatternEntry, h::UInt64) = hash(v.type_id, hash(v.values, h))
Base.:(==)(v1::PatternEntry, v2::PatternEntry) = v1.type_id == v2.type_id && v1.values == v2.values

@nospecialize
_match_value(unknown_value::AnyObject, known_value) = true
_match_value(unknown_value::AnyObject, known_value::PatternWrapper) = true
_match_value(unknown_value::PatternWrapper, known_value) = _match_value(unknown_value.value, known_value)
_match_value(unknown_value::PatternWrapper, known_value::PatternWrapper) =
    _match_value(unknown_value.value, known_value.value)
_match_value(unknown_value, known_value::PatternWrapper) = unknown_value == known_value.value
_match_value(unknown_value::Array, known_value::PatternWrapper) = unknown_value == known_value.value
_match_value(unknown_value::Tuple, known_value::PatternWrapper) = unknown_value == known_value.value
_match_value(unknown_value::Set, known_value::PatternWrapper) = unknown_value == known_value.value
_match_value(unknown_value::AbductibleValue, known_value::PatternWrapper) =
    _match_value(unknown_value.value, known_value.value)
_match_value(unknown_value::EitherOptions, known_value::PatternWrapper) =
    @invoke(_match_value(unknown_value::EitherOptions, known_value.value::Any))
_match_value(unknown_value, known_value) = unknown_value == known_value

_match_value(unknown_value::Array, known_value::Array) =
    size(unknown_value) == size(known_value) && all(_match_value(v, ov) for (v, ov) in zip(unknown_value, known_value))

_match_value(unknown_value::Array, known_value) = false

_match_value(unknown_value::Tuple, known_value::Tuple) =
    length(unknown_value) == length(known_value) &&
    all(_match_value(v, ov) for (v, ov) in zip(unknown_value, known_value))

_match_value(unknown_value::Tuple, known_value) = false

_match_value(unknown_value::AbductibleValue, known_value) = _match_value(unknown_value.value, known_value)

_match_value(unknown_value::EitherOptions, known_value) =
    any(_match_value(op, known_value) for (_, op) in unknown_value.options)

function _match_value(unknown_value::Set, known_value::Set)
    if length(unknown_value) != length(known_value)
        return false
    end
    if unknown_value == known_value
        return true
    end
    matched_indices = Set{Int}()
    for uv in unknown_value
        found = false
        for (i, kv) in enumerate(known_value)
            if in(i, matched_indices)
                continue
            end
            if _match_value(uv, kv)
                push!(matched_indices, i)
                found = true
                break
            end
        end
        if !found
            return false
        end
    end
    return true
end

_match_value(unknown_value::Set, known_value) = false
@specialize

match_at_index(entry::PatternEntry, index::Int, value) = _match_value(entry.values[index], value)

function match_with_entry(sc, entry::PatternEntry, other::ValueEntry)
    return all(match_at_index(entry, i, other.values[i]) for i in 1:sc.example_count)
end

function match_with_entry(sc, entry::ValueEntry, other::PatternEntry)
    return false
end

function match_with_entry(sc, entry::PatternEntry, other::PatternEntry)
    return all(match_at_index(entry, i, other.values[i]) for i in 1:sc.example_count)
end

function match_with_entry(sc, entry::EitherEntry, other::PatternEntry)
    return all(match_at_index(entry, i, other.values[i]) for i in 1:sc.example_count)
end

match_with_entry(sc, entry::NoDataEntry, other::PatternEntry) =
    in(other.type_id, get_sub_types(sc.types, entry.type_id))

function matching_with_unknown_candidates(sc, entry::PatternEntry, branch_id)
    results = []
    if !entry_has_data(entry)
        return results
    end
    var_id = sc.branch_vars[branch_id]

    types = get_sub_types(sc.types, entry.type_id)
    # @info "Sub types for $(sc.types[entry.type_id]) are $([sc.types[t] for t in types])"

    for tp_id in types
        for known_branch_id in get_connected_to(sc.branch_types, tp_id)
            if !sc.branch_is_not_copy[known_branch_id]
                continue
            end
            if known_branch_id == sc.target_branch_id
                continue
            end
            if sc.complexities[known_branch_id] == 0
                continue
            end
            known_var_id = sc.branch_vars[known_branch_id]
            known_entry_id = sc.branch_entries[known_branch_id]
            if vars_in_loop(sc, known_var_id, var_id) || !match_with_entry(sc, entry, sc.entries[known_entry_id])
                # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                continue
            end
            tp = sc.types[tp_id]
            prev_matches_count = _get_prev_matches_count(sc, var_id, known_entry_id)
            push!(
                results,
                (FreeVar(tp, tp, known_var_id, nothing), known_var_id, known_branch_id, tp, prev_matches_count),
            )
        end
    end
    results
end

function matching_with_known_candidates(sc, entry::PatternEntry, known_branch_id)
    results = []
    if entry.complexity == 0 || !entry_has_data(entry)
        return results
    end
    types = get_super_types(sc.types, entry.type_id)
    entry_type = sc.types[entry.type_id]
    known_entry_id = sc.branch_entries[known_branch_id]

    known_var_id = sc.branch_vars[known_branch_id]
    for tp_id in types
        for unknown_branch_id in get_connected_to(sc.branch_types, tp_id)
            if !sc.branch_is_unknown[unknown_branch_id]
                continue
            end
            unknown_var_id = sc.branch_vars[unknown_branch_id]
            if vars_in_loop(sc, known_var_id, unknown_var_id)
                # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                continue
            end
            unknown_entry_id = sc.branch_entries[unknown_branch_id]
            unknown_entry = sc.entries[unknown_entry_id]
            if unknown_entry_id == known_entry_id || (
                !isa(unknown_entry, ValueEntry) &&
                (!isa(unknown_entry, PatternEntry) || entry_has_data(unknown_entry)) &&
                match_with_entry(sc, unknown_entry, entry)
            )
                prev_matches_count = _get_prev_matches_count(sc, unknown_var_id, known_entry_id)
                push!(
                    results,
                    (
                        FreeVar(entry_type, entry_type, known_var_id, nothing),
                        unknown_var_id,
                        unknown_branch_id,
                        prev_matches_count,
                    ),
                )
            end
        end
    end

    results
end

struct AbductibleEntry <: Entry
    type_id::UInt64
    values::Vector
    complexity_summary::Accumulator
    max_summary::Accumulator
    options_count::Int
    complexity::Float64
end

Base.hash(v::AbductibleEntry, h::UInt64) = hash(v.type_id, hash(v.values, h))
Base.:(==)(v1::AbductibleEntry, v2::AbductibleEntry) = v1.type_id == v2.type_id && v1.values == v2.values

match_at_index(entry::AbductibleEntry, index::Int, value) = _match_value(entry.values[index], value)

function match_with_entry(sc, entry::AbductibleEntry, other::ValueEntry)
    return all(match_at_index(entry, i, other.values[i]) for i in 1:sc.example_count)
end

function match_with_entry(sc, entry::AbductibleEntry, other::PatternEntry)
    return false
end

function matching_with_unknown_candidates(sc, entry::AbductibleEntry, branch_id)
    results = []
    var_id = sc.branch_vars[branch_id]

    types = get_sub_types(sc.types, entry.type_id)
    for tp_id in types
        for known_branch_id in get_connected_to(sc.branch_types, tp_id)
            if !sc.branch_is_not_copy[known_branch_id]
                continue
            end
            if known_branch_id == sc.target_branch_id
                continue
            end
            if sc.complexities[known_branch_id] == 0
                continue
            end
            known_var_id = sc.branch_vars[known_branch_id]
            known_entry_id = sc.branch_entries[known_branch_id]
            if vars_in_loop(sc, known_var_id, var_id) || !match_with_entry(sc, entry, sc.entries[known_entry_id])
                # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                continue
            end
            tp = sc.types[tp_id]
            prev_matches_count = _get_prev_matches_count(sc, var_id, known_entry_id)
            push!(
                results,
                (FreeVar(tp, tp, known_var_id, nothing), known_var_id, known_branch_id, tp, prev_matches_count),
            )
        end
    end
    results
end

_try_unify_values(v1, v2::AnyObject, check_pattern, block_id) = true, v1
_try_unify_values(v1::AnyObject, v2, check_pattern, block_id) = true, v2
_try_unify_values(v1::AnyObject, v2::AnyObject, check_pattern, block_id) = true, v2

function _try_unify_values(v1::PatternWrapper, v2, check_pattern, block_id)
    found, res = _try_unify_values(v1.value, v2, true, block_id)
    if !found
        return found, res
    end
    return found, _wrap_wildcard(res)
end

function _try_unify_values(v1, v2::PatternWrapper, check_pattern, block_id)
    found, res = _try_unify_values(v1, v2.value, true, block_id)
    if !found
        return found, res
    end
    return found, _wrap_wildcard(res)
end

function _try_unify_values(v1::PatternWrapper, v2::PatternWrapper, check_pattern, block_id)
    found, res = _try_unify_values(v1.value, v2.value, true, block_id)
    if !found
        return found, res
    end
    return found, _wrap_wildcard(res)
end

_try_unify_values(v1::PatternWrapper, v2::AnyObject, check_pattern, block_id) = true, v1
_try_unify_values(v1::AnyObject, v2::PatternWrapper, check_pattern, block_id) = true, v2

function _try_unify_values(v1::AbductibleValue, v2, check_pattern, block_id)
    found, res = _try_unify_values(v1.value, v2, true, block_id)
    if !found
        return found, res
    end
    found, _wrap_abductible(res)
end

function _try_unify_values(v1, v2::AbductibleValue, check_pattern, block_id)
    found, res = _try_unify_values(v1, v2.value, true, block_id)
    if !found
        return found, res
    end
    found, _wrap_abductible(res)
end

function _try_unify_values(v1::AbductibleValue, v2::AbductibleValue, check_pattern, block_id)
    found, res = _try_unify_values(v1.value, v2.value, true, block_id)
    if !found
        return found, res
    end
    found, _wrap_abductible(res)
end

_try_unify_values(v1::AbductibleValue, v2::AnyObject, check_pattern, block_id) = true, v1
_try_unify_values(v1::AnyObject, v2::AbductibleValue, check_pattern, block_id) = true, v2

function _try_unify_values(v1::AbductibleValue, v2::PatternWrapper, check_pattern, block_id)
    found, res = _try_unify_values(v1.value, v2.value, true, block_id)
    if !found
        return found, res
    end
    found, _wrap_abductible(res)
end

function _try_unify_values(v1::PatternWrapper, v2::AbductibleValue, check_pattern, block_id)
    found, res = _try_unify_values(v1.value, v2.value, true, block_id)
    if !found
        return found, res
    end
    found, _wrap_abductible(res)
end

function _try_unify_values(v1::EitherOptions, v2::PatternWrapper, check_pattern, block_id)
    @invoke _try_unify_values(v1::EitherOptions, v2::Any, check_pattern, block_id)
end

function _try_unify_values(v1::EitherOptions, v2::AbductibleValue, check_pattern, block_id)
    @invoke _try_unify_values(v1::EitherOptions, v2::Any, check_pattern, block_id)
end

function _try_unify_values(v1::EitherOptions, v2, check_pattern, block_id)
    options = Dict()
    for (h, v) in v1.options
        found, unified_v = _try_unify_values(v, v2, check_pattern, block_id)
        if found
            options[h] = unified_v
        end
    end
    if isempty(options)
        return false, nothing
    end
    return true, EitherOptions(options)
end

function _try_unify_values(v1::PatternWrapper, v2::EitherOptions, check_pattern, block_id)
    @invoke _try_unify_values(v1::Any, v2::EitherOptions, check_pattern, block_id)
end

function _try_unify_values(v1::AbductibleValue, v2::EitherOptions, check_pattern, block_id)
    @invoke _try_unify_values(v1::Any, v2::EitherOptions, check_pattern, block_id)
end

function _try_unify_values(v1, v2::EitherOptions, check_pattern, block_id)
    options = Dict()
    for (h, v) in v2.options
        found, unified_v = _try_unify_values(v1, v, check_pattern, block_id)
        if found
            options[h] = unified_v
        end
    end
    if isempty(options)
        return false, nothing
    end
    return true, EitherOptions(options)
end

function _try_unify_values(v1::EitherOptions, v2::EitherOptions, check_pattern, block_id)
    options = Dict()
    for (h, v) in v1.options
        if haskey(v2.options, h)
            found, unified_v = _try_unify_values(v, v2.options[h], check_pattern, block_id)
            if found
                options[h] = unified_v
            else
                return false, nothing
            end
        end
    end
    if isempty(options)
        return false, nothing
    end
    return true, EitherOptions(options)
end

_try_unify_values(v1::EitherOptions, v2::AnyObject, check_pattern, block_id) = true, v1
_try_unify_values(v1::AnyObject, v2::EitherOptions, check_pattern, block_id) = true, v2

function _try_unify_values(v1, v2, check_pattern, block_id)
    if v1 == v2
        return true, v1
    end
    return false, nothing
end

function _try_unify_values(v1::Array, v2::Array, check_pattern, block_id)
    if length(v1) != length(v2)
        return false, nothing
    end
    if v1 == v2
        return true, v1
    end
    if !check_pattern
        return false, nothing
    end
    res = []
    for i in 1:length(v1)
        found, unified_v = _try_unify_values(v1[i], v2[i], check_pattern, block_id)
        if !found
            return false, nothing
        end
        push!(res, unified_v)
    end
    res = reshape(res, size(v1))
    return true, res
end

function _try_unify_values(v1::Tuple, v2::Tuple, check_pattern, block_id)
    if length(v1) != length(v2)
        return false, nothing
    end
    if v1 == v2
        return true, v1
    end
    if !check_pattern
        return false, nothing
    end
    res = []
    for i in 1:length(v1)
        found, unified_v = _try_unify_values(v1[i], v2[i], check_pattern, block_id)
        if !found
            return false, nothing
        end
        push!(res, unified_v)
    end
    return true, Tuple(res)
end

function _try_unify_values(v1::Set, v2::Set, check_pattern, block_id)
    if length(v1) != length(v2)
        return false, nothing
    end
    if v1 == v2
        return true, v1
    end
    if !check_pattern
        return false, nothing
    end
    options = []
    f_v = first(v1)
    if in(f_v, v2)
        found, rest = _try_unify_values(setdiff(v1, Set([f_v])), setdiff(v2, Set([f_v])), check_pattern, block_id)
        if !found
            return false, nothing
        end
        if isa(rest, EitherOptions)
            for (h, v) in rest.options
                push!(options, union(Set([f_v]), v))
            end
        else
            push!(rest, f_v)
            return true, rest
        end
    else
        for v in v2
            found, unified_v = _try_unify_values(f_v, v, check_pattern, block_id)
            if !found
                continue
            end
            found, rest = _try_unify_values(setdiff(v1, Set([f_v])), setdiff(v2, Set([v])), check_pattern, block_id)
            if !found
                continue
            end
            if isa(rest, EitherOptions)
                for (h, val) in rest.options
                    push!(options, union(Set([unified_v]), val))
                end
            else
                push!(options, union(Set([unified_v]), rest))
            end
        end
    end
    if isempty(options)
        return false, nothing
    elseif length(options) == 1
        return true, options[1]
    else
        return true, EitherOptions(Dict(hash(option, block_id) => option for option in options))
    end
end

function make_entry(sc, type_id, values)
    complexity_summary, max_summary, options_count = get_complexity_summary(values, sc.types[type_id])
    if any(isa(v, EitherOptions) for v in values)
        new_entry = EitherEntry(
            type_id,
            values,
            complexity_summary,
            max_summary,
            options_count,
            get_complexity(sc, complexity_summary),
        )
    elseif any(isa(v, AbductibleValue) for v in values)
        new_entry = AbductibleEntry(
            type_id,
            values,
            complexity_summary,
            max_summary,
            options_count,
            get_complexity(sc, complexity_summary),
        )
    elseif any(isa(v, PatternWrapper) for v in values)
        new_entry = PatternEntry(
            type_id,
            values,
            complexity_summary,
            max_summary,
            options_count,
            get_complexity(sc, complexity_summary),
        )
    else
        new_entry = ValueEntry(
            type_id,
            values,
            complexity_summary,
            max_summary,
            options_count,
            get_complexity(sc, complexity_summary),
        )
    end
    new_entry_index = push!(sc.entries, new_entry)
    return new_entry, new_entry_index
end
