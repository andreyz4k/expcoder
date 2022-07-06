
abstract type Entry end

using DataStructures: Accumulator
struct ValueEntry <: Entry
    type::Tp
    values::Vector
    complexity_summary::Accumulator
    complexity::Float64
end

Base.hash(v::ValueEntry, h::UInt64) = hash(v.type, h) + hash(v.values, h)
Base.:(==)(v1::ValueEntry, v2::ValueEntry) = v1.type == v2.type && v1.values == v2.values

get_matching_seq(entry::ValueEntry) = [(rv -> rv == v ? Strict : NoMatch) for v in entry.values]

match_with_entry(entry::ValueEntry, other::ValueEntry) = entry == other

function matching_with_unknown_candidates(sc, entry::ValueEntry, key)
    results = []
    index = sc.entries_storage.val_to_ind[entry]
    for known_branch in sc.known_branches[entry.type]
        if !known_branch.is_meaningful || keys_in_loop(sc, known_branch.key, key)
            # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
            continue
        end
        if known_branch.value_index == index
            push!(
                results,
                (FreeVar(known_branch.type, known_branch.key), [(known_branch.key, known_branch)], known_branch.type),
            )
        end
    end
    results
end


const_options(entry::ValueEntry) = [entry.values[1]]

struct NoDataEntry <: Entry
    type::Tp
end
Base.hash(v::NoDataEntry, h::UInt64) = hash(v.type, h)
Base.:(==)(v1::NoDataEntry, v2::NoDataEntry) = v1.type == v2.type

get_matching_seq(entry::NoDataEntry) = Iterators.repeated(_ -> TypeOnly)

match_with_entry(entry::NoDataEntry, other::ValueEntry) = might_unify(entry.type, other.type)

function matching_with_unknown_candidates(sc, entry::NoDataEntry, key)
    results = []
    for (tp, known_branches) in sc.known_branches
        if might_unify(entry.type, tp)
            for known_branch in known_branches
                if !known_branch.is_meaningful || keys_in_loop(sc, known_branch.key, key)
                    # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                    continue
                end
                push!(results, (FreeVar(tp, known_branch.key), [(known_branch.key, known_branch)], tp))
            end
        end
    end
    results
end

const_options(entry::NoDataEntry) = []


function matching_with_known_candidates(sc, entry::ValueEntry, known_branch)
    results = []
    for (tp, unknown_branches) in sc.unknown_branches
        if might_unify(entry.type, tp)
            for unknown_branch in unknown_branches
                if keys_in_loop(sc, known_branch.key, unknown_branch.key)
                    # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                    continue
                end
                unknown_entry = get_entry(sc.entries_storage, unknown_branch.value_index)
                if unknown_branch.value_index == known_branch.value_index ||
                   (!isa(unknown_entry, ValueEntry) && match_with_entry(unknown_entry, entry))
                    push!(results, (FreeVar(entry.type, known_branch.key), unknown_branch, entry.type))
                end
            end
        end
    end
    results
end

struct EitherOptions
    options::Dict{UInt64,Any}
end

struct EitherEntry <: Entry
    type::Tp
    values::Vector
    complexity_summary::Accumulator
    complexity::Float64
end

Base.hash(v::EitherEntry, h::UInt64) = hash(v.type, h) + hash(v.values, h)
Base.:(==)(v1::EitherEntry, v2::EitherEntry) = v1.type == v2.type && v1.values == v2.values

function matching_with_unknown_candidates(sc, entry::EitherEntry, key)
    results = []
    for (tp, known_branches) in sc.known_branches
        if might_unify(entry.type, tp)
            for known_branch in known_branches
                if !known_branch.is_meaningful ||
                   keys_in_loop(sc, known_branch.key, key) ||
                   !match_with_entry(entry, get_entry(sc.entries_storage, known_branch.value_index))
                    # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                    continue
                end
                push!(results, (FreeVar(tp, known_branch.key), [(known_branch.key, known_branch)], tp))
            end
        end
    end
    results
end

function _const_options(options::EitherOptions)
    return vcat([_const_options(op) for (_, op) in options.options]...)
end

function _const_options(value)
    return [value]
end

function const_options(entry::EitherEntry)
    return _const_options(entry.values[1])
end

function _match_options(value::EitherOptions)
    matchers = [_match_options(op) for (_, op) in value.options]
    return rv -> (any(matcher(rv) != NoMatch for matcher in matchers)) ? Pattern : NoMatch
end

_match_options(value) = (rv -> rv == value ? Strict : NoMatch)

get_matching_seq(entry::EitherEntry) = [_match_options(value) for value in entry.values]

function match_with_entry(entry::EitherEntry, other::ValueEntry)
    matchers = get_matching_seq(entry)
    return all(matcher(v) != NoMatch for (matcher, v) in zip(matchers, other.values))
end

is_subeither(wide::EitherOptions, narrow) = any(is_subeither(op, narrow) for op in wide.options)
is_subeither(wide, narrow::EitherOptions) = false
is_subeither(wide, narrow) = wide == narrow

function is_subeither(wide::EitherOptions, narrow::EitherOptions)
    check_level = any(haskey(wide.options, k) for k in keys(narrow.options))
    if check_level
        all(haskey(wide.options, k) && is_subeither(wide.options[k], n_op) for (k, n_op) in narrow.options)
    else
        any(is_subeither(op, narrow) for op in wide.options)
    end
end
