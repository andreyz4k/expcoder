
abstract type Entry end

using DataStructures: Accumulator
struct ValueEntry <: Entry
    type_id::Int
    values::Vector
    complexity_summary::Accumulator
    complexity::Float64
end

Base.hash(v::ValueEntry, h::UInt64) = hash(v.type_id, hash(v.values, h))
Base.:(==)(v1::ValueEntry, v2::ValueEntry) = v1.type_id == v2.type_id && v1.values == v2.values

get_matching_seq(entry::ValueEntry) = [(rv -> rv == v ? Strict : NoMatch) for v in entry.values]

match_with_entry(sc, entry::ValueEntry, other::ValueEntry) = entry == other

function matching_with_unknown_candidates(sc, entry::ValueEntry, var_id)
    results = []
    index = get_index(sc.entries, entry)

    branches = sc.branch_types[:, entry.type_id]

    known_branches = emul(branches, sc.branches_is_known[:])

    for known_branch_id in nonzeroinds(known_branches)
        known_var_id = sc.branch_vars[known_branch_id]
        if vars_in_loop(sc, known_var_id, var_id)
            # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
            continue
        end
        if sc.branch_entries[known_branch_id] == index
            known_type = sc.types[reduce(any, sc.branch_types[known_branch_id, :])]
            push!(results, (FreeVar(known_type, known_var_id), Dict(known_var_id => known_branch_id), known_type))
        end
    end
    results
end


const_options(entry::ValueEntry) = [entry.values[1]]

struct NoDataEntry <: Entry
    type_id::Int
end
Base.hash(v::NoDataEntry, h::UInt64) = hash(v.type_id, h)
Base.:(==)(v1::NoDataEntry, v2::NoDataEntry) = v1.type_id == v2.type_id

get_matching_seq(entry::NoDataEntry) = Iterators.repeated(_ -> TypeOnly)

match_with_entry(sc, entry::NoDataEntry, other::ValueEntry) =
    might_unify(sc.types[entry.type_id], sc.types[other.type_id])

function matching_with_unknown_candidates(sc, entry::NoDataEntry, var_id)
    results = []
    types = get_super_types(sc.types, entry.type_id)

    branches = reduce(any, sc.branch_types[:, types], dims = 2)

    known_branches = emul(branches, sc.branches_is_known[:])

    for (known_branch_id, tp_id) in zip(findnz(known_branches)...)
        known_var_id = sc.branch_vars[known_branch_id]
        if vars_in_loop(sc, known_var_id, var_id)
            # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
            continue
        end
        tp = sc.types[tp_id]
        push!(results, (FreeVar(tp, known_var_id), Dict(known_var_id => known_branch_id), tp))
    end

    results
end

const_options(entry::NoDataEntry) = []


function matching_with_known_candidates(sc, entry::ValueEntry, known_branch_id)
    results = []
    types = get_super_types(sc.types, entry.type_id)
    entry_type = sc.types[entry.type_id]
    branches = reduce(any, sc.branch_types[:, types], dims = 2)

    unknown_branches = emul(branches, sc.branches_is_unknown[:])

    known_var_id = sc.branch_vars[known_branch_id]
    for unknown_branch_id in nonzeroinds(unknown_branches)
        unknown_var_id = sc.branch_vars[unknown_branch_id]
        if vars_in_loop(sc, known_var_id, unknown_var_id)
            # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
            continue
        end
        unknown_entry_id = sc.branch_entries[unknown_branch_id]
        unknown_entry = sc.entries[unknown_entry_id]
        if unknown_entry_id == sc.branch_entries[known_branch_id] ||
           (!isa(unknown_entry, ValueEntry) && match_with_entry(sc, unknown_entry, entry))
            push!(results, (FreeVar(entry_type, known_var_id), unknown_var_id, unknown_branch_id, entry_type))
        end
    end

    results
end

struct EitherOptions
    options::Dict{UInt64,Any}
end

struct EitherEntry <: Entry
    type_id::Int
    values::Vector
    complexity_summary::Accumulator
    complexity::Float64
end

Base.hash(v::EitherEntry, h::UInt64) = hash(v.type_id, hash(v.values, h))
Base.:(==)(v1::EitherEntry, v2::EitherEntry) = v1.type_id == v2.type_id && v1.values == v2.values

function matching_with_unknown_candidates(sc, entry::EitherEntry, var_id)
    results = []
    types = get_super_types(sc.types, entry.type_id)

    branches = reduce(any, sc.branch_types[:, types], dims = 2)

    known_branches = emul(branches, sc.branches_is_known[:])

    for (known_branch_id, tp_id) in zip(findnz(known_branches)...)
        known_var_id = sc.branch_vars[known_branch_id]
        if vars_in_loop(sc, known_var_id, var_id) ||
           !match_with_entry(sc, entry, sc.entries[sc.branch_entries[known_branch_id]])
            # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
            continue
        end
        tp = sc.types[tp_id]
        push!(results, (FreeVar(tp, known_var_id), Dict(known_var_id => known_branch_id), tp))
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

function match_with_entry(sc, entry::EitherEntry, other::ValueEntry)
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
