
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

match_with_task_val(entry::ValueEntry, other::ValueEntry, key) =
    if entry.type == other.type && entry.values == other.values
        (Strict, FreeVar(other.type, key))
    else
        missing
    end

function matching_with_unknown_candidates(sc, entry::ValueEntry, key)
    results = []
    index = sc.entries_storage.val_to_ind[entry]
    for known_branch in sc.known_branches[entry.type]
        if !known_branch.is_meaningful || keys_in_loop(sc, known_branch.key, key)
            # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
            continue
        end
        if known_branch.value_index == index
            push!(results, (FreeVar(known_branch.type, known_branch.key), [(known_branch.key, known_branch)], known_branch.type))
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
match_with_task_val(entry::NoDataEntry, other::ValueEntry, key) =
    might_unify(entry.type, other.type) ? (TypeOnly, FreeVar(other.type, key)) : missing

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

struct EitherEntry <: Entry
    type::Tp
    values::Vector
    complexity_summary::Accumulator
    complexity::Float64
end

Base.hash(v::EitherEntry, h::UInt64) = hash(v.type, h) + hash(v.values, h)
Base.:(==)(v1::EitherEntry, v2::EitherEntry) = v1.type == v2.type && v1.values == v2.values


function matching_with_known_candidates(sc, entry::ValueEntry, known_branch)
    results = []
    for (tp, unknown_branches) in sc.unknown_branches
        if might_unify(entry.type, tp)
            for unknown_branch in unknown_branches
                if keys_in_loop(sc, known_branch.key, unknown_branch.key)
                    # || !is_branch_compatible(unknown_branch.key, unknown_branch, [input_branch])
                    continue
                end
                unknown_entry = sc.entries_storage.values[unknown_branch.value_index]
                if isa(unknown_entry, EitherEntry)
                    error("Not implemented")
                end
                if (isa(unknown_entry, ValueEntry) && unknown_branch.value_index == known_branch.value_index) ||
                   isa(unknown_entry, NoDataEntry)
                    push!(results, (FreeVar(entry.type, known_branch.key), unknown_branch, entry.type))
                end
            end
        end
    end
    results
end
