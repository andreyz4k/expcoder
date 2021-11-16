
abstract type Entry end

struct ValueEntry <: Entry
    type::Tp
    values::Vector
end

Base.hash(v::ValueEntry, h::UInt64) = hash(v.type, h) + hash(v.values, h)

get_matching_seq(entry::ValueEntry) = [(rv -> rv == v ? Strict : NoMatch) for v in entry.values]

match_with_task_val(entry::ValueEntry, other::ValueEntry, key) =
    if entry.type == other.type && entry.values == other.values
        (Strict, FreeVar(other.type, key))
    else
        missing
    end

const_options(entry::ValueEntry) =
    [entry.values[1]]

struct NoDataEntry <: Entry
    type::Tp
end
Base.hash(v::NoDataEntry, h::UInt64) = hash(v.type, h)

get_matching_seq(entry::NoDataEntry) = Iterators.repeated(_ -> TypeOnly)
match_with_task_val(entry::NoDataEntry, other::ValueEntry, key) =
    might_unify(entry.type, other.type) ? (TypeOnly, FreeVar(other.type, key)) : missing

const_options(entry::NoDataEntry) = []
