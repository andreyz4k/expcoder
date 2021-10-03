
abstract type Entry end

struct ValueEntry <: Entry
    type::Tp
    values::Vector
end

get_matching_seq(entry::ValueEntry) = [(rv -> rv == v ? Strict : NoMatch) for v in entry.values]

match_with_task_val(entry::ValueEntry, other::ValueEntry, key) =
    if entry.type == other.type && entry.values == other.values
        (key, Strict, copy_field)
    else
        missing
    end

value_updates(entry::ValueEntry, key, new_values) =
    Dict(key => entry)

struct NoDataEntry <: Entry
    type::Tp
end

get_matching_seq(entry::NoDataEntry) = Iterators.repeated(_ -> TypeOnly)
match_with_task_val(entry::NoDataEntry, other::ValueEntry, key) =
    might_unify(entry.type, other.type) ? (key, TypeOnly, copy_field) : missing

value_updates(entry::NoDataEntry, key, new_values) =
    Dict(key => ValueEntry(entry.type, new_values))
