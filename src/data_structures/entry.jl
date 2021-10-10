
abstract type Entry end

struct ValueEntry <: Entry
    type::Tp
    values::Vector
end

get_matching_seq(entry::ValueEntry) = [(rv -> rv == v ? Strict : NoMatch) for v in entry.values]

match_with_task_val(entry::ValueEntry, other::ValueEntry, key) =
    if entry.type == other.type && entry.values == other.values
        (key, Strict, FreeVar(other.type, key))
    else
        missing
    end

value_updates(sc, key, new_values, t) = _value_updates(sc, sc[key], key, new_values, t)

_value_updates(sc, entry::ValueEntry, key, new_values, t) = Dict(key => entry), Dict()

struct NoDataEntry <: Entry
    type::Tp
end

get_matching_seq(entry::NoDataEntry) = Iterators.repeated(_ -> TypeOnly)
match_with_task_val(entry::NoDataEntry, other::ValueEntry, key) =
    might_unify(entry.type, other.type) ? (key, TypeOnly, FreeVar(other.type, key)) : missing

function _value_updates(sc, entry::NoDataEntry, key, new_values, t)
    known_updates = Dict(key => ValueEntry(t, new_values))
    unknown_updates = get_unknown_updates(sc, key, t)

    known_updates, unknown_updates
end

function get_unknown_updates(sc, key, t)
    result = Dict()
    for op in downstream_ops(sc, key)
        i = findfirst(k -> k == key, op.inputs)
        arg_type = arguments_of_type(op.type)[i]
        if is_polymorphic(arg_type)
            context = empty_context
            context, op_type = instantiate(op.type, context)
            for (k, arg_type) in zip(op.inputs, arguments_of_type(op_type))
                if isknown(sc, k)
                    context = unify(context, arg_type, sc[k].type)
                end
            end
            arg_type = arguments_of_type(op_type)[i]
            context = unify(context, t, arg_type)
            context, new_op_type = apply_context(context, op_type)
            for (k, old_type, new_type) in zip(op.inputs, arguments_of_type(op_type), arguments_of_type(new_op_type))
                if k != key && !isknown(sc, k) && old_type != new_type
                    result[k] = NoDataEntry(new_type)
                end
            end
            new_return = return_of_type(new_op_type)
            if return_of_type(op_type) != new_return
                result[op.output] = NoDataEntry(new_return)
                merge!(result, get_unknown_updates(sc, op.output, new_return))
            end
        end
    end
    result
end
