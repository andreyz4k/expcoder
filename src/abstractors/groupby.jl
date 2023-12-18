
function rev_groupby(f, item, groups)
    key = f(item)
    result = Set()
    matched = false
    for (k, values) in groups
        if k == key
            matched = true
            push!(result, (k, union(values, [item])))
        else
            push!(result, (k, values))
        end
    end
    if !matched
        push!(result, (key, Set([item])))
    end
    return result
end

function reverse_rev_groupby()
    function _reverse_rev_groupby(groups, context)
        output_options = []
        for (k, values) in groups
            for v in values
                new_groups = copy(groups)
                delete!(new_groups, (k, values))
                new_values = copy(values)
                delete!(new_values, v)
                if !isempty(new_values)
                    push!(new_groups, (k, new_values))
                end
                push!(output_options, (v, new_groups))
            end
        end
        if length(output_options) == 0
            error("Groups are empty")
        elseif length(output_options) == 1
            r = first(output_options)
            result = [SkipArg(), r[1], r[2]]
        else
            hashed_options = Dict(rand(UInt64) => option for option in output_options)
            result = Any[SkipArg()]
            for i in 1:2
                push!(result, EitherOptions(Dict(h => option[i] for (h, option) in hashed_options)))
            end
        end
        return groups,
        ReverseRunContext(
            context.arguments,
            vcat(context.predicted_arguments, reverse(result)),
            context.calculated_arguments,
            context.filled_indices,
            context.filled_vars,
        )
    end
    return [(_has_no_holes, CustomArgChecker(false, -1, false, nothing))], _reverse_rev_groupby
end

# This function is meant to be used with fold
@define_custom_reverse_primitive(
    "rev_groupby",
    arrow(arrow(t0, t1), t0, tset(ttuple2(t1, tset(t0))), tset(ttuple2(t1, tset(t0)))),
    (f -> (item -> (grs -> rev_groupby(f, item, grs)))),
    reverse_rev_groupby()
)
