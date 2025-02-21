
function __unfold_trace_value(val)
    return [val], ones(Float32, 1, 1)
end

function __unfold_trace_value(val::EitherOptions)
    output = []
    next_masks = []
    for op in values(val.options)
        vals, mask = __unfold_trace_value(op)
        append!(output, vals)
        push!(next_masks, mask)
    end

    cur_m = fill(1 / Float32(length(val.options)), length(val.options))
    out_mask = _make_next_mask(next_masks) * cur_m

    return output, out_mask
end

function _unfold_trace_value(tp, trace_val)
    output = []
    next_masks = []
    for val in trace_val
        vals, mask = __unfold_trace_value(val)
        for v in vals
            push!(output, string((tp, v)))
        end
        push!(next_masks, mask)
    end
    cur_m = fill(1 / Float32(length(trace_val)), length(trace_val))
    return output, _make_next_mask(next_masks) * cur_m
end
