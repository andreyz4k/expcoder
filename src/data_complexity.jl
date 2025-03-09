
function get_complexity_summary(values, t)
    accum = Accumulator{String,Int64}()
    max_result = Accumulator{String,Int64}()
    options_count = 0
    for value in values
        max_accum = Accumulator{String,Int64}()
        ops = get_complexity_summary(value, t, accum, max_accum)
        options_count += ops
        for (k, v) in max_accum
            if !haskey(max_result, k) || max_result[k] < v
                max_result[k] = v
            end
        end
    end
    accum["either"] = options_count
    return accum, max_result, options_count
end

function get_complexity_summary(@nospecialize(values), t::TypeConstructor, accum, max_accum)
    inc!(accum, t.name)
    inc!(max_accum, t.name)
    if isempty(t.arguments)
        return 1
    elseif length(t.arguments) == 1
        for v in values
            get_complexity_summary(v, t.arguments[1], accum, max_accum)
        end
    elseif length(t.arguments) == 2
        get_complexity_summary(values[1], t.arguments[1], accum, max_accum)
        get_complexity_summary(values[2], t.arguments[2], accum, max_accum)
    else
        error("unsupported type constructor: $(t.name)")
    end
    return 1
end

function get_complexity_summary(values::AnyObject, t::TypeVariable, accum, max_accum)
    inc!(accum, "any")
    inc!(max_accum, "any")
    return 1
end

function get_complexity_summary(values::AnyObject, t::TypeConstructor, accum, max_accum)
    inc!(accum, t.name)
    inc!(max_accum, t.name)
    for arg in t.arguments
        get_complexity_summary(values, arg, accum, max_accum)
    end
    return 1
end

function get_complexity_summary(values::Nothing, t::TypeConstructor, accum, max_accum)
    inc!(max_accum, t.name)
    return 1
end
function get_complexity_summary(values::Nothing, t::TypeVariable, accum, max_accum)
    inc!(max_accum, "nothing")
    return 1
end

function get_complexity_summary(values::EitherOptions, t::TypeConstructor, accum, max_accum)
    summary = Accumulator{String,Int64}()
    options_count = 0
    for (h, option) in values.options
        op_summary = Accumulator{String,Int64}()
        ops_count = get_complexity_summary(option, t, summary, op_summary)
        options_count += ops_count
        for (k, v) in op_summary
            if !haskey(max_accum, k) || max_accum[k] < v
                max_accum[k] = v
            end
        end
    end

    for (k, count) in summary
        inc!(accum, k, div(count, length(values.options)))
    end
    return options_count
end

get_complexity_summary(values::PatternWrapper, t::TypeConstructor, accum, max_accum) =
    get_complexity_summary(values.value, t, accum, max_accum)
get_complexity_summary(values::PatternWrapper, t::TypeVariable, accum, max_accum) =
    get_complexity_summary(values.value, t, accum, max_accum)

get_complexity_summary(values::AbductibleValue, t::TypeConstructor, accum, max_accum) =
    get_complexity_summary(values.value, t, accum, max_accum)
get_complexity_summary(values::AbductibleValue, t::TypeVariable, accum, max_accum) =
    get_complexity_summary(values.value, t, accum, max_accum)

function get_complexity(sc::SolutionContext, summary::Accumulator)
    return sum(sc.type_weights[tname] * count for (tname, count) in summary; init = 0.0)
end
