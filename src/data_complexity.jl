

function get_complexity(sc::SolutionContext, values, t::TypeConstructor)
    if isempty(t.arguments)
        return sc.type_weights[t.name] * length(values)
    end
    if length(t.arguments) == 1
        if isempty(t.arguments[1].arguments)
            return sum(
                sc.type_weights[t.name] + sc.type_weights[t.arguments[1].name] * length(v) for v in values;
                init = 0.0,
            )
        else
            return sum(sc.type_weights[t.name] + get_complexity(sc, v, t.arguments[1]) for v in values; init = 0.0)
        end
    else
        error("unsupported type constructor: " + t.name)
    end
    error("unsupported type constructor: " + t.name)
end
