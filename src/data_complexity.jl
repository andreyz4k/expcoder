
using DataStructures: Accumulator
function get_complexity_summary(values, t::TypeConstructor)
    result = Accumulator{String,Int64}()
    result[t.name] = length(values)
    if isempty(t.arguments)
        return result
    elseif length(t.arguments) == 1
        merge!(result, [get_complexity_summary(v, t.arguments[1]) for v in values]...)
        return result
    else
        error("unsupported type constructor: " + t.name)
    end
end


function get_complexity(sc::SolutionContext, summary::Accumulator)
    return sum(sc.type_weights[tname] * count for (tname, count) in summary; init = 0.0)
end
