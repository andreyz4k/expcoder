
all_abstractors = Dict{Program,Dict{String,Any}}()

function reverse_repeat(value)
    if any(v != value[1] for v in value)
        error("Elements are not equal")
    end
    return value[1], length(value)
end

all_abstractors[every_primitive["repeat"]] = Dict(
    "reversed" => _ -> _ -> reverse_repeat,
    "replacements" => [:default, :default],
)

function reverse_cons(value)
    if isempty(value)
        error("List is empty")
    end
    return value[1], value[2:end]
end

all_abstractors[every_primitive["cons"]] = Dict(
    "reversed" => _ -> _ -> reverse_cons,
    "replacements" => [:default, :default],
)


function is_reversible(p::Primitive)
    return haskey(all_abstractors, p)
end

function is_reversible(p::Apply)
    if is_reversible(p.f)
        if isa(p.x, Hole)
            return !isarrow(p.x.t)
        end
        if isa(p.x, Abstraction)
            return is_reversible(p.x.b)
        end
    end
    false
end

is_reversible(p::Invented) = is_reversible(p.p)

function is_reversible(p::Program)
    false
end

function _replace_free_vars(p::FreeVar, replacements)
    popfirst!(replacements)
end

function _replace_free_vars(p::Apply, replacements)
    new_f = _replace_free_vars(p.f, replacements)
    new_x = _replace_free_vars(p.x, replacements)
    Apply(new_f, new_x)
end

_replace_free_vars(p::Abstraction, replacements) = Abstraction(_replace_free_vars(p.b, replacements))
_replace_free_vars(p::Program, replacements) = p


function map_function_replacement(map_f, filled_types)
    if length(filled_types) == 1
        replacements = [Index(0)]
    elseif length(filled_types) == 2
        replacements =
            [Apply(every_primitive["tuple2_first"], Index(0)), Apply(every_primitive["tuple2_second"], Index(0))]
    end
    return _replace_free_vars(map_f, replacements), filled_types
end

function zip_free_vars(filled_hole, filled_types)
    if length(filled_types) == 2
        return filled_hole, [filled_types[2]]
    elseif length(filled_types) == 3
        return (
            Apply(
                Apply(every_primitive["zip2"], FreeVar(tlist(filled_types[1]), nothing)),
                FreeVar(tlist(filled_types[2]), nothing),
            ),
            [tlist(filled_types[1]), tlist(filled_types[2])],
        )
    end
end

function reverse_map(map_f)
    rev_inner = get_reversed_program(map_f)
    function rev_map(value)
        processed_values = map(rev_inner, value)
        return zip(processed_values...)
    end
end
all_abstractors[every_primitive["map"]] = Dict(
    "reversed" => map_f -> _ -> reverse_map(map_f),
    "replacements" => [map_function_replacement, zip_free_vars],
)


function fill_free_holes(p::Program)
    res, _, _ = _fill_free_holes(p)
    res
end

function _fill_free_holes(p::Apply)
    new_f, replacements, filled_types = _fill_free_holes(p.f)
    x_replacement = replacements[1]
    new_x, replacements_x, filled_types_x = _fill_free_holes(p.x)
    filled_types = vcat(filled_types, filled_types_x)
    if x_replacement != :default
        new_x, filled_types = x_replacement(new_x, filled_types)
    end
    Apply(new_f, new_x), view(replacements, 2:length(replacements)), filled_types
end

function _fill_free_holes(p::Hole)
    FreeVar(p.t, nothing), [], [p.t]
end

function _fill_free_holes(p::Primitive)
    replacements = all_abstractors[p]["replacements"]
    p, replacements, []
end

function _fill_free_holes(p::Abstraction)
    new_b, replacements, filled_types = _fill_free_holes(p.b)
    Abstraction(new_b), replacements, filled_types
end

function get_reversed_program(p::Primitive)
    return all_abstractors[p]["reversed"]
end

function get_reversed_program(p::Apply)
    reversed_fs = get_reversed_program(p.f)
    return reversed_fs(p.x)
end

get_reversed_program(p::Abstraction) = get_reversed_program(p.b)
