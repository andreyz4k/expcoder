
all_abstractors = Dict{Program,Vector{Program}}()


all_abstractors[every_primitive["repeat"]] = [
    parse_program("(lambda (fold \$0 (car \$0) (lambda (lambda (if (eq? \$0 \$1) \$0 exception)))))"),
    every_primitive["length"],
]

function is_reversible(p::Primitive)
    return haskey(all_abstractors, p)
end

function is_reversible(p::Apply)
    return is_reversible(p.f) && ((isa(p.x, Hole) || (isa(p.x, FreeVar) && isnothing(p.x.key))) && !isarrow(p.x.t))
end

function is_reversible(p::Program)
    false
end

fill_free_holes(p::Apply) = Apply(fill_free_holes(p.f), fill_free_holes(p.x))

fill_free_holes(p::Hole) = FreeVar(p.t, nothing)

fill_free_holes(p::Program) = p

function get_reversed_program(p::Apply, output_var)
    get_reversed_program(p.f, output_var)
end

function get_reversed_program(p::Primitive, output_var)
    output_type = output_var[2].values[output_var[1]].value.type
    [Apply(pr, FreeVar(output_type, output_var[1])) for pr in all_abstractors[p]]
end
