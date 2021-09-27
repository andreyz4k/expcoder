
abstract type Program end

struct Index <: Program
    n::Int64
end

struct Abstraction <: Program
    b::Program
end

struct Apply <: Program
    f::Program
    x::Program
end

struct Primitive <: Program
    t::Tp
    name::String
    code::Any

    function Primitive(name::String, t::Tp, x; skip_saving = false)
        p = new(t, name, x)
        if !skip_saving
            @assert !haskey(every_primitive, name)
            every_primitive[name] = p
        end
        p
    end
end

every_primitive = Dict{String,Primitive}()
struct Invented <: Program
    t::Tp
    b::Program
end

Base.show(io::IO, p::Index) = print(io, "\$", p.n)
Base.show(io::IO, p::Abstraction) = print(io, "(lambda ", p.b, ")")
Base.show(io::IO, p::Apply) = print(io, "(", p.f, " ", p.x, ")")
Base.show(io::IO, p::Primitive) = p.name == "FREE_VAR" ? print(io, "FREE_VAR(", p.t, ")") : print(io, p.name)
Base.show(io::IO, p::Invented) = print(io, "#(", p.b, ")")


struct ProgramBlock
    p::Program
    inputs::Vector{String}
    outputs::Vector{String}
end


struct UnknownPrimitive <: Exception
    name::String
end


function lookup_primitive(name)
    if haskey(every_primitive, name)
        every_primitive[name]
    else
        throw(UnknownPrimitive(name))
    end
end


parse_token = token_parser(
    c -> isletter(c) || isdigit(c) || in(c, ['_', '-', '?', '/', '.', '*', '\'', '+', ',', '>', '<', '@', '|']),
)
parse_whitespace = token_parser(can_be_empty = true, isspace)
parse_number = token_parser(isdigit)

parse_primitive = bind_parsers(parse_token, (name -> try
    return_parse(lookup_primitive(name))
catch e
    @error "Error finding type of primitive $name"
    parse_failure
end))

parse_variable = bind_parsers(
    constant_parser("\$"),
    (_ -> bind_parsers(parse_number, (n -> Index(parse(Int64, n)) |> return_parse))),
)

parse_fixed_real = bind_parsers(
    constant_parser("real"),
    (_ -> bind_parsers(parse_token, (v -> Primitive(treal, "real", parse(Float64, v)) |> return_parse))),
)

parse_invented = bind_parsers(
    constant_parser("#"),
    (
        _ -> bind_parsers(
            _parse_program,
            (p -> begin
                t = try
                    infer_program_type(empty_context, [], p)[2]
                catch e
                    if isa(e, UnificationFailure) || isa(e, UnboundVariable)
                        @warn "WARNING: Could not type check invented $p"
                        t0
                    else
                        rethrow()
                    end
                end

                return_parse(Invented(t, p))
            end),
        )
    ),
)

nabstractions(n, b) = n == 0 ? b : nabstractions((n - 1), (Abstraction(b)))

parse_abstraction = bind_parsers(
    constant_parser("(lambda"),
    (
        _ -> branch_parsers(
            bind_parsers(
                parse_whitespace,
                (
                    _ -> bind_parsers(
                        _parse_program,
                        (b -> bind_parsers(constant_parser(")"), (_ -> return_parse(Abstraction(b))))),
                    )
                ),
            ),
            bind_parsers(
                parse_number,
                (
                    n -> bind_parsers(
                        parse_whitespace,
                        (
                            _ -> bind_parsers(
                                _parse_program,
                                (
                                    b -> bind_parsers(
                                        constant_parser(")"),
                                        (_ -> return_parse(nabstractions((parse(Int64, n)), b))),
                                    )
                                ),
                            )
                        ),
                    )
                ),
            ),
        )
    ),
)

parse_application_sequence(maybe_function) = bind_parsers(
    parse_whitespace,
    (
        _ -> if isnothing(maybe_function)
            bind_parsers(_parse_program, (f -> parse_application_sequence(f)))
        else
            branch_parsers(
                return_parse(maybe_function),
                bind_parsers(_parse_program, (x -> parse_application_sequence(Apply(maybe_function, x)))),
            )
        end
    ),
)

parse_application = bind_parsers(
    constant_parser("("),
    (
        _ -> bind_parsers(
            parse_application_sequence(nothing),
            (a -> bind_parsers(constant_parser(")"), (_ -> return_parse(a)))),
        )
    ),
)

_parse_program = branch_parsers(
    parse_application,
    parse_primitive,
    parse_variable,
    parse_invented,
    parse_abstraction,
    parse_fixed_real,
)


function parse_program(s)
    res = first((p for (p, n) in _parse_program(s, 1) if n == length(s) + 1), 1)
    if isempty(res)
        error("Could not parse: $s")
    else
        res[1]
    end
end

function infer_program_type(context, environment, p::Index)::Tuple{Context,Tp}
    t = environment[p.n]
    if isnothing(t)
        throw(UnboundVariable())
    else
        apply_context(context, t)
    end
end

infer_program_type(context, environment, p::Primitive)::Tuple{Context,Tp} = instantiate(p.t, context)

infer_program_type(context, environment, p::Invented)::Tuple{Context,Tp} = instantiate(p.t, context)

function infer_program_type(context, environment, p::Abstraction)::Tuple{Context,Tp}
    (xt, context) = makeTID(context)
    (context, rt) = infer_program_type(context, vcat(xt, environment), p.b)
    applyContext(context, arrow(xt, rt))
end

function infer_program_type(context, environment, p::Apply)::Tuple{Context,Tp}
    (rt, context) = makeTID(context)
    (context, xt) = infer_program_type(context, environment, p.x)
    (context, ft) = infer_program_type(context, environment, p.f)
    context = unify(context, ft, arrow(xt, rt))
    applyContext(context, rt)
end

closed_inference(p) = infer_program_type(empty_context, [], p)[2]

number_of_free_parameters(p::Invented) = number_of_free_parameters(p.b)
number_of_free_parameters(p::Abstraction) = number_of_free_parameters(p.b)
number_of_free_parameters(p::Apply) = number_of_free_parameters(p.f) + number_of_free_parameters(p.x)
number_of_free_parameters(p::Primitive) =
    if in(p.name, Set(["REAL", "STRING", "r_const", "FREE_VAR"]))
        1
    else
        0
    end
number_of_free_parameters(::Index) = 0

application_function(p::Apply) = application_function(p.f)
application_function(p::Program) = p

function application_parse(p::Apply)
    (f, arguments) = application_parse(p.f)
    (f, vcat(arguments, [p.x]))
end
application_parse(p::Program) = (p, [])


analyze_evaluation(p::Abstraction) = environment -> (x -> (analyze_evaluation(p.b)(vcat([x], environment))))

analyze_evaluation(p::Index) = environment -> environment[p.n]

analyze_evaluation(p::Primitive) = _ -> p.code

analyze_evaluation(p::Invented) = _ -> analyze_evaluation(p.b)([])

function analyze_evaluation(p::Apply)
    if isa(p.f, Apply) && isa(p.f.f, Apply) && isa(p.f.f.f, Primitive) && p.f.f.f.name == "if"
        branch = analyze_evaluation(p.f.f.x)
        yes = analyze_evaluation(p.f.x)
        no = analyze_evaluation(p.x)
        return environment -> (branch(environment) ? yes(environment) : no(environment))
    else
        environment -> (analyze_evaluation(p.f)(environment)(analyze_evaluation(p.x)(environment)))
    end
end

function run_analyzed_with_arguments(p, arguments)
    l = p([])
    for x in arguments
        l = l(x)
    end
    return l
end

include("primitives.jl")

copy_field = Primitive("copy",arrow(t0, t0),  (x -> x); skip_saving=true)
