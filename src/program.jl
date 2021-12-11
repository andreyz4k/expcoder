
abstract type Program end

struct Index <: Program
    n::Int64
end

Base.hash(p::Index, h::UInt64) = hash(p.n, h)
Base.:(==)(p::Index, q::Index) = p.n == q.n

struct Abstraction <: Program
    b::Program
end
Base.hash(p::Abstraction, h::UInt64) = hash(p.b, h)
Base.:(==)(p::Abstraction, q::Abstraction) = p.b == q.b

struct Apply <: Program
    f::Program
    x::Program
end
Base.hash(p::Apply, h::UInt64) = hash(p.f, h) + hash(p.x, h)
Base.:(==)(p::Apply, q::Apply) = p.f == q.f && p.x == q.x

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
Base.hash(p::Primitive, h::UInt64) = hash(p.name, h)
Base.:(==)(p::Primitive, q::Primitive) = p.name == q.name

every_primitive = Dict{String,Primitive}()
struct Invented <: Program
    t::Tp
    b::Program
end
Base.hash(p::Invented, h::UInt64) = hash(p.b, h)
Base.:(==)(p::Invented, q::Invented) = p.b == q.b

struct Hole <: Program
    t::Tp
    grammar::Any
end
Base.hash(p::Hole, h::UInt64) = hash(p.t, h) + hash(p.grammar, h)
Base.:(==)(p::Hole, q::Hole) = p.t == q.t && p.grammar == q.grammar

struct FreeVar <: Program
    t::Tp
    key::Union{String,Nothing}
end
Base.hash(p::FreeVar, h::UInt64) = hash(p.t, h) + hash(p.key, h)
Base.:(==)(p::FreeVar, q::FreeVar) = p.t == q.t && p.key == q.key


struct SetConst <: Program
    t::Tp
    value::Any
end
Base.hash(p::SetConst, h::UInt64) = hash(p.t, h) + hash(p.value, h)
Base.:(==)(p::SetConst, q::SetConst) = p.t == q.t && p.value == q.value

struct LetClause <: Program
    var_name::String
    v::Program
    b::Program
end
Base.hash(p::LetClause, h::UInt64) = hash(p.var_name, h) + hash(p.v, h) + hash(p.b, h)
Base.:(==)(p::LetClause, q::LetClause) = p.var_name == q.var_name && p.v == q.v && p.b == q.b


struct MultiLetClause <: Program
    var_names::Vector{String}
    inp_var_names::Vector{String}
    v::Program
    rev_v::Vector{Program}
    b::Program
end
Base.hash(p::MultiLetClause, h::UInt64) = hash(p.var_names, h) + hash(p.v, h) + hash(p.b, h)
Base.:(==)(p::MultiLetClause, q::MultiLetClause) = p.var_names == q.var_names && p.v == q.v && p.b == q.b

struct ExceptionProgram <: Program end


Base.show(io::IO, p::Program) = print(io, show_program(p, false)...)

show_program(p::Index, is_function::Bool) = ["\$", p.n]
show_program(p::Abstraction, is_function::Bool) = vcat(["(lambda "], show_program(p.b, false), [")"])
show_program(p::Apply, is_function::Bool) =
    if is_function
        vcat(show_program(p.f, true), [" "], show_program(p.x, false))
    else
        vcat(["("], show_program(p.f, true), [" "], show_program(p.x, false), [")"])
    end
show_program(p::Primitive, is_function::Bool) = [p.name]
show_program(p::FreeVar, is_function::Bool) = isnothing(p.key) ? ["FREE_VAR"] : [p.key]
show_program(p::Hole, is_function::Bool) = ["??(", p.t, ")"]
show_program(p::Invented, is_function::Bool) = vcat(["#"], show_program(p.b, false))
show_program(p::SetConst, is_function::Bool) = vcat(["Const{", p.t, "}(", p.value, ")"])
show_program(p::LetClause, is_function::Bool) =
    vcat(["let ", p.var_name, " = "], show_program(p.v, false), [" in "], show_program(p.b, false))
show_program(p::MultiLetClause, is_function::Bool) = vcat(
    ["let ", join(p.var_names, ", "), " = rev("],
    show_program(p.v, false),
    [", [", join(p.inp_var_names, ", "), "]) in "],
    show_program(p.b, false),
)
show_program(p::ExceptionProgram, is_function::Bool) = ["EXCEPTION"]

abstract type AbstractProgramBlock end

struct ProgramBlock <: AbstractProgramBlock
    p::Program
    analized_p::Function
    type::Tp
    cost::Float64
    input_vars::Vector{Tuple{String,Any}}
    output_var::Tuple{String,Any}
end

ProgramBlock(p::Program, type::Tp, cost, input_vars, output_var) =
    ProgramBlock(p, analyze_evaluation(p), type, cost, input_vars, output_var)

Base.show(io::IO, block::ProgramBlock) = print(
    io,
    "ProgramBlock(",
    block.p,
    ", ",
    block.type,
    ", ",
    block.cost,
    ", ",
    ["($k, $(hash(br)))" for (k, br) in block.input_vars],
    ", (",
    block.output_var[1],
    ", ",
    hash(block.output_var[2]),
    "))",
)

struct ReverseProgramBlock <: AbstractProgramBlock
    p::Program
    reverse_blocks::Vector{ProgramBlock}
    cost::Float64
    input_vars::Vector{Tuple{String,Any}}
    output_vars::Vector{Tuple{String,Any}}
end


Base.show(io::IO, block::ReverseProgramBlock) = print(
    io,
    "ReverseProgramBlock(",
    block.p,
    ", ",
    block.reverse_blocks,
    ", ",
    block.cost,
    ", (",
    block.input_vars[1][1],
    ", ",
    hash(block.input_vars[1][2]),
    "), ",
    ["($k, $(hash(br)))" for (k, br) in block.output_vars],
    ")",
)

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
    # @error "Error finding type of primitive $name"
    parse_failure
end))

parse_variable = bind_parsers(
    constant_parser("\$"),
    (_ -> bind_parsers(parse_number, (n -> Index(parse(Int64, n)) |> return_parse))),
)

parse_fixed_real = bind_parsers(
    constant_parser("real"),
    (
        _ -> bind_parsers(
            parse_token,
            (v -> Primitive(treal, "real", parse(Float64, v); skip_saving = true) |> return_parse),
        )
    ),
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

parse_exception = bind_parsers(constant_parser("exception"), _ -> return_parse(ExceptionProgram()))

_parse_program = branch_parsers(
    parse_application,
    parse_exception,
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
    t = environment[p.n+1]
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
    (context, rt) = infer_program_type(context, vcat([xt], environment), p.b)
    apply_context(context, arrow(xt, rt))
end

function infer_program_type(context, environment, p::Apply)::Tuple{Context,Tp}
    (rt, context) = makeTID(context)
    (context, xt) = infer_program_type(context, environment, p.x)
    (context, ft) = infer_program_type(context, environment, p.f)
    context = unify(context, ft, arrow(xt, rt))
    apply_context(context, rt)
end

infer_program_type(context, environment, p::FreeVar) = instantiate(p.t, context)

infer_program_type(context, environment, p::ExceptionProgram) = instantiate(t0, context)

closed_inference(p) = infer_program_type(empty_context, [], p)[2]

number_of_free_parameters(p::Invented) = number_of_free_parameters(p.b)
number_of_free_parameters(p::Abstraction) = number_of_free_parameters(p.b)
number_of_free_parameters(p::Apply) = number_of_free_parameters(p.f) + number_of_free_parameters(p.x)
number_of_free_parameters(p::FreeVar) = 1
number_of_free_parameters(p::Primitive) =
    if in(p.name, Set(["REAL", "STRING", "r_const"]))
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


function analyze_evaluation(p::Abstraction)
    b = analyze_evaluation(p.b)
    (environment, workspace) -> (x -> (b(vcat([x], environment), workspace)))
end

analyze_evaluation(p::Index) = (environment, workspace) -> environment[p.n+1]

analyze_evaluation(p::FreeVar) = (environment, workspace) -> workspace[p.key]

analyze_evaluation(p::Primitive) = (_, _) -> p.code

function analyze_evaluation(p::Invented)
    b = analyze_evaluation(p.b)
    (_, _) -> b([], Dict())
end

function analyze_evaluation(p::Apply)
    if isa(p.f, Apply) && isa(p.f.f, Apply) && isa(p.f.f.f, Primitive) && p.f.f.f.name == "if"
        branch = analyze_evaluation(p.f.f.x)
        yes = analyze_evaluation(p.f.x)
        no = analyze_evaluation(p.x)
        return (environment, workspace) ->
            (branch(environment, workspace) ? yes(environment, workspace) : no(environment, workspace))
    else
        f = analyze_evaluation(p.f)
        x = analyze_evaluation(p.x)
        (environment, workspace) -> (f(environment, workspace)(x(environment, workspace)))
    end
end

analyze_evaluation(p::SetConst) = (_, _) -> p.value

function analyze_evaluation(p::LetClause)
    v = analyze_evaluation(p.v)
    b = analyze_evaluation(p.b)
    (environment, workspace) -> b(environment, merge(workspace, Dict(p.var_name => v(environment, workspace))))
end

function analyze_evaluation(p::MultiLetClause)
    rev_vs = [analyze_evaluation(v) for v in p.rev_v]
    b = analyze_evaluation(p.b)
    (environment, workspace) -> b(
        environment,
        merge(
            workspace,
            merge(Dict(var_name => v(environment, workspace) for (var_name, v) in zip(p.var_names, rev_vs))),
        ),
    )
end

function analyze_evaluation(p::ExceptionProgram)
    (environment, workspace) -> error("Inapplicable program")
end

function run_analyzed_with_arguments(p, arguments, workspace)
    l = p([], workspace)
    for x in arguments
        l = l(x)
    end
    return l
end

include("primitives.jl")
include("abstractors.jl")
