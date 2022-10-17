
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
    var_id::Union{Int,Nothing,String}
end
Base.hash(p::FreeVar, h::UInt64) = hash(p.t, h) + hash(p.var_id, h)
Base.:(==)(p::FreeVar, q::FreeVar) = p.t == q.t && p.var_id == q.var_id

struct SetConst <: Program
    t::Tp
    value::Any
end
Base.hash(p::SetConst, h::UInt64) = hash(p.t, h) + hash(p.value, h)
Base.:(==)(p::SetConst, q::SetConst) = p.t == q.t && p.value == q.value

struct LetClause <: Program
    var_id::Int
    v::Program
    b::Program
end
Base.hash(p::LetClause, h::UInt64) = hash(p.var_id, h) + hash(p.v, h) + hash(p.b, h)
Base.:(==)(p::LetClause, q::LetClause) = p.var_id == q.var_id && p.v == q.v && p.b == q.b

struct LetRevClause <: Program
    var_ids::Vector{Int}
    inp_var_id::Union{Int,String}
    v::Program
    rev_v::Any
    b::Program
end
Base.hash(p::LetRevClause, h::UInt64) = hash(p.var_ids, h) + hash(p.v, h) + hash(p.b, h)
Base.:(==)(p::LetRevClause, q::LetRevClause) = p.var_ids == q.var_ids && p.v == q.v && p.b == q.b

struct WrapEither <: Program
    var_ids::Vector{Int}
    inp_var_id::Union{Int,String}
    fixer_var_id::Int
    v::Program
    rev_v::Any
    f::FreeVar
    b::Program
end
Base.hash(p::WrapEither, h::UInt64) =
    hash(p.var_ids, hash(p.inp_var_id, hash(p.fixer_var_id, hash(p.v, hash(p.f, hash(p.b, h))))))
Base.:(==)(p::WrapEither, q::WrapEither) =
    p.var_ids == q.var_ids &&
    p.inp_var_id == q.inp_var_id &&
    p.fixer_var_id == q.fixer_var_id &&
    p.v == q.v &&
    p.f == q.f &&
    p.b == q.b

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
show_program(p::FreeVar, is_function::Bool) =
    isnothing(p.var_id) ? ["FREE_VAR"] : ["\$", (isa(p.var_id, Int) ? "v" : ""), "$(p.var_id)"]
show_program(p::Hole, is_function::Bool) = ["??(", p.t, ")"]
show_program(p::Invented, is_function::Bool) = vcat(["#"], show_program(p.b, false))
show_program(p::SetConst, is_function::Bool) = vcat(["Const("], show_type(p.t, true), [", ", p.value, ")"])
show_program(p::LetClause, is_function::Bool) =
    vcat(["let \$v$(p.var_id) = "], show_program(p.v, false), [" in "], show_program(p.b, false))
show_program(p::LetRevClause, is_function::Bool) = vcat(
    [
        "let ",
        join(["\$v$v" for v in p.var_ids], ", "),
        " = rev(\$",
        (isa(p.inp_var_id, Int) ? "v" : ""),
        "$(p.inp_var_id) = ",
    ],
    show_program(p.v, false),
    [") in "],
    show_program(p.b, false),
)
show_program(p::WrapEither, is_function::Bool) = vcat(
    [
        "let ",
        join(["\$v$v" for v in p.var_ids], ", "),
        " = wrap(let ",
        join(["\$v$v" for v in p.var_ids], ", "),
        " = rev(\$",
        (isa(p.inp_var_id, Int) ? "v" : ""),
        "$(p.inp_var_id) = ",
    ],
    show_program(p.v, false),
    ["); let \$v$(p.fixer_var_id) = "],
    show_program(p.f, false),
    [") in "],
    show_program(p.b, false),
)
show_program(p::ExceptionProgram, is_function::Bool) = ["EXCEPTION"]

abstract type AbstractProgramBlock end

struct ProgramBlock <: AbstractProgramBlock
    p::Program
    analized_p::Function
    type::Tp
    cost::Float64
    input_vars::Vector{Int}
    output_var::Int
    is_reversible::Bool
end

ProgramBlock(p::Program, type::Tp, cost, input_vars, output_var, is_reversible) =
    ProgramBlock(p, analyze_evaluation(p), type, cost, input_vars, output_var, is_reversible)

Base.show(io::IO, block::ProgramBlock) = print(
    io,
    "ProgramBlock(",
    block.p,
    ", ",
    block.type,
    ", ",
    block.cost,
    ", ",
    block.input_vars,
    ", ",
    block.output_var,
    ")",
)

Base.:(==)(block::ProgramBlock, other::ProgramBlock) =
    block.p == other.p &&
    block.type == other.type &&
    block.cost == other.cost &&
    block.input_vars == other.input_vars &&
    block.output_var == other.output_var

Base.hash(block::ProgramBlock, h::UInt64) =
    hash(block.p, hash(block.type, hash(block.cost, hash(block.input_vars, hash(block.output_var, h)))))

struct ReverseProgramBlock <: AbstractProgramBlock
    p::Program
    reverse_program::Any
    cost::Float64
    input_vars::Vector{Int}
    output_vars::Vector{Int}
end

Base.show(io::IO, block::ReverseProgramBlock) =
    print(io, "ReverseProgramBlock(", block.p, ", ", block.cost, ", ", block.input_vars, ", ", block.output_vars, ")")

Base.:(==)(block::ReverseProgramBlock, other::ReverseProgramBlock) =
    block.p == other.p &&
    block.cost == other.cost &&
    block.input_vars == other.input_vars &&
    block.output_vars == other.output_vars

Base.hash(block::ReverseProgramBlock, h::UInt64) =
    hash(block.p, hash(block.cost, hash(block.input_vars, hash(block.output_vars, h))))

struct WrapEitherBlock <: AbstractProgramBlock
    main_block::ReverseProgramBlock
    fixer_var::Int
    cost::Float64
    input_vars::Vector{Int}
    output_vars::Vector{Int}
end

Base.:(==)(block::WrapEitherBlock, other::WrapEitherBlock) =
    block.main_block == other.main_block &&
    block.fixer_var == other.fixer_var &&
    block.cost == other.cost &&
    block.input_vars == other.input_vars &&
    block.output_vars == other.output_vars

Base.hash(block::WrapEitherBlock, h::UInt64) =
    hash(block.main_block, hash(block.fixer_var, hash(block.cost, hash(block.input_vars, hash(block.output_vars, h)))))

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

analyze_evaluation(p::FreeVar) = (environment, workspace) -> workspace[p.var_id]

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
    (environment, workspace) -> b(environment, merge(workspace, Dict(p.var_id => v(environment, workspace))))
end

function analyze_evaluation(p::LetRevClause)
    b = analyze_evaluation(p.b)
    (environment, workspace) -> begin
        vals = p.rev_v(workspace[p.inp_var_id])
        b(environment, merge(workspace, Dict(var_id => val for (var_id, val) in zip(p.var_ids, vals))))
    end
end

function analyze_evaluation(p::WrapEither)
    b = analyze_evaluation(p.b)
    f = analyze_evaluation(p.f)
    (environment, workspace) -> begin
        vals = p.rev_v(workspace[p.inp_var_id])
        unfixed_vals = Dict(var_id => val for (var_id, val) in zip(p.var_ids, vals))
        fixed_val = f(environment, workspace)

        fixed_hashes = [_get_fixed_hashes(unfixed_vals[p.fixer_var_id], fixed_val)]

        fixed_values = Dict()
        for (var_id, target_value) in unfixed_vals
            if var_id == p.fixer_var_id
                fixed_values[var_id] = fixed_val
            else
                fixed_values[var_id] = _fix_option_hashes(fixed_hashes, [target_value])[1]
            end
        end

        b(environment, merge(workspace, fixed_values))
    end
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
