
abstract type Program <: Function end

struct Index <: Program
    n::Int64
    hash_value::UInt64
    Index(n::Int64) = new(n, hash(n))
end

Base.hash(p::Program, h::UInt64) = hash(p.hash_value, h)
Base.:(==)(p::Index, q::Index) = p.n == q.n

struct Abstraction <: Program
    b::Program
    hash_value::UInt64
    Abstraction(b::Program) = new(b, hash(b))
end
Base.:(==)(p::Abstraction, q::Abstraction) = p.b == q.b

struct Abstraction2{B} <: Program
    b::B
    hash_value::UInt64
    base::Abstraction
    Abstraction2(b::B, base::Abstraction) where {B} = new{B}(b, hash(b), base)
end
Base.:(==)(p::Abstraction2, q::Abstraction2) = p.b == q.b

struct Apply <: Program
    f::Program
    x::Program
    hash_value::UInt64
    Apply(f::Program, x::Program) = new(f, x, hash(f, hash(x)))
end
Base.:(==)(p::Apply, q::Apply) = p.f == q.f && p.x == q.x

struct Apply2{F,X} <: Program
    f::F
    x::X
    hash_value::UInt64
    Apply2(f::F, x::X) where {F,X} = new{F,X}(f, x, hash(f, hash(x)))
end
Base.:(==)(p::Apply2, q::Apply2) = p.f == q.f && p.x == q.x

struct Primitive <: Program
    t::Tp
    name::String
    code::Any
    hash_value::UInt64
    Primitive(t::Tp, name::String, code::Any) = new(t, name, code, hash(name))
end

Base.:(==)(p::Primitive, q::Primitive) = p.name == q.name

struct Primitive2{C} <: Program
    t::Tp
    name::String
    code::Any
    hash_value::UInt64
    Primitive2(t::Tp, name::String, code::Any) = new{Val{Symbol(name)}}(t, name, code, hash(name))
end

Base.:(==)(p::Primitive2, q::Primitive2) = p.name == q.name

every_primitive = Dict{String,Primitive}()

macro define_primitive(name, t, x)
    return quote
        local n = $(esc(name))
        local p = Primitive($(esc(t)), n, $(esc(x)))
        every_primitive[n] = p
    end
end

struct Invented <: Program
    t::Tp
    b::Program
    is_reversible::Bool
    name::String
    hash_value::UInt64
    Invented(t::Tp, b::Program) = new(t, b, is_reversible(b), "#" * string(b), hash(b))
end
Base.:(==)(p::Invented, q::Invented) = p.name == q.name

struct Invented2{B} <: Program
    t::Tp
    b::B
    is_reversible::Bool
    name::String
    hash_value::UInt64
    Invented2(t::Tp, b::B) where {B} = new{B}(t, b, is_reversible(b), "#" * string(b), hash(b))
end
Base.:(==)(p::Invented2, q::Invented2) = p.name == q.name

struct Hole <: Program
    t::Tp
    root_t::Tp
    locations::Vector{Tuple{Program,Int64}}
    candidates_filter::Any
    possible_values::Any
    hash_value::UInt64
    Hole(t::Tp, root_t::Tp, locations, candidates_filter::Any, possible_values) = new(
        t,
        root_t,
        locations,
        candidates_filter,
        possible_values,
        hash(t, hash(root_t, hash(locations, hash(candidates_filter, hash(possible_values))))),
    )
end

Base.:(==)(p::Hole, q::Hole) =
    p.t == q.t &&
    p.locations == q.locations &&
    p.candidates_filter == q.candidates_filter &&
    p.possible_values == q.possible_values

struct FreeVar <: Program
    t::Tp
    fix_t::Tp
    var_id::Union{UInt64,String}
    location::Union{Nothing,Tuple{Program,Int64}}
    hash_value::UInt64
    FreeVar(t::Tp, fix_t::Tp, var_id::Union{UInt64,String}, location::Union{Nothing,Tuple{Program,Int64}}) =
        new(t, fix_t, var_id, location, hash(t, hash(var_id, hash(location))))
end
Base.:(==)(p::FreeVar, q::FreeVar) = p.t == q.t && p.var_id == q.var_id && p.location == q.location

struct SetConst <: Program
    t::Tp
    value::Any
    hash_value::UInt64
    SetConst(t::Tp, value::Any) = new(t, value, hash(t, hash(value)))
end
Base.:(==)(p::SetConst, q::SetConst) = p.t == q.t && p.value == q.value

struct SetConst2{V} <: Program
    t::Tp
    value::V
    hash_value::UInt64
    SetConst2(t::Tp, value::V) where {V} = new{V}(t, value, hash(t, hash(value)))
end
Base.:(==)(p::SetConst2, q::SetConst2) = p.t == q.t && p.value == q.value

struct LetClause <: Program
    var_id::UInt64
    v::Program
    b::Program
    hash_value::UInt64
    LetClause(var_id::UInt64, v::Program, b::Program) = new(var_id, v, b, hash(var_id, hash(v, hash(b))))
end
Base.:(==)(p::LetClause, q::LetClause) = p.var_id == q.var_id && p.v == q.v && p.b == q.b

struct LetRevClause <: Program
    var_ids::Vector{UInt64}
    inp_var_id::Union{UInt64,String}
    v::Program
    b::Program
    hash_value::UInt64
    LetRevClause(var_ids::Vector{UInt64}, inp_var_id::Union{UInt64,String}, v::Program, b::Program) =
        new(var_ids, inp_var_id, v, b, hash(var_ids, hash(inp_var_id, hash(v, hash(b)))))
end
Base.:(==)(p::LetRevClause, q::LetRevClause) =
    p.var_ids == q.var_ids && p.inp_var_id == q.inp_var_id && p.v == q.v && p.b == q.b

Base.show(io::IO, p::Program) = print(io, show_program(p, false)...)
Base.print(io::IO, p::Program) = print(io, show_program(p, false)...)

show_program(p::Index, is_function::Bool) = ["\$", p.n]
show_program(p::Abstraction, is_function::Bool) = vcat(["(lambda "], show_program(p.b, false), [")"])
show_program(p::Abstraction2, is_function::Bool) = vcat(["(lambda "], show_program(p.b, false), [")"])
show_program(p::Apply, is_function::Bool) =
    if is_function
        vcat(show_program(p.f, true), [" "], show_program(p.x, false))
    else
        vcat(["("], show_program(p.f, true), [" "], show_program(p.x, false), [")"])
    end
show_program(p::Apply2, is_function::Bool) =
    if is_function
        vcat(show_program(p.f, true), [" "], show_program(p.x, false))
    else
        vcat(["("], show_program(p.f, true), [" "], show_program(p.x, false), [")"])
    end
show_program(p::Primitive, is_function::Bool) = [p.name]
show_program(p::Primitive2, is_function::Bool) = [p.name]
show_program(p::FreeVar, is_function::Bool) = ["\$", (isa(p.var_id, UInt64) ? "v" : ""), "$(p.var_id)"]
show_program(p::Hole, is_function::Bool) = ["??(", p.t, ")"]
show_program(p::Invented, is_function::Bool) = [p.name]
show_program(p::Invented2, is_function::Bool) = [p.name]
show_program(p::SetConst, is_function::Bool) = vcat(["Const("], show_type(p.t, true), [", ", p.value, ")"])
show_program(p::SetConst2, is_function::Bool) = vcat(["Const("], show_type(p.t, true), [", ", p.value, ")"])
show_program(p::LetClause, is_function::Bool) =
    vcat(["let \$v$(p.var_id) = "], show_program(p.v, false), [" in "], show_program(p.b, false))
show_program(p::LetRevClause, is_function::Bool) = vcat(
    [
        "let ",
        join(["\$v$v" for v in p.var_ids], ", "),
        " = rev(\$",
        (isa(p.inp_var_id, UInt64) ? "v" : ""),
        "$(p.inp_var_id) = ",
    ],
    show_program(p.v, false),
    [") in "],
    show_program(p.b, false),
)

abstract type AbstractProgramBlock end

struct ProgramBlock <: AbstractProgramBlock
    p::Program
    type_id::UInt64
    cost::Float64
    input_vars::Vector{UInt64}
    output_var::UInt64
    is_reversible::Bool
end

Base.show(io::IO, block::ProgramBlock) = print(
    io,
    "ProgramBlock(",
    block.p,
    ", ",
    block.type_id,
    ", ",
    block.cost,
    ", ",
    block.input_vars,
    ", ",
    string(block.output_var),
    ")",
)

Base.:(==)(block::ProgramBlock, other::ProgramBlock) =
    block.p == other.p &&
    block.type_id == other.type_id &&
    block.cost == other.cost &&
    block.input_vars == other.input_vars &&
    block.output_var == other.output_var

Base.hash(block::ProgramBlock, h::UInt64) =
    hash(block.p, hash(block.type_id, hash(block.cost, hash(block.input_vars, hash(block.output_var, h)))))

struct ReverseProgramBlock <: AbstractProgramBlock
    p::Program
    type_id::UInt64
    cost::Float64
    input_vars::Vector{UInt64}
    output_vars::Vector{UInt64}
end

Base.show(io::IO, block::ReverseProgramBlock) = print(
    io,
    "ReverseProgramBlock(",
    block.p,
    ", ",
    block.type_id,
    ", ",
    block.cost,
    ", ",
    block.input_vars,
    ", ",
    block.output_vars,
    ")",
)

Base.:(==)(block::ReverseProgramBlock, other::ReverseProgramBlock) =
    block.p == other.p &&
    block.type_id == other.type_id &&
    block.cost == other.cost &&
    block.input_vars == other.input_vars &&
    block.output_vars == other.output_vars

Base.hash(block::ReverseProgramBlock, h::UInt64) =
    hash(block.p, hash(block.type_id, hash(block.cost, hash(block.input_vars, hash(block.output_vars, h)))))

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

function infer_program_type(context, environment, var_env, p::Index)::Tuple{Context,Tp}
    t = environment[p.n+1]
    if isnothing(t)
        throw(UnboundVariable())
    else
        apply_context(context, t)
    end
end

infer_program_type(context, environment, var_env, p::Primitive)::Tuple{Context,Tp} = instantiate(p.t, context)

infer_program_type(context, environment, var_env, p::Invented)::Tuple{Context,Tp} = instantiate(p.t, context)

function infer_program_type(context, environment, var_env, p::Abstraction)::Tuple{Context,Tp}
    (xt, context) = makeTID(context)
    (context, rt) = infer_program_type(context, vcat([xt], environment), var_env, p.b)
    apply_context(context, arrow(xt, rt))
end

function infer_program_type(context, environment, var_env, p::Apply)::Tuple{Context,Tp}
    (rt, context) = makeTID(context)
    (context, xt) = infer_program_type(context, environment, var_env, p.x)
    (context, ft) = infer_program_type(context, environment, var_env, p.f)
    context = unify(context, ft, arrow(xt, rt))
    if isnothing(context)
        error("Unification failed $ft $xt $rt $(p.x) $(p.f)")
    end
    apply_context(context, rt)
end

function infer_program_type(context, environment, var_env, p::FreeVar)::Tuple{Context,Tp}
    (context, rt) = instantiate(p.t, context)
    if haskey(var_env, p.var_id)
        unify(context, var_env[p.var_id], rt)
        context, rt = apply_context(context, rt)
    else
        var_env[p.var_id] = rt
    end
    return context, rt
end

infer_program_type(context, environment, var_env, p::SetConst)::Tuple{Context,Tp} = instantiate(p.t, context)

using DataStructures

function closed_inference(p)
    var_env = OrderedDict()
    (context, rt) = infer_program_type(empty_context, [], var_env, p)
    if !isempty(var_env)
        vars_dict = OrderedDict{Union{String,UInt64},Tp}()
        for (k, v) in var_env
            _, t = apply_context(context, v)
            vars_dict[k] = t
        end
        return TypeNamedArgsConstructor(ARROW, vars_dict, rt)
    else
        return rt
    end
end

using ParserCombinator

parse_token = p"([a-zA-Z0-9_\-+*/'.<>|@?])+"

parse_whitespace = Drop(Star(Space()))

parse_number = p"([0-9])+" > (s -> parse(Int64, s))

parse_var_name = (E"v" + p"([0-9])+" > (s -> parse(UInt64, s))) | (p"([a-zA-Z][a-zA-Z0-9]*)" > (s -> string(s)))

using AutoHashEquals
@auto_hash_equals mutable struct MatchPrimitive <: Delegate
    name::Symbol
    matcher::Matcher

    MatchPrimitive(matcher) = new(:MatchPrimitive, matcher)
end

@auto_hash_equals struct MatchPrimitiveState <: DelegateState
    state::State
end

function ParserCombinator.success(k::Config, m::MatchPrimitive, s, t, i, r::Value)
    try
        result = lookup_primitive(r[1])
        Success(MatchPrimitiveState(t), i, Any[result])
    catch e
        if isa(e, InterruptException)
            rethrow()
        end
        # @error "Error finding type of primitive $(r[1])"
        FAILURE
    end
end
parse_primitive = MatchPrimitive(parse_token)

parse_variable = P"\$" + parse_number > Index

parse_free_variable = P"\$" + parse_var_name > (v -> FreeVar(t0, t0, v, nothing))

parse_fixed_real = P"real" + parse_token > (v -> Primitive(treal, "real", parse(Float64, v)))

_parse_program = Delayed()

struct UnboundVariable <: Exception end

parse_invented =
    P"#" + _parse_program > (p -> begin
        t = try
            closed_inference(p)
        catch e
            if isa(e, ErrorException) || isa(e, UnboundVariable)
                bt = catch_backtrace()
                @warn "WARNING: Could not type check invented $p" exception = (e, bt)
                t0
            else
                rethrow()
            end
        end

        Invented(t, p)
    end)

parse_abstraction = P"\(lambda " + parse_whitespace + _parse_program + P"\)" > Abstraction

parse_application = P"\(" + Repeat(_parse_program + parse_whitespace, 2, ALL) + P"\)" |> (xs -> foldl(Apply, xs))

parse_let_clause =
    P"let " + P"\$v" + parse_number + P" = " + _parse_program + P" in" + parse_whitespace + _parse_program |>
    (v -> LetClause(UInt64(v[1]), v[2], v[3]))

parse_var_name_list = (E"$"+parse_var_name+E", ")[0:end] + E"$" + parse_var_name |> (vs -> [v for v in vs])

parse_let_rev_clause =
    P"let " +
    parse_var_name_list +
    P" = rev\(\$" +
    parse_var_name +
    P" = " +
    _parse_program +
    P"\) in" +
    parse_whitespace +
    _parse_program |> (v -> LetRevClause(v[1], v[2], v[3], v[4]))

julia_type_def = Delayed()
julia_type_def.matcher =
    parse_token | (parse_token + e"{" + (julia_type_def+e","+parse_whitespace)[0:end] + julia_type_def + e"}")

parse_object = Delayed()
parse_object.matcher =
    parse_token |
    (parse_token + Opt(e"{" + julia_type_def + e"}") + e"(" + (parse_object+e", ")[0:end] + parse_object + e")") |
    (parse_token + Opt(e"{" + julia_type_def + e"}") + e"()") |
    (e"[" + (parse_object+e", ")[0:end] + parse_object + e"]") |
    (e"[" + (parse_object+Opt(e";")+e" ")[0:end] + parse_object + e"]") |
    (e"[]") |
    (e"(" + (parse_object+e", ")[0:end] + parse_object + e")") |
    (parse_token + Opt(e"{" + julia_type_def + e"}") + e"[" + (parse_object+e", ")[0:end] + parse_object + e"]") |
    (parse_token + Opt(e"{" + julia_type_def + e"}") + e"[]") |> (vs -> eval(Meta.parse(join(vs, ""))))

parse_const_clause = P"Const\(" + type_parser + P", " + parse_object + P"\)" |> (v -> SetConst(v[1], v[2]))

parse_hole = P"\?\?\(" + type_parser + P"\)" > (t -> Hole(t, t, [], nothing, nothing))

_parse_program.matcher =
    parse_application |
    parse_variable |
    parse_invented |
    parse_abstraction |
    parse_primitive |
    parse_fixed_real |
    parse_free_variable |
    parse_let_clause |
    parse_let_rev_clause |
    parse_const_clause |
    parse_hole

function parse_program(s)
    parse_one(s, _parse_program)[1]
end

number_of_free_parameters(p::Invented) = number_of_free_parameters(p.b)
number_of_free_parameters(p::Abstraction) = number_of_free_parameters(p.b)
number_of_free_parameters(p::Apply) = number_of_free_parameters(p.f) + number_of_free_parameters(p.x)
number_of_free_parameters(p::FreeVar) = 1

const free_param_keys = Set(["REAL", "STRING", "r_const"])

number_of_free_parameters(p::Primitive) =
    if in(p.name, free_param_keys)
        1
    else
        0
    end
number_of_free_parameters(::Index) = 0
number_of_free_parameters(::SetConst) = 0

application_function(p::Apply) = application_function(p.f)
application_function(p::Program) = p

application_parse(p) = _application_parse(p, Program[])

function _application_parse(p::Apply, arguments)
    push!(arguments, p.x)
    _application_parse(p.f, arguments)
end
_application_parse(p::Program, args) = (p, reverse(args))

struct BoundAbstraction{B} <: Function
    p::Abstraction2{B}
    p_base::Abstraction
    arguments::Vector{Any}
    workspace::Dict{Any,Any}
end

function __run_with_arguments(p::Abstraction2{B}, environment, workspace) where {B}
    return BoundAbstraction{B}(p, p.base, environment, workspace)
end

(p::BoundAbstraction)(x) = __run_with_arguments(p.p.b, vcat(p.arguments, [x]), p.workspace)

__run_with_arguments(p::Index, environment, workspace) = environment[end-p.n]

__run_with_arguments(p::FreeVar, environment, workspace) = workspace[p.var_id]

__run_with_arguments(p::Primitive2, environment, workspace) = p.code

__run_with_arguments(p::Invented2, environment, workspace) = __run_with_arguments(p.b, environment, workspace)

function wrap_any_object_call(f)
    # Should I put this in @define_primitive macro?
    function _inner(x)
        try
            r = f(x)
            if r isa Function
                return wrap_any_object_call(r)
            else
                return _wrap_wildcard(r)
            end
        catch e
            if e isa MethodError && any(arg === any_object for arg in e.args)
                if x === any_object
                    return PatternWrapper(any_object)
                else
                    error("MethodError with any_object")
                end
            else
                rethrow()
            end
        end
    end
    return _inner
end

function __run_with_arguments(
    p::Apply2{Apply2{Apply2{Primitive2{Val{:if}},X2},X3},X},
    environment,
    workspace,
) where {X2,X3,X}
    branch = __run_with_arguments(p.f.f.x, environment, workspace)
    if branch
        __run_with_arguments(p.f.x, environment, workspace)
    else
        __run_with_arguments(p.x, environment, workspace)
    end
end

function __run_with_arguments(p::Apply2{F,X}, environment, workspace) where {F,X}
    f = __run_with_arguments(p.f, environment, workspace)
    x = __run_with_arguments(p.x, environment, workspace)
    _fun_call_wrapper(f, x)
end

function _fun_call_wrapper(f, x::Nothing)
    error("Parameter is nothing")
end

function _fun_call_wrapper(f, x::PatternWrapper)
    wrap_any_object_call(f)(x.value)
end

function _fun_call_wrapper(f, x)
    try
        f(x)
    catch e
        if e isa MethodError && any(arg === any_object for arg in e.args)
            error("MethodError with any_object")
        end
        rethrow()
    end
end

__run_with_arguments(p::SetConst2, environment, workspace) = p.value

function __run_with_arguments(p::LetClause, environment, workspace)
    v = __run_with_arguments(_build_typed_expression(p.v), environment, workspace)
    workspace[p.var_id] = v
    b = __run_with_arguments(_build_typed_expression(p.b), environment, workspace)
    delete!(workspace, p.var_id)
    return b
end

function __run_with_arguments(p::LetRevClause, environment, workspace)
    vals = run_in_reverse(p.v, workspace[p.inp_var_id], rand(UInt64))
    for (k, v) in vals
        if isa(v, EitherOptions) || isa(v, AbductibleValue)
            @error p.v
            @error workspace[p.inp_var_id]
            error("LetRevClause $p cannot return wildcard $k $v")
        end
        workspace[k] = v
    end
    b = __run_with_arguments(_build_typed_expression(p.b), environment, workspace)
    for var_id in p.var_ids
        delete!(workspace, var_id)
    end
    return b
end

ex_typed_cache = Dict{Program,Any}()

function _build_typed_expression(p::Abstraction)
    if !haskey(ex_typed_cache, p)
        ex_typed_cache[p] = Abstraction2(_build_typed_expression(p.b), p)
    end
    return ex_typed_cache[p]
end

function _build_typed_expression(p::Apply)
    if !haskey(ex_typed_cache, p)
        ex_typed_cache[p] = Apply2(_build_typed_expression(p.f), _build_typed_expression(p.x))
    end
    return ex_typed_cache[p]
end

function _build_typed_expression(p::Primitive)
    if !haskey(ex_typed_cache, p)
        ex_typed_cache[p] = Primitive2(p.t, p.name, p.code)
    end
    return ex_typed_cache[p]
end

function _build_typed_expression(p::Invented)
    if !haskey(ex_typed_cache, p)
        ex_typed_cache[p] = Invented2(p.t, _build_typed_expression(p.b))
    end
    return ex_typed_cache[p]
end

function _build_typed_expression(p::SetConst)
    if !haskey(ex_typed_cache, p)
        ex_typed_cache[p] = SetConst2(p.t, p.value)
    end
    return ex_typed_cache[p]
end

function _build_typed_expression(p::Program)
    return p
end

function run_with_arguments(p::Program, arguments, workspace)
    if !haskey(ex_typed_cache, p)
        ex_typed_cache[p] = _build_typed_expression(p)
    end
    # @info "Running $p $arguments $workspace"

    l = __run_with_arguments(ex_typed_cache[p], [], workspace)
    for x in arguments
        l = l(x)
    end
    return l
end
