
abstract type Tp end

struct TypeVariable <: Tp
    id::Int64
end


struct TypeConstructor <: Tp
    name::String
    arguments::Vector{Tp}
    is_poly::Bool
end

is_polymorphic(::TypeVariable) = true
is_polymorphic(tc::TypeConstructor) = tc.is_poly

TypeConstructor(name, arguments) = TypeConstructor(name, arguments, any(is_polymorphic(a) for a in arguments))

ARROW = "->"

Base.:(==)(a::TypeVariable, b::TypeVariable) = a.id == b.id
Base.:(==)(a::TypeConstructor, b::TypeConstructor) = a.name == b.name && a.arguments == b.arguments

Base.show(io::IO, t::Tp) = print(io, show_type(t, true)...)

show_type(t::TypeVariable, is_return::Bool) = ["t", t.id]
function show_type(t::TypeConstructor, is_return::Bool)
    if isempty(t.arguments)
        [t.name]
    elseif t.name == ARROW
        if is_return
            vcat(show_type(t.arguments[1], false), [" -> "], show_type(t.arguments[2], true))
        else
            vcat(["("], show_type(t.arguments[1], false), [" -> "], show_type(t.arguments[2], true), [")"])
        end
    else
        vcat([t.name, "("], vcat([vcat(show_type(a, true), [", "]) for a in t.arguments]...)[1:end - 1], [")"])
    end
end

struct Context
    next_variable::Int64
    substitution::Dict{Int64,Tp}
end

empty_context = Context(0, Dict())



arrow(arguments...) =
    if length(arguments) == 1
        return arguments[1]
    else
        return TypeConstructor(ARROW, [arguments[1], arrow(arguments[2:end]...)])
    end

isarrow(t::TypeConstructor) = t.name == ARROW
isarrow(::TypeVariable) = false

t0 = TypeVariable(0)
t1 = TypeVariable(1)
t2 = TypeVariable(2)


tlist(t) = TypeConstructor("list", [t])

baseType(n) = TypeConstructor(n, [])

tint = baseType("int")
treal = baseType("real")
tbool = baseType("bool")
tboolean = tbool  # alias
tcharacter = baseType("char")


function instantiate(t::TypeVariable, context, bindings = nothing)
    if isnothing(bindings)
        bindings = Dict()
    end
    if haskey(bindings, t.id)
        return (context, bindings[t.id])
    end
    new = TypeVariable(context.next_variable)
    bindings[t.id] = new
    context = Context(context.next_variable + 1, context.substitution)
    return (context, new)
end

function instantiate(t::TypeConstructor, context, bindings = nothing)
    if !t.is_poly
        return context, t
    end
    if isnothing(bindings)
        bindings = Dict()
    end
    new_arguments = []
    for x in t.arguments
        (context, x) = instantiate(x, context, bindings)
        push!(new_arguments, x)
    end
    return (context, TypeConstructor(t.name, new_arguments))
end

arguments_of_type(t::TypeConstructor) =
    if t.name == ARROW
        return vcat([t.arguments[1]], arguments_of_type(t.arguments[2]))
    else
        return []
    end

arguments_of_type(::TypeVariable) = []

return_of_type(t::TypeConstructor) =
    if t.name == ARROW
        return_of_type(t.arguments[2])
    else
        t
    end

return_of_type(t::TypeVariable) = t

occurs(i::Int64, t::TypeVariable) = t.id == i
occurs(i::Int64, t::TypeConstructor) =
    if !is_polymorphic(t)
        false
    else
        any(occurs(i, ta) for ta in t.arguments)
    end

struct UnificationFailure <: Exception end

_unify(context, t1::TypeVariable, t2) =
    if t1 == t2
        context
    elseif occurs(t1.id, t2)
        throw(UnificationFailure())
    else
        bindTID(t1.id, t2, context)
    end

_unify(context, t1, t2::TypeVariable) =
    if t1 == t2
        context
    elseif occurs(t2.id, t1)
        throw(UnificationFailure())
    else
        bindTID(t2.id, t1, context)
    end

_unify(context, t1::TypeVariable, t2::TypeVariable) = invoke(_unify, Tuple{Any,TypeVariable,Any}, context, t1, t2)

_unify(context, t1::TypeConstructor, t2::TypeConstructor) =
    if t1.name == t2.name
        for (x1, x2) in zip(t1.arguments, t2.arguments)
            context = unify(context, x1, x2)
        end
        context
    else
        throw(UnificationFailure())
    end

function unify(context, t1, t2)
    (context, t1) = apply_context(context, t1)
    (context, t2) = apply_context(context, t2)
    if (!is_polymorphic(t1)) && (!is_polymorphic(t2))
        if t1 == t2
            context
        else
            throw(UnificationFailure())
        end
    else
        _unify(context, t1, t2)
    end
end

might_unify(t1::TypeVariable, t2) = true
might_unify(t1, t2::TypeVariable) = true
might_unify(t1::TypeVariable, t2::TypeVariable) = true
might_unify(t1::TypeConstructor, t2::TypeConstructor) =
    t1.name == t2.name &&
    length(t1.arguments) == length(t2.arguments) &&
    all(might_unify(as1, as2) for (as1, as2) in zip(t1.arguments, t2.arguments))

function lookupTID(context::Context, j)
    @assert (j < context.next_variable)
    get(context.substitution, j, nothing)
end

function bindTID(i, t, context)
    new_substitutions = copy(context.substitution)
    new_substitutions[i] = t
    Context(context.next_variable, new_substitutions)
end

function apply_context(context, t::TypeVariable)
    tp = lookupTID(context, t.id)
    if isnothing(tp)
        (context, t)
    else
        (context, tp2) = apply_context(context, tp)
        context = tp == tp2 ? context : bindTID(t.id, tp2, context)
        (context, tp2)
    end
end

function apply_context(context, t::TypeConstructor)
    if !is_polymorphic(t)
        (context, t)
    end
    new_argtypes = []
    for x in t.arguments
        context, xt = apply_context(context, x)
        push!(new_argtypes, xt)
    end
    (context, TypeConstructor(t.name, new_argtypes))
end


function deserialize_type(message)
    try
        name = message["constructor"]
        arguments = map(deserialize_type, message["arguments"])
        TypeConstructor(name, arguments)
    catch
        TypeVariable(message["index"])
    end
end
