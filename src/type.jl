
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

arrow(arguments...) =
    if length(arguments) == 1
        return arguments[1]
    else
        return TypeConstructor(ARROW, [arguments[1], arrow(arguments[2:end]...)])
    end

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
