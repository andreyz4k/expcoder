
abstract type Tp end

struct TID <: Tp
    id::Int64
end

struct TCon
    name::String
    arguments::Vector{Tp}
    is_polimorphic::Bool
end
