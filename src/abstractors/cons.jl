
function reverse_cons(block_id, value)::Vector{Any}
    if isempty(value)
        error("List is empty")
    end
    return [value[1], value[2:end]]
end

@define_reverse_primitive "cons" arrow(t0, tlist(t0), tlist(t0)) (x -> (y -> vcat([x], y))) reverse_cons
