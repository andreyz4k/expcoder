
function reverse_rows_to_grid(block_id, value)::Vector{Any}
    [[value[i, :] for i in (1:size(value, 1))]]
end

@define_reverse_primitive(
    "rows_to_grid",
    arrow(tlist(tlist(t0)), tgrid(t0)),
    (
        rs ->
            isempty(rs) ? Array{Any}(undef, 0, 0) :
            (
                any(!isa(r, Array) for r in rs) ? error("Only arrays are allowed as rows") :
                vcat([permutedims(r) for r in rs]...)
            )
    ),
    reverse_rows_to_grid
)

function reverse_columns_to_grid(block_id, value)::Vector{Any}
    [[value[:, i] for i in (1:size(value, 2))]]
end

@define_reverse_primitive(
    "columns_to_grid",
    arrow(tlist(tlist(t0)), tgrid(t0)),
    (cs -> isempty(cs) ? Array{Any}(undef, 0, 0) : hcat(cs...)),
    reverse_columns_to_grid
)

function reverse_rows(block_id, value)::Vector{Any}
    if isempty(value)
        return [Array{Any}(undef, 0, 0)]
    end
    [vcat([permutedims(r) for r in value]...)]
end

function reverse_columns(block_id, value)::Vector{Any}
    if isempty(value)
        return [Array{Any}(undef, 0, 0)]
    end
    [hcat(value...)]
end

@define_reverse_primitive(
    "rows",
    arrow(tgrid(t0), tlist(tlist(t0))),
    (g -> [g[i, :] for i in (1:size(g, 1))]),
    reverse_rows
)

@define_reverse_primitive(
    "columns",
    arrow(tgrid(t0), tlist(tlist(t0))),
    (g -> [g[:, i] for i in (1:size(g, 2))]),
    reverse_columns
)
