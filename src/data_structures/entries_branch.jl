
struct EntryBranchItem
    value::Entry
    incoming_blocks::Dict{ProgramBlock,Int64}
    outgoing_blocks::Vector{ProgramBlock}
    is_known::Bool
end

struct EntriesBranch
    values::Dict{String,EntryBranchItem}
    parent::Union{Nothing,EntriesBranch}
    children::Vector{EntriesBranch}
end
