

struct EntriesStorage
    values::Vector{Entry}
    val_to_ind::Dict{Entry,Int}
end

EntriesStorage() = EntriesStorage(Vector{Entry}(), Dict{Entry,Int}())

function add_entry(storage::EntriesStorage, entry::Entry)::Int
    if haskey(storage.val_to_ind, entry)
        return storage.val_to_ind[entry]
    end
    push!(storage.values, entry)
    ind = length(storage.values)
    storage.val_to_ind[entry] = ind
    return ind
end

function get_entry(storage::EntriesStorage, ind::Int)::Entry
    return storage.values[ind]
end
