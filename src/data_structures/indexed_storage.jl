
struct IndexedStorage{T}
    values::Vector{T}
    val_to_ind::Dict{T,Int}
    new_values::Vector{T}
    new_val_to_ind::Dict{T,Int}
end

IndexedStorage{T}() where {T} = IndexedStorage{T}(Vector{T}(), Dict{T,Int}(), Vector{T}(), Dict{T,Int}())

function Base.push!(storage::IndexedStorage{T}, value::T)::Int where {T}
    if haskey(storage.new_val_to_ind, value)
        return storage.new_val_to_ind[value]
    end
    if haskey(storage.val_to_ind, value)
        return storage.val_to_ind[value]
    end
    push!(storage.new_values, value)
    ind = length(storage.values) + length(storage.new_values)
    storage.new_val_to_ind[value] = ind
    return ind
end

function Base.getindex(storage::IndexedStorage, ind::Integer)
    if ind <= length(storage.values)
        return storage.values[ind]
    end
    return storage.new_values[ind-length(storage.values)]
end

function Base.length(storage::IndexedStorage)
    return length(storage.values) + length(storage.new_values)
end

function get_index(storage::IndexedStorage, value)::Int
    if haskey(storage.new_val_to_ind, value)
        return storage.new_val_to_ind[value]
    end
    if haskey(storage.val_to_ind, value)
        return storage.val_to_ind[value]
    end
    throw(KeyError(value))
end

function save_changes!(storage::IndexedStorage)
    append!(storage.values, storage.new_values)
    merge!(storage.val_to_ind, storage.new_val_to_ind)
    drop_changes!(storage)
end

function drop_changes!(storage::IndexedStorage)
    empty!(storage.new_values)
    empty!(storage.new_val_to_ind)
end

function get_new_values(storage::IndexedStorage)
    return (length(storage.values)+1):(length(storage.values)+length(storage.new_values))
end
