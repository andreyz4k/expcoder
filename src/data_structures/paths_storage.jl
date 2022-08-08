
using DataStructures

struct PathsStorage
    values::AbstractDict{Int,Vector{OrderedDict{Int,Int}}}
    new_values::AbstractDict{Int,Vector{OrderedDict{Int,Int}}}
end

PathsStorage() = PathsStorage(
    DefaultDict{Int,Vector{OrderedDict{Int,Int}}}(() -> []),
    DefaultDict{Int,Vector{OrderedDict{Int,Int}}}(() -> []),
)

function save_changes!(storage::PathsStorage)
    for (k, v) in storage.new_values
        if haskey(storage.values, k)
            append!(storage.values[k], v)
        else
            storage.values[k] = v
        end
    end
    drop_changes!(storage)
end

function drop_changes!(storage::PathsStorage)
    empty!(storage.new_values)
end

function Base.getindex(storage::PathsStorage, ind::Integer)
    if !haskey(storage.new_values, ind)
        return storage.values[ind]
    end
    if !haskey(storage.values, ind)
        return storage.new_values[ind]
    end
    return vcat(storage.values[ind], storage.new_values[ind])
end

function Base.haskey(storage::PathsStorage, key::Integer)
    return haskey(storage.values, key) || haskey(storage.new_values, key)
end

function Base.setindex!(storage::PathsStorage, value, ind::Integer)
    storage.new_values[ind] = value
end

function add_path!(storage::PathsStorage, branch_id, path)
    push!(storage.new_values[branch_id], path)
end

function get_new_paths(storage::PathsStorage, branch_id)
    return storage.new_values[branch_id]
end
