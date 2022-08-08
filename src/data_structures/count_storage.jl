
mutable struct CountStorage
    value::Int
    new_value::Union{Int,Nothing}
end

CountStorage() = CountStorage(0, nothing)

function Base.getindex(storage::CountStorage)
    if isnothing(storage.new_value)
        return storage.value
    end
    return storage.new_value
end

function save_changes!(storage::CountStorage)
    if !isnothing(storage.new_value)
        storage.value = storage.new_value
        drop_changes!(storage)
    end
end

function drop_changes!(storage::CountStorage)
    storage.new_value = nothing
end

function increment!(storage::CountStorage)
    if isnothing(storage.new_value)
        storage.new_value = storage.value + 1
    else
        storage.new_value += 1
    end
    storage.new_value
end

function get_new_values(storage::CountStorage)
    if isnothing(storage.new_value)
        return 1:0
    end
    return (storage.value+1):storage.new_value
end
