mutable struct DenseConnectionGraphStorage
    transaction_depth::Int
    updates_stack::Dict{Int,Matrix{Int16}}
    needs_sync::Bool
    sync_id::Int
end

using LinearAlgebra

DenseConnectionGraphStorage() =
    DenseConnectionGraphStorage(0, Dict{Int,Matrix{Int16}}(0 => Matrix{Int16}(I(16))), false, 0)

function start_transaction!(storage::DenseConnectionGraphStorage, depth::Int)
    storage.transaction_depth = depth
    for d in keys(storage.updates_stack)
        if d >= depth
            delete!(storage.updates_stack, d)
        end
    end
end

function save_changes!(storage::DenseConnectionGraphStorage, depth)
    max_depth = maximum(keys(storage.updates_stack))
    if max_depth > depth
        storage.updates_stack[depth] = storage.updates_stack[max_depth]
        sync_storage!(storage, depth)
    end
    drop_changes!(storage, depth)
end

function drop_changes!(storage::DenseConnectionGraphStorage, depth)
    for d in keys(storage.updates_stack)
        if d > depth
            delete!(storage.updates_stack, d)
        end
    end
    storage.transaction_depth = depth
    storage.needs_sync = false
end

function sync_storage!(storage::DenseConnectionGraphStorage, depth::Int)
    if storage.needs_sync
        v = storage.updates_stack[depth]
        while true
            new_v = Int16.((v * v) .!= 0)
            if new_v == v
                storage.updates_stack[depth] = new_v
                break
            end
            v = new_v
        end
        storage.needs_sync = false
        storage.sync_id += 1
    end
end

function Base.getindex(storage::DenseConnectionGraphStorage, i::UInt64, j::UInt64)
    sync_storage!(storage, storage.transaction_depth)
    for k in storage.transaction_depth:-1:0
        if !haskey(storage.updates_stack, k)
            continue
        end
        m_size = size(storage.updates_stack[k])[1]
        if i > m_size || j > m_size
            return false
        end
        return storage.updates_stack[k][i, j] != 0
    end
    error("Empty updates stack")
end

function Base.setindex!(storage::DenseConnectionGraphStorage, value::Bool, i::UInt64, j::UInt64)
    if !value
        error("DenseConnectionGraphStorage does not support deleting edges")
    else
        k = storage.transaction_depth
        while k >= 0
            if haskey(storage.updates_stack, k)
                break
            end
            k -= 1
        end
        if k == -1
            error("Empty updates stack")
        end
        m_size = size(storage.updates_stack[k])[1]
        needs_resize = i > m_size || j > m_size

        if k != storage.transaction_depth
            if needs_resize
                storage.updates_stack[storage.transaction_depth] = Matrix{Int16}(I(m_size * 2))
                view(storage.updates_stack[storage.transaction_depth], 1:m_size, 1:m_size) .= storage.updates_stack[k]
            else
                storage.updates_stack[storage.transaction_depth] = copy(storage.updates_stack[k])
            end
        elseif needs_resize
            old_m = storage.updates_stack[storage.transaction_depth]
            storage.updates_stack[storage.transaction_depth] = Matrix{Int16}(I(m_size * 2))
            view(storage.updates_stack[storage.transaction_depth], 1:m_size, 1:m_size) .= old_m
        end
        storage.updates_stack[storage.transaction_depth][i, j] = 1
        storage.needs_sync = true
    end
end

function get_connected_from(storage::DenseConnectionGraphStorage, i::UInt64)
    sync_storage!(storage, storage.transaction_depth)
    for k in storage.transaction_depth:-1:0
        if !haskey(storage.updates_stack, k)
            continue
        end
        m = storage.updates_stack[k]
        res = Set{UInt64}()
        if i > size(m)[1]
            return res
        end
        for j in 1:size(m)[2]
            if m[i, j] != 0
                push!(res, j)
            end
        end
        return res
    end
    error("Empty updates stack")
end

function get_connected_to(storage::DenseConnectionGraphStorage, j::UInt64)
    sync_storage!(storage, storage.transaction_depth)
    for k in storage.transaction_depth:-1:0
        if !haskey(storage.updates_stack, k)
            continue
        end
        m = storage.updates_stack[k]
        res = Set{UInt64}()
        if j > size(m)[2]
            return res
        end
        for i in 1:size(m)[1]
            if m[i, j] != 0
                push!(res, i)
            end
        end
        return res
    end
    error("Empty updates stack")
end

mutable struct DenseProjectionConnectionGraphStorage
    transaction_depth::Int
    base_storage::DenseConnectionGraphStorage
    updates_stack::Dict{Int,Matrix{Int16}}
    reverse_base::Bool
    needs_sync::Bool
    sync_id::Int
end

DenseProjectionConnectionGraphStorage(base_storage::DenseConnectionGraphStorage, reverse_base::Bool) =
    DenseProjectionConnectionGraphStorage(
        0,
        base_storage,
        Dict{Int,Matrix{Int16}}(0 => zeros(Int16, 16, 16)),
        reverse_base,
        false,
        0,
    )

function start_transaction!(storage::DenseProjectionConnectionGraphStorage, depth::Int)
    storage.transaction_depth = depth
    for d in keys(storage.updates_stack)
        if d >= depth
            delete!(storage.updates_stack, d)
        end
    end
end

function save_changes!(storage::DenseProjectionConnectionGraphStorage, depth)
    max_depth = maximum(keys(storage.updates_stack))
    if max_depth > depth
        storage.updates_stack[depth] = storage.updates_stack[max_depth]
        sync_storage!(storage.base_storage, storage.base_storage.transaction_depth)
        sync_storage!(storage, depth, depth)
    end
    drop_changes!(storage, depth)
end

function drop_changes!(storage::DenseProjectionConnectionGraphStorage, depth)
    for d in keys(storage.updates_stack)
        if d > depth
            delete!(storage.updates_stack, d)
        end
    end
    storage.transaction_depth = depth
end

function sync_storage!(storage::DenseProjectionConnectionGraphStorage, get_depth::Int, set_depth::Int)
    if storage.needs_sync || storage.sync_id != storage.base_storage.sync_id
        for l in storage.base_storage.transaction_depth:-1:0
            if !haskey(storage.base_storage.updates_stack, l)
                continue
            end
            m_size = size(storage.updates_stack[get_depth])[1]
            b_size = size(storage.base_storage.updates_stack[l])[1]
            if m_size < b_size
                get_matrix = zeros(Int16, b_size, b_size)
                view(get_matrix, 1:m_size, 1:m_size) .= storage.updates_stack[get_depth]
                b_matrix = storage.base_storage.updates_stack[l]
            elseif m_size > b_size
                get_matrix = storage.updates_stack[get_depth]
                b_matrix = zeros(Int16, m_size, m_size)
                view(b_matrix, 1:b_size, 1:b_size) .= storage.base_storage.updates_stack[l]
            else
                get_matrix = storage.updates_stack[get_depth]
                b_matrix = storage.base_storage.updates_stack[l]
            end
            if storage.reverse_base
                storage.updates_stack[set_depth] = Int16.((permutedims(b_matrix, (2, 1)) * get_matrix) .!= 0)
            else
                storage.updates_stack[set_depth] = Int16.((b_matrix * get_matrix) .!= 0)
            end
            storage.needs_sync = false
            storage.sync_id = storage.base_storage.sync_id
            return set_depth
        end
    end
    return get_depth
end

function Base.getindex(storage::DenseProjectionConnectionGraphStorage, i::UInt64, j::UInt64)
    sync_storage!(storage.base_storage, storage.base_storage.transaction_depth)
    for k in storage.transaction_depth:-1:0
        if !haskey(storage.updates_stack, k)
            continue
        end
        depth = sync_storage!(storage, k, storage.transaction_depth)
        m_size = size(storage.updates_stack[depth])[1]
        if i > m_size || j > m_size
            return false
        end
        return storage.updates_stack[depth][i, j] != 0
    end
    error("Empty updates stack")
end

function Base.setindex!(storage::DenseProjectionConnectionGraphStorage, value::Bool, i::UInt64, j::UInt64)
    if !value
        error("DenseConnectionGraphStorage does not support deleting edges")
    else
        k = storage.transaction_depth
        while k >= 0
            if haskey(storage.updates_stack, k)
                break
            end
            k -= 1
        end
        if k == -1
            error("Empty updates stack")
        end
        m_size = size(storage.updates_stack[k])[1]
        needs_resize = i > m_size || j > m_size

        if k != storage.transaction_depth
            if needs_resize
                storage.updates_stack[storage.transaction_depth] = zeros(Int16, m_size * 2, m_size * 2)
                view(storage.updates_stack[storage.transaction_depth], 1:m_size, 1:m_size) .= storage.updates_stack[k]
            else
                storage.updates_stack[storage.transaction_depth] = copy(storage.updates_stack[k])
            end
        elseif needs_resize
            old_m = storage.updates_stack[storage.transaction_depth]
            storage.updates_stack[storage.transaction_depth] = zeros(Int16, m_size * 2, m_size * 2)
            view(storage.updates_stack[storage.transaction_depth], 1:m_size, 1:m_size) .= old_m
        end
        storage.updates_stack[storage.transaction_depth][i, j] = 1
        storage.needs_sync = true
    end
end

function get_connected_from(storage::DenseProjectionConnectionGraphStorage, i::UInt64)
    sync_storage!(storage.base_storage, storage.base_storage.transaction_depth)
    for k in storage.transaction_depth:-1:0
        if !haskey(storage.updates_stack, k)
            continue
        end
        depth = sync_storage!(storage, k, storage.transaction_depth)
        m = storage.updates_stack[depth]
        res = Set{UInt64}()
        if i > size(m)[1]
            return res
        end
        for j in 1:size(m)[2]
            if m[i, j] != 0
                push!(res, j)
            end
        end
        return res
    end
    error("Empty updates stack")
end
