

function extract_solution(branch::SolutionBranch)
    operations_map = Dict()
    for block in iter_operations(branch)
        if all(isknown(branch, key) for key in block.inputs)
            for key in block.outputs
                operations_map[key] = block
            end
        end
    end
    needed_keys = Set(branch.target_keys)
    result = []
    used_ops = Set()
    while !isempty(needed_keys)
        key = pop!(needed_keys)
        if !haskey(operations_map, key)
            continue
        end
        op = operations_map[key]
        if !in(op, used_ops)
            push!(result, operations_map[key])
            push!(used_ops, op)
            union!(needed_keys, op.inputs)
        end
    end

    output = result[1].p
    for block in view(result, 2:length(result))
        output = LetClause(block.outputs[1], block.p, output)
    end
    @info output
    return output
end
