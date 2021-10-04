

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
    result_blocks = reverse(result)
    environment = []
    path = []
    output = Hole(t0, nothing)
    for key in reverse(branch.input_keys)
        output = modify_skeleton(output, Abstraction(Hole(t0, nothing)), path)
        push!(path, ArgTurn(t0))
        push!(environment, key)
    end
    for block in result_blocks
        vars = []
        for key in block.inputs
            for i in 0:length(environment) - 1
                if environment[length(environment) - i] == key
                    push!(vars, i)
                    break
                end
            end
        end
        op = block.p
        for v in vars
            op = Apply(op, Index(v))
        end
        if block.outputs == branch.target_keys
            template = op
        else
            template = Apply(Abstraction(Hole(t0, nothing)), op)
        end
        output = modify_skeleton(output, template, path)
        push!(path, LeftTurn())
        push!(path, ArgTurn(t0))
        append!(environment, block.outputs)
    end
    return output
end
