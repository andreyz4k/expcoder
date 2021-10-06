

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
    # This is required because recognition and compression don't support let clauses
    output = beta_reduction(output)
    output = replace_inputs(output, branch.input_keys, 0)
    for _ in branch.input_keys
        output = Abstraction(output)
    end
    return output
end

replace_free_var(p::Apply, key, v) =
    Apply(replace_free_var(p.f, key, v), replace_free_var(p.x, key, v))

replace_free_var(p::Abstraction, key, v) =
    Abstraction(replace_free_var(p.b, key, v))

replace_free_var(p::LetClause, key, v) =
    LetClause(p.var_name, replace_free_var(p.v, key, v), replace_free_var(p.b, key, v))

replace_free_var(p::FreeVar, key, v) = p.key == key ? v : p

replace_free_var(p::Program, key, v) = p

beta_reduction(p::LetClause) =
    beta_reduction(replace_free_var(p.b, p.var_name, p.v))

beta_reduction(p::Program) = p

function replace_inputs(p::FreeVar, keys, depth)
    for (i, key) in enumerate(keys)
        if p.key == key
            return Index(length(keys) - i + depth)
        end
    end
    error("Unknown var $(p.key)")
end

replace_inputs(p::Abstraction, keys, depth) = Abstraction(replace_inputs(p.b, keys, depth + 1))
replace_inputs(p::Apply, keys, depth) = Apply(replace_inputs(p.f, keys, depth), replace_inputs(p.x, keys, depth))
replace_inputs(p::Program, keys, depth) = p
