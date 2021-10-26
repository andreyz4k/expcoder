

function extract_solution(branch::SolutionContext)
    operations_map = Dict()
    for block in iter_operations(branch)
        if all(isknown(branch, key) for key in block.inputs)
            operations_map[block.output] = block
        end
    end
    needed_keys = Set([branch.target_key])
    result_ops = MultiDict{String,ProgramBlock}()
    used_ops = Set()
    while !isempty(needed_keys)
        key = pop!(needed_keys)
        if !haskey(operations_map, key)
            continue
        end
        op = operations_map[key]
        if !in(op, used_ops)
            if isempty(op.inputs)
                insert!(result_ops, "", op)
            end
            for k in op.inputs
                insert!(result_ops, k, op)
            end
            push!(used_ops, op)
            union!(needed_keys, op.inputs)
        end
    end

    result = []
    ready_to_add = Set()
    filled_keys = Set()
    for key in flatten([branch.input_keys, [""]])
        union!(ready_to_add, get(result_ops, key, []))
        push!(filled_keys, key)
    end
    while !isempty(ready_to_add)
        block = pop!(ready_to_add)
        push!(result, block)
        push!(filled_keys, block.output)
        if block.output != branch.target_key
            for op in result_ops[block.output]
                if all(in(k, filled_keys) for k in op.inputs)
                    push!(ready_to_add, op)
                end
            end
        end
    end

    output = result[end].p
    for block in view(result, length(result)-1:-1:1)
        output = LetClause(block.output, block.p, output)
    end
    # @info output
    # This is required because recognition and compression don't support let clauses
    output = beta_reduction(output)
    output = replace_inputs(output, branch.input_keys, 0)
    for _ in branch.input_keys
        output = Abstraction(output)
    end
    return output
end

replace_free_var(p::Apply, key, v) = Apply(replace_free_var(p.f, key, v), replace_free_var(p.x, key, v))

replace_free_var(p::Abstraction, key, v) = Abstraction(replace_free_var(p.b, key, v))

replace_free_var(p::LetClause, key, v) =
    LetClause(p.var_name, replace_free_var(p.v, key, v), replace_free_var(p.b, key, v))

replace_free_var(p::FreeVar, key, v) = p.key == key ? v : p

replace_free_var(p::Program, key, v) = p

beta_reduction(p::LetClause) = beta_reduction(replace_free_var(p.b, p.var_name, p.v))

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
