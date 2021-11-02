

function extract_solutions(sc::SolutionContext, target_paths)
    result = []
    for last_op in keys(target_paths)
        for ops_set in _extract_valid_ops_set(sc, last_op.output_var..., target_paths)
            # @info ops_set
            cost = sum(block.cost for block in ops_set)
            result_ops = MultiDict{String,ProgramBlock}()
            for op in ops_set
                if isempty(op.input_vars)
                    insert!(result_ops, "", op)
                end
                for kb in op.input_vars
                    insert!(result_ops, kb[1], op)
                end
            end

            res = []
            ready_to_add = Set()
            filled_keys = Set()
            for key in flatten([sc.input_keys, [""]])
                union!(ready_to_add, get(result_ops, key, []))
                push!(filled_keys, key)
            end
            while !isempty(ready_to_add)
                block = pop!(ready_to_add)
                push!(res, block)
                push!(filled_keys, block.output_var[1])
                if block.output_var[1] != sc.target_key
                    for op in result_ops[block.output_var[1]]
                        if all(in(k, filled_keys) for (k, _) in op.input_vars)
                            push!(ready_to_add, op)
                        end
                    end
                end
            end

            output = res[end].p
            for block in view(res, length(res)-1:-1:1)
                output = LetClause(block.output_var[1], block.p, output)
            end
            # @info output
            # This is required because recognition and compression don't support let clauses
            output = beta_reduction(output)
            output = replace_inputs(output, sc.input_keys, 0)
            for _ in sc.input_keys
                output = Abstraction(output)
            end
            push!(result, (output, cost))
        end
    end
    result
end

function _extract_valid_ops_set(sc::SolutionContext, out_key, out_branch, target_paths)
    result = []
    # @info out_branch.values[out_key].incoming_blocks
    if isempty(out_branch.values[out_key].incoming_blocks)
        return [Set()]
    end
    for block in keys(out_branch.values[out_key].incoming_blocks)
        if out_key == sc.target_key && !haskey(target_paths, block)
            continue
        end
        if any(!isknown(br, k) for (k, br) in block.input_vars)
            continue
        end
        paths = [Set([block])]
        for (inp_key, inp_branch) in block.input_vars
            input_paths = _extract_valid_ops_set(sc, inp_key, inp_branch, target_paths)
            paths = [union(path, input_path) for path in paths for input_path in input_paths]
        end
        append!(result, paths)
    end
    result
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
