
block_to_let(block::ProgramBlock, output) = LetClause(block.output_var[1], block.p, output)
block_to_let(block::ReverseProgramBlock, output) = MultiLetClause(
    [output_var[1] for output_var in block.output_vars],
    block.p,
    [b.p for b in block.reverse_blocks],
    output,
)

function extract_solution(sc::SolutionContext, solution_path::OrderedDict)
    res = unique(collect(values(solution_path)))
    cost = sum(block.cost for block in values(solution_path))
    output = res[end].p
    for block in view(res, length(res)-1:-1:1)
        output = block_to_let(block, output)
    end
    # @info output
    # This is required because recognition and compression don't support let clauses
    output = beta_reduction(output)
    output = replace_inputs(output, sc.input_keys, 0)
    for _ in sc.input_keys
        output = Abstraction(output)
    end
    # @info output
    return (output, cost)
end


replace_free_var(p::Apply, key, v) = Apply(replace_free_var(p.f, key, v), replace_free_var(p.x, key, v))

replace_free_var(p::Abstraction, key, v) = Abstraction(replace_free_var(p.b, key, v))

replace_free_var(p::LetClause, key, v) =
    LetClause(p.var_name, replace_free_var(p.v, key, v), replace_free_var(p.b, key, v))

replace_free_var(p::MultiLetClause, key, v) = MultiLetClause(
    p.var_names,
    replace_free_var(p.v, key, v),
    [replace_free_var(rp, key, v) for rp in p.rev_v],
    replace_free_var(p.b, key, v),
)

replace_free_var(p::FreeVar, key, v) = p.key == key ? v : p

replace_free_var(p::Program, key, v) = p

beta_reduction(p::LetClause) = beta_reduction(replace_free_var(p.b, p.var_name, p.v))
function beta_reduction(p::MultiLetClause)
    out = p.b
    for (var_name, v) in zip(p.var_names, p.rev_v)
        out = replace_free_var(out, var_name, v)
    end
    beta_reduction(out)
end

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
