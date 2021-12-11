
block_to_let(block::ProgramBlock, output) = LetClause(block.output_var[1], block.p, output)
block_to_let(block::ReverseProgramBlock, output) = MultiLetClause(
    [output_var[1] for output_var in block.output_vars],
    [input_var[1] for input_var in block.input_vars],
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
    # Renaming variables for comparison between programs and remove variables copying
    output = alpha_substitution(output, Dict(), 1)[1]
    # @info output
    # output = beta_reduction(output)
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
    [k == key ? v.key : k for k in p.inp_var_names],
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


function alpha_substitution(p::LetClause, replacements, next_index)
    if isa(p.v, FreeVar)
        if haskey(replacements, p.v.key)
            replacements[p.var_name] = replacements[p.v.key]
        else
            replacements[p.var_name] = p.v.key
        end
        return alpha_substitution(p.b, replacements, next_index)
    elseif isa(p.b, FreeVar) && p.b.key == p.var_name
        return alpha_substitution(p.v, replacements, next_index)
    else
        new_v, next_index = alpha_substitution(p.v, replacements, next_index)
        new_var_name = "\$v$next_index"
        replacements[p.var_name] = new_var_name
        new_b, next_index = alpha_substitution(p.b, replacements, next_index + 1)
        return LetClause(new_var_name, new_v, new_b), next_index
    end
end

function alpha_substitution(p::MultiLetClause, replacements, next_index)
    new_v, next_index = alpha_substitution(p.v, replacements, next_index)
    new_inp_var_names = [haskey(replacements, k) ? replacements[k] : k for k in p.inp_var_names]
    new_rev_v = []
    for v in p.rev_v
        new_rv, next_index = alpha_substitution(v, replacements, next_index)
        push!(new_rev_v, new_rv)
    end
    new_var_names = []
    for name in p.var_names
        new_name = "\$v$next_index"
        replacements[name] = new_name
        push!(new_var_names, new_name)
        next_index = next_index + 1
    end
    new_b, next_index = alpha_substitution(p.b, replacements, next_index)
    return MultiLetClause(new_var_names, new_inp_var_names, new_v, new_rev_v, new_b), next_index
end

function alpha_substitution(p::FreeVar, replacements, next_index)
    if haskey(replacements, p.key)
        return FreeVar(p.t, replacements[p.key]), next_index
    else
        return p, next_index
    end
end

function alpha_substitution(p::Abstraction, replacements, next_index)
    new_b, next_index = alpha_substitution(p.b, replacements, next_index)
    Abstraction(new_b), next_index
end

function alpha_substitution(p::Apply, replacements, next_index)
    new_f, next_index = alpha_substitution(p.f, replacements, next_index)
    new_x, next_index = alpha_substitution(p.x, replacements, next_index)
    return Apply(new_f, new_x), next_index
end

alpha_substitution(p::Program, replacements, next_index) = p, next_index

function check_var_name(name, keys, depth)
    for (i, key) in enumerate(keys)
        if name == key
            return length(keys) - i + depth
        end
    end
    return -1
end

function replace_inputs(p::FreeVar, keys, depth)
    input_index = check_var_name(p.key, keys, depth)
    if input_index != -1
        return Index(input_index)
    else
        return p
    end
end

function replace_inputs_in_var_names(names, keys, depth)
    res = []
    for name in names
        input_index = check_var_name(name, keys, depth)
        if input_index != -1
            push!(res, "\$$input_index")
        else
            push!(res, name)
        end
    end
    return res
end

replace_inputs(p::Abstraction, keys, depth) = Abstraction(replace_inputs(p.b, keys, depth + 1))
replace_inputs(p::Apply, keys, depth) = Apply(replace_inputs(p.f, keys, depth), replace_inputs(p.x, keys, depth))
replace_inputs(p::Program, keys, depth) = p
replace_inputs(p::LetClause, keys, depth) =
    LetClause(p.var_name, replace_inputs(p.v, keys, depth), replace_inputs(p.b, keys, depth))
replace_inputs(p::MultiLetClause, keys, depth) = MultiLetClause(
    p.var_names,
    replace_inputs_in_var_names(p.inp_var_names, keys, depth),
    p.v,
    [replace_inputs(rp, keys, depth) for rp in p.rev_v],
    replace_inputs(p.b, keys, depth),
)
