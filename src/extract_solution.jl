
block_to_let(block::ProgramBlock, output) = LetClause(block.output_var[1], block.p, output)
block_to_let(block::ReverseProgramBlock, output) = LetRevClause(
    [output_var[1] for output_var in block.output_vars],
    block.input_vars[1][1],
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
    return (output, cost)
end


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
        new_var_name = "v$next_index"
        replacements[p.var_name] = new_var_name
        new_b, next_index = alpha_substitution(p.b, replacements, next_index + 1)
        return LetClause(new_var_name, new_v, new_b), next_index
    end
end

function alpha_substitution(p::LetRevClause, replacements, next_index)
    new_var_names = []
    for name in p.var_names
        new_name = "v$next_index"
        replacements[name] = new_name
        push!(new_var_names, new_name)
        next_index = next_index + 1
    end
    new_v, next_index = alpha_substitution(p.v, replacements, next_index)
    new_inp_var_name = haskey(replacements, p.inp_var_name) ? replacements[p.inp_var_name] : p.inp_var_name
    new_rev_v = []
    for v in p.rev_v
        new_rv, next_index = alpha_substitution(v, replacements, next_index)
        push!(new_rev_v, new_rv)
    end
    new_b, next_index = alpha_substitution(p.b, replacements, next_index)
    return LetRevClause(new_var_names, new_inp_var_name, new_v, new_rev_v, new_b), next_index
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
