
block_to_let(block::ProgramBlock, output) = LetClause(block.output_var, block.p, output)
block_to_let(block::ReverseProgramBlock, output) = LetRevClause(block.output_vars, block.input_vars[1], block.p, output)

function extract_solution(sc::SolutionContext, solution_path::Path)
    res = [(bl_id, sc.blocks[bl_id]) for bl_id in extract_block_sequence(solution_path)]

    root_block_branches = [sc.block_root_branches[block_id] for (block_id, block) in res if !isa(block.p, FreeVar)]
    root_block_entries = Dict(
        first(get_connected_from(sc.branch_vars, branch_id)) => sc.entries[sc.branch_entries[branch_id]] for
        branch_id in root_block_branches
    )

    cost = sum(block.cost for (_, block) in res)
    output = res[end][2].p
    for (_, block) in view(res, length(res)-1:-1:1)
        output = block_to_let(block, output)
    end
    # @info output
    # Renaming variables for comparison between programs and remove variables copying
    replacements = Dict{UInt64,Any}()
    base_output = output
    output = alpha_substitution(output, replacements, Set{UInt64}(), Set{UInt64}(), UInt64(1), sc.input_keys)[1]
    output_var_id = first(get_connected_from(sc.branch_vars, sc.target_branch_id))
    trace_values = Dict()
    for (var_id, entry) in root_block_entries
        tp = sc.types[entry.type_id]
        if var_id == output_var_id
            trace_values["output"] = (tp, entry.values)
        elseif haskey(sc.input_keys, var_id)
            trace_values[sc.input_keys[var_id]] = (tp, entry.values)
        elseif haskey(replacements, var_id)
            trace_values[replacements[var_id]] = (tp, entry.values)
        else
            @info var_id
            @info entry
            @info replacements
            @info sc.input_keys
            @info res
            @info root_block_entries
            @info base_output
            @info output
            trace_values[replacements[var_id]] = entry.values
        end
    end
    if !haskey(trace_values, "output")
        entry = sc.entries[sc.branch_entries[sc.target_branch_id]]
        trace_values["output"] = (sc.types[entry.type_id], entry.values)
    end
    for (var_id, name) in sc.input_keys
        if !haskey(trace_values, name)
            # Using var id as branch id because they are the same for input variables
            entry = sc.entries[sc.branch_entries[var_id]]
            trace_values[name] = (sc.types[entry.type_id], entry.values)
        end
    end

    # @info output
    return (output, cost, trace_values)
end

function has_var(p::LetClause, var_id::UInt64)
    return has_var(p.v, var_id) || has_var(p.b, var_id)
end

function has_var(p::LetRevClause, var_id::UInt64)
    return has_var(p.b, var_id)
end

function has_var(p::FreeVar, var_id::UInt64)
    return p.var_id == var_id
end

function has_var(p::Abstraction, var_id::UInt64)
    return has_var(p.b, var_id)
end

function has_var(p::Apply, var_id::UInt64)
    return has_var(p.f, var_id) || has_var(p.x, var_id)
end

function has_var(p::Program, var_id::UInt64)
    return false
end

function alpha_substitution(p::LetClause, replacements, let_vars, used_vars, next_index::UInt64, input_keys)
    if isa(p.v, FreeVar)
        if haskey(input_keys, p.v.var_id)
            replacements[p.var_id] = input_keys[p.v.var_id]
        elseif length([v for (v, r) in replacements if r == replacements[p.v.var_id]]) > 1 || (in(p.v.var_id, let_vars) && (has_var(p.b, p.v.var_id) || in(p.v.var_id, used_vars)))
            new_v, next_index = alpha_substitution(p.v, replacements, let_vars, Set{UInt64}(), next_index, input_keys)
            replacements[p.var_id] = next_index
            new_b, next_index2 = alpha_substitution(p.b, replacements, let_vars, used_vars, next_index + 1, input_keys)
            return LetClause(next_index, new_v, new_b), next_index2
        elseif haskey(replacements, p.v.var_id)
            replacements[p.var_id] = replacements[p.v.var_id]
        else
            replacements[p.var_id] = p.v.var_id
        end
        return alpha_substitution(p.b, replacements, let_vars, used_vars, next_index, input_keys)
    elseif isa(p.b, FreeVar) && p.b.var_id == p.var_id
        replacements[p.var_id] = "output"
        return alpha_substitution(p.v, replacements, let_vars, used_vars, next_index, input_keys)
    else
        new_v, next_index = alpha_substitution(p.v, replacements, let_vars, used_vars, next_index, input_keys)
        replacements[p.var_id] = next_index
        push!(let_vars, p.var_id)
        new_b, next_index2 = alpha_substitution(p.b, replacements, let_vars, used_vars, next_index + 1, input_keys)
        return LetClause(next_index, new_v, new_b), next_index2
    end
end

function alpha_substitution(p::LetRevClause, replacements, let_vars, used_vars, next_index::UInt64, input_keys)
    new_var_ids = UInt64[]
    for var_id in p.var_ids
        replacements[var_id] = next_index
        push!(new_var_ids, next_index)
        next_index += 1
    end
    new_v, next_index = alpha_substitution(p.v, replacements, let_vars, Set{UInt64}(), next_index, input_keys)
    if haskey(input_keys, p.inp_var_id)
        new_inp_var_id = input_keys[p.inp_var_id]
    elseif haskey(replacements, p.inp_var_id)
        new_inp_var_id = replacements[p.inp_var_id]
    else
        new_inp_var_id = p.inp_var_id
    end
    new_b, next_index = alpha_substitution(p.b, replacements, let_vars, used_vars, next_index, input_keys)
    return LetRevClause(new_var_ids, new_inp_var_id, new_v, new_b), next_index
end

function alpha_substitution(p::FreeVar, replacements, let_vars, used_vars, next_index::UInt64, input_keys)
    push!(used_vars, p.var_id)
    if haskey(input_keys, p.var_id)
        return FreeVar(p.t, input_keys[p.var_id], p.location), next_index
    elseif haskey(replacements, p.var_id)
        return FreeVar(p.t, replacements[p.var_id], p.location), next_index
    else
        return p, next_index
    end
end

function alpha_substitution(p::Abstraction, replacements, let_vars, used_vars, next_index::UInt64, input_keys)
    new_b, next_index = alpha_substitution(p.b, replacements, let_vars, used_vars, next_index, input_keys)
    Abstraction(new_b), next_index
end

function alpha_substitution(p::Apply, replacements, let_vars, used_vars, next_index::UInt64, input_keys)
    new_f, next_index = alpha_substitution(p.f, replacements, let_vars, used_vars, next_index, input_keys)
    new_x, next_index = alpha_substitution(p.x, replacements, let_vars, used_vars, next_index, input_keys)
    return Apply(new_f, new_x), next_index
end

alpha_substitution(p::Program, replacements, let_vars, used_vars, next_index::UInt64, input_keys) = p, next_index
