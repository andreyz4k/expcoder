

function match_with_known_field(sc::SolutionBranch, unknown_key, timeout, redis)
    unknown_value = sc[unknown_key]
    new_branches = []
    for (input_key, inp_value) in iter_known_vars(sc)
        match = match_with_task_val(unknown_value, inp_value, input_key)
        if !ismissing(match)
            (k, m, pr) = match
            new_block = ProgramBlock(pr, arrow(inp_value.type, inp_value.type), [k], unknown_key)
            new_branch = add_new_block(sc, new_block, timeout, redis)
            if !isnothing(new_branch)
                push!(new_branches, new_branch)
            end
        end
    end
    new_branches
end

function match_with_unknown_field(sc::SolutionBranch, input_key, timeout, redis)
    inp_value = sc[input_key]
    new_branches = []
    for (branch, (unknown_key, unknown_value)) in iter_unknown_vars(sc)
        match = match_with_task_val(unknown_value, inp_value, input_key)
        if !ismissing(match)
            (k, m, pr) = match
            new_block = ProgramBlock(pr, arrow(inp_value.type, inp_value.type), [k], unknown_key)
            new_branch = add_new_block(branch, new_block, timeout, redis)
            if !isnothing(new_branch)
                push!(new_branches, new_branch)
            end
        end
    end
    new_branches
end

function get_matches(sc::SolutionBranch, timeout, redis)
    # @info(sc.updated_keys)
    if is_solved(sc)
        return [sc]
    end
    for key in sc.updated_keys
        if !isknown(sc, key)
            matchers = [
                match_with_known_field
            ]
        else
            matchers = [
                match_with_unknown_field
            ]
        end
        matched_results = Set()
        for matcher in matchers
            for new_branch in matcher(sc, key, timeout, redis)
                push!(matched_results, new_branch)
            end
        end
        if !isempty(matched_results)
            return vcat([get_matches(b, timeout, redis) for b in matched_results]...)
        end
    end
    return [sc]
end
