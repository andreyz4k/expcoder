

function match_with_known_field(sc::SolutionBranch, key)
    kv = sc[key]
    new_branches = []
    for (k, inp_value) in iter_known_vars(sc)
        match = match_with_task_val(kv, inp_value, k)
        if !ismissing(match)
            (k, m, pr) = match
            new_block = ProgramBlock(pr, arrow(inp_value.type, inp_value.type), [k], key)
            new_branch = add_new_block(sc, new_block)
            if !isnothing(new_branch)
                push!(new_branches, new_branch)
            end
        end
    end
    new_branches
end

function get_matches(sc::SolutionBranch)
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
            matchers = []
        end
        matched_results = Set()
        for matcher in matchers
            for new_branch in matcher(sc, key)
                push!(matched_results, new_branch)
            end
        end
        if !isempty(matched_results)
            return vcat([get_matches(b) for b in matched_results]...)
        end
    end
    return [sc]
end
