

function match_with_known_field(run_context, sc::SolutionContext, unknown_key, entry_hash)
    unknown_option = sc.var_data[unknown_key].options[entry_hash]
    new_branches = []
    for (input_key, input_entry_hash, input_option) in iter_known_vars(sc)
        match = match_with_task_val(unknown_option.value, input_option.value, input_key)
        if !ismissing(match)
            (k, m, pr) = match
            new_block = ProgramBlock(
                pr,
                arrow(input_option.value.type, input_option.value.type),
                [k],
                (unknown_key, entry_hash),
            )
            new_branch =
                add_new_block(run_context, sc, new_block, [(input_key, input_entry_hash, input_option.value.type)])
            if !isnothing(new_branch)
                push!(new_branches, new_branch)
            end
        end
    end
    new_branches
end

function match_with_unknown_field(run_context, sc::SolutionContext, input_key, entry_hash)
    input_option = sc.var_data[input_key].options[entry_hash]
    new_branches = []
    for (unknown_key, unknown_entry_hash, unknown_option) in iter_unknown_vars(sc)
        match = match_with_task_val(unknown_option.value, input_option.value, input_key)
        if !ismissing(match)
            (k, m, pr) = match
            new_block = ProgramBlock(
                pr,
                arrow(input_option.value.type, input_option.value.type),
                [k],
                (unknown_key, unknown_entry_hash),
            )
            new_branch =
                add_new_block(run_context, branch, new_block, [(input_key, input_entry_hash, input_option.value.type)])
            if !isnothing(new_branch)
                push!(new_branches, new_branch)
            end
        end
    end
    new_branches
end

function get_matches(run_context, sc::SolutionContext)
    @info(sc.updated_options)
    for (key, entry_hash) in sc.updated_options
        if !isknown(sc, key, entry_hash)
            matchers = [match_with_known_field]
        else
            matchers = [match_with_unknown_field]
        end
        matched_results = Set()
        for matcher in matchers
            for new_branch in matcher(run_context, sc, key, entry_hash)
                push!(matched_results, new_branch)
            end
        end
        if !isempty(matched_results)
            return vcat([get_matches(run_context, b) for b in matched_results]...)
        end
    end
    return [sc]
end
