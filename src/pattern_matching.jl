

function match_with_known_field(run_context, sc::SolutionContext, unknown_key, unknown_branch)
    unknown_option = unknown_branch.values[unknown_key]
    found = false
    # @info "Matching unknown $unknown_key $(hash(unknown_branch))"
    for (input_key, input_branch, input_option) in iter_known_meaningful_vars(sc)
        if keys_in_loop(sc, input_key, unknown_key) ||
           !is_branch_compatible(unknown_key, unknown_branch, [input_branch])
            continue
        end
        match = match_with_task_val(unknown_option.value, input_option.value, input_key)
        if !ismissing(match)
            (m, pr) = match
            # @info "With known $input_key $(hash(input_branch))"
            new_block = ProgramBlock(
                pr,
                arrow(input_option.value.type, input_option.value.type),
                0,
                [(input_key, input_branch)],
                (unknown_key, unknown_branch),
            )
            found |= add_new_block(run_context, sc, new_block, Dict(input_key => input_branch))
        end
    end
    found
end

function match_with_unknown_field(run_context, sc::SolutionContext, input_key, input_branch)
    input_option = input_branch.values[input_key]
    found = false
    # @info "Matching known $input_key $(hash(input_branch))"
    for (unknown_key, unknown_branch, unknown_option) in iter_unknown_vars(sc)
        if keys_in_loop(sc, input_key, unknown_key) ||
           !is_branch_compatible(unknown_key, unknown_branch, [input_branch])
            continue
        end
        match = match_with_task_val(unknown_option.value, input_option.value, input_key)
        if !ismissing(match)
            (m, pr) = match
            # @info "With unknown $unknown_key $(hash(unknown_branch))"
            new_block = ProgramBlock(
                pr,
                arrow(input_option.value.type, input_option.value.type),
                0,
                [(input_key, input_branch)],
                (unknown_key, unknown_branch),
            )
            found |= add_new_block(run_context, sc, new_block, Dict(input_key => input_branch))
        end
    end
    found
end

function get_matches(run_context, sc::SolutionContext)
    _get_matches(run_context, sc, Set())
end

function _get_matches(run_context, sc::SolutionContext, checked_options)
    # @info "Start matching iteration"
    # @info [(ke[1], "$(hash(ke[2]))") for ke in sc.updated_options]
    # @info [(ke[1], "$(hash(ke[2]))") for ke in checked_options]
    for (key, branch) in sc.updated_options
        if in((key, branch), checked_options)
            continue
        end
        # @info key
        # @info branch
        if !isknown(branch, key)
            matchers = [match_with_known_field]
        elseif branch.values[key].is_meaningful
            matchers = [match_with_unknown_field]
        else
            matchers = []
        end
        found = false
        for matcher in matchers
            found |= matcher(run_context, sc, key, branch)
        end
        if found
            _get_matches(run_context, sc, union(checked_options, [(key, branch)]))
            break
        end
    end
    # @info "End matching iteration"
end
