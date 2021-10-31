

function match_with_known_field(run_context, sc::SolutionContext, unknown_key, unknown_branch)
    unknown_option = unknown_branch.values[unknown_key]
    found = false
    for (input_key, input_branch, input_option) in iter_known_vars(sc)
        if in(unknown_key, sc.previous_keys[input_key])
            continue
        end
        match = match_with_task_val(unknown_option.value, input_option.value, input_key)
        if !ismissing(match)
            (k, m, pr) = match
            new_block = ProgramBlock(
                pr,
                arrow(input_option.value.type, input_option.value.type),
                [k],
                (unknown_key, unknown_branch),
            )
            found |= add_new_block(run_context, sc, new_block, [(input_key, input_branch, input_option.value.type)])
        end
    end
    found
end

function match_with_unknown_field(run_context, sc::SolutionContext, input_key, input_branch)
    input_option = input_branch.values[input_key]
    found = false
    for (unknown_key, unknown_branch, unknown_option) in iter_unknown_vars(sc)
        if in(unknown_key, sc.previous_keys[input_key])
            continue
        end
        match = match_with_task_val(unknown_option.value, input_option.value, input_key)
        if !ismissing(match)
            (k, m, pr) = match
            new_block = ProgramBlock(
                pr,
                arrow(input_option.value.type, input_option.value.type),
                [k],
                (unknown_key, unknown_branch),
            )
            found |= add_new_block(run_context, sc, new_block, [(input_key, input_branch, input_option.value.type)])
        end
    end
    found
end

function get_matches(run_context, sc::SolutionContext)
    _get_matches(run_context, sc, Set())
end

function _get_matches(run_context, sc::SolutionContext, checked_options)
    # @info "Start matching iteration"
    # @info(sc.updated_options)
    # @info checked_options
    for (key, branch) in sc.updated_options
        if in((key, branch), checked_options)
            continue
        end
        # @info key
        # @info branch
        if !isknown(branch, key)
            matchers = [match_with_known_field]
        else
            matchers = [match_with_unknown_field]
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
end
