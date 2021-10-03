
function get_matches(sc::SolutionBranch, keys)
    @info(keys)
    for key in keys
        kv = sc.unknown_vars[key]
        matched_inputs = skipmissing(match_with_task_val(kv, inp_value, k) for (k, inp_value) in sc.known_vars)

        new_branches = map(matched_inputs) do (k, m, pr)
            new_block = ProgramBlock(pr, [k], [key])
            add_new_block(sc, new_block)
        end
    end

end
