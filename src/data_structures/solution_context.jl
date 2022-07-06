
using DataStructures

mutable struct SolutionContext
    entries_storage::EntriesStorage
    var_data::Dict{String,EntryBranch}
    known_branches::DefaultDict{Tp,Vector{EntryBranch}}
    unknown_branches::DefaultDict{Tp,Vector{EntryBranch}}
    target_key::String
    created_vars::Int64
    input_keys::Vector{String}
    inserted_options::Set{EntryBranch}
    updated_cost_options::Set{EntryBranch}
    example_count::Int64
    previous_keys::Dict{String,Set{String}}
    following_keys::Dict{String,Set{String}}
    type_weights::Dict{String,Float64}
    total_number_of_enumerated_programs::Int64
    pq_input::PriorityQueue
    pq_output::PriorityQueue
    branch_queues::Dict{EntryBranch,PriorityQueue}
end

function create_starting_context(task::Task, type_weights)::SolutionContext
    argument_types = arguments_of_type(task.task_type)
    input_keys = []
    previous_keys = Dict{String,Set{String}}()
    following_keys = Dict{String,Set{String}}()
    example_count = length(task.train_outputs)
    target_key = "out"
    sc = SolutionContext(
        EntriesStorage(),
        Dict{String,EntryBranch}(),
        DefaultDict{Tp,Vector{EntryBranch}}(() -> []),
        DefaultDict{Tp,Vector{EntryBranch}}(() -> []),
        target_key,
        0,
        input_keys,
        Set(),
        Set(),
        example_count,
        previous_keys,
        following_keys,
        type_weights,
        0,
        PriorityQueue(),
        PriorityQueue(),
        Dict(),
    )
    for (key, t) in argument_types
        values = [inp[key] for inp in task.train_inputs]
        complexity_summary = get_complexity_summary(values, t)
        entry = ValueEntry(t, values, complexity_summary, get_complexity(sc, complexity_summary))
        entry_index = add_entry(sc.entries_storage, entry)
        sc.var_data[key] = EntryBranch(
            entry_index,
            key,
            t,
            Set(),
            Set(),
            Set(),
            [OrderedDict{String,ProgramBlock}()],
            Set(),
            Set(),
            true,
            true,
            0.0,
            entry.complexity,
            entry.complexity,
            0.0,
            entry.complexity,
            entry.complexity,
            Set(),
        )
        push!(sc.input_keys, key)
        push!(sc.known_branches[t], sc.var_data[key])
        sc.previous_keys[key] = Set([key])
        sc.following_keys[key] = Set([key])
    end
    return_type = return_of_type(task.task_type)
    complexity_summary = get_complexity_summary(task.train_outputs, return_type)
    entry = ValueEntry(return_type, task.train_outputs, complexity_summary, get_complexity(sc, complexity_summary))
    entry_index = add_entry(sc.entries_storage, entry)
    sc.var_data[target_key] = EntryBranch(
        entry_index,
        target_key,
        return_type,
        Set(),
        Set(),
        Set(),
        [],
        Set(),
        Set(),
        false,
        false,
        0.0,
        entry.complexity,
        entry.complexity,
        0.0,
        entry.complexity,
        entry.complexity,
        Set(),
    )
    push!(sc.unknown_branches[return_type], sc.var_data[target_key])
    sc.previous_keys[target_key] = Set([target_key])
    sc.following_keys[target_key] = Set([target_key])
    return sc
end

function reset_updated_keys(ctx::SolutionContext)
    ctx.inserted_options = Set()
    ctx.updated_cost_options = Set()
end

function create_next_var(solution_ctx::SolutionContext)
    solution_ctx.created_vars += 1
end

function check_insert_new_branch(sc::SolutionContext, branch::EntryBranch)
    key = branch.key
    is_new_branch = false
    if isempty(branch.parents)
        if !haskey(sc.var_data, key)
            sc.var_data[key] = branch
            sc.previous_keys[key] = Set([key])
            sc.following_keys[key] = Set([key])
            is_new_branch = true
        end
    else
        for parent in branch.parents
            if !in(branch, parent.children)
                push!(parent.children, branch)
                for child in branch.children
                    if in(child, parent.children)
                        delete!(parent.children, child)
                    end
                    if in(parent, child.parents)
                        delete!(child.parents, parent)
                    end
                    if !in(branch, child.parents)
                        push!(child.parents, branch)
                    end
                end
                is_new_branch = true
            end
        end
    end
    if is_new_branch
        if branch.is_known
            push!(sc.known_branches[branch.type], branch)
        else
            push!(sc.unknown_branches[branch.type], branch)
        end
        push!(sc.inserted_options, branch)
    end
    for constraint in branch.constraints
        if !haskey(constraint.branches, branch.key)
            constraint.branches[branch.key] = branch
        end
        for (_, br) in constraint.branches
            if !in(constraint, br.constraints)
                push!(br.constraints, constraint)
            end
        end
    end
    return is_new_branch
end

function get_input_paths_for_new_block(bl, input_branches)
    new_block_paths = [OrderedDict{String,ProgramBlock}()]
    for (in_key, _) in bl.input_vars
        inp_branch = input_branches[in_key]
        next_paths = []
        for path in new_block_paths
            for inp_path in inp_branch.incoming_paths
                bad_path = false
                for (k, b) in inp_path
                    if haskey(path, k) && path[k] != b
                        bad_path = true
                        # @warn "Paths mismatch $bl" path inp_path
                        break
                    end
                end
                if !bad_path
                    new_path = merge(path, inp_path)
                    push!(next_paths, new_path)
                end
            end
        end
        new_block_paths = next_paths
    end
    return new_block_paths
end

function get_input_paths_for_existing_block(bl, input_branches, new_paths)
    new_block_paths = []
    for l = 1:length(bl.input_vars)
        if !haskey(new_paths, input_branches[bl.input_vars[l][1]])
            continue
        end
        new_block_paths_part = [OrderedDict{String,ProgramBlock}()]
        for (i, (in_key, _)) in enumerate(bl.input_vars)
            inp_branch = input_branches[in_key]
            next_paths = []
            for path in new_block_paths_part
                if i == l
                    inp_paths = new_paths[inp_branch]
                elseif i < l && haskey(new_paths, inp_branch)
                    inp_paths = filter(p -> !in(p, new_paths[inp_branch]), inp_branch.incoming_paths)
                else
                    inp_paths = inp_branch.incoming_paths
                end
                for inp_path in inp_paths
                    bad_path = false
                    for (k, b) in inp_path
                        if haskey(path, k) && path[k] != b
                            bad_path = true
                            # @warn "Paths mismatch $bl" path inp_path
                            break
                        end
                    end
                    if !bad_path
                        new_path = merge(path, inp_path)
                        push!(next_paths, new_path)
                    end
                end
            end
            new_block_paths_part = next_paths
        end
        append!(new_block_paths, new_block_paths_part)
    end
    return new_block_paths
end

function get_new_paths_for_block(sc, bl::ProgramBlock, is_new_block, new_paths, output_branches, input_branches)
    # @info "Getting paths for existing block $bl"
    if is_new_block
        new_block_paths = get_input_paths_for_new_block(bl, input_branches)
    else
        new_block_paths = get_input_paths_for_existing_block(bl, input_branches, new_paths)
    end
    check_path_cost = any(!isnothing(input_branches[ibr_key].min_path_cost) for (ibr_key, _) in bl.input_vars)
    best_cost = Inf
    for path in new_block_paths
        path[bl.output_var[1]] = bl
        if check_path_cost
            cost = sum(b.cost for b in values(path); init = 0.0)
            if cost < best_cost
                best_cost = cost
            end
        end
    end
    output_var = first(br for br in output_branches if br.key == bl.output_var[1])
    append!(output_var.incoming_paths, new_block_paths)
    if check_path_cost && (isnothing(output_var.min_path_cost) || best_cost < output_var.min_path_cost)
        output_var.min_path_cost = best_cost
        push!(sc.updated_cost_options, output_var)
    end
    new_paths[output_var] = new_block_paths
    if output_var.is_meaningful && !isa(bl.p, FreeVar)
        output_var.is_meaningful = true
    end
end

function get_new_paths_for_block(sc, bl::ReverseProgramBlock, is_new_block, new_paths, output_branches, input_branches)
    # @info "Getting paths for new block $bl"
    if is_new_block
        input_paths = get_input_paths_for_new_block(bl, input_branches)
    else
        input_paths = get_input_paths_for_existing_block(bl, input_branches, new_paths)
    end
    check_path_cost = any(!isnothing(input_branches[ibr_key].min_path_cost) for (ibr_key, _) in bl.input_vars)
    best_cost = Inf
    if check_path_cost
        for path in input_paths
            cost = sum(b.cost for b in values(path); init = 0.0) + bl.cost
            if cost < best_cost
                best_cost = cost
            end
        end
    end
    for (out_key, _) in bl.output_vars
        out_branch = first(br for br in output_branches if br.key == out_key)
        new_block_paths = []
        for path in input_paths
            push!(new_block_paths, merge(path, Dict(out_key => bl)))
        end
        append!(out_branch.incoming_paths, new_block_paths)
        if check_path_cost && (isnothing(out_branch.min_path_cost) || best_cost < out_branch.min_path_cost)
            out_branch.min_path_cost = best_cost
            push!(sc.updated_cost_options, out_branch)
        end
        new_paths[out_branch] = new_block_paths
        out_branch.is_meaningful = true
    end
end

function update_prev_follow_keys(sc, key, bl::ProgramBlock)
    union!(sc.following_keys[key], sc.following_keys[bl.output_var[1]])
    union!(sc.previous_keys[bl.output_var[1]], sc.previous_keys[key])
end

function update_prev_follow_keys(sc, key, bl::ReverseProgramBlock)
    for output_var in bl.output_vars
        union!(sc.following_keys[key], sc.following_keys[output_var[1]])
        union!(sc.previous_keys[output_var[1]], sc.previous_keys[key])
    end
end

function check_incoming_blocks(bl::ProgramBlock, new_branches)
    for branch in new_branches
        if branch.key == bl.output_var[1]
            push!(branch.incoming_blocks, bl)
        end
    end
end

function check_incoming_blocks(bl::ReverseProgramBlock, new_branches)
    out_keys = Set(key for (key, _) in bl.output_vars)
    for branch in new_branches
        if in(branch.key, out_keys)
            push!(branch.incoming_blocks, bl)
        end
    end
end

function _push_factor_diff_to_input(sc, branch::EntryBranch)
    inp_branches = Set()
    for br in get_all_children(branch)
        if !br.is_known
            if !isnothing(br.complexity)
                new_factor =
                    br.complexity +
                    br.added_upstream_complexity +
                    sum(b.unmatched_complexity for b in br.related_complexity_branches; init = 0.0)
                if new_factor < br.complexity_factor
                    br.complexity_factor = new_factor
                    push!(sc.updated_cost_options, br)
                    for inp_block in br.incoming_blocks
                        union!(inp_branches, (b for (_, b) in inp_block.input_vars))
                    end
                end
            else
                for out_block in br.outgoing_blocks
                    out_branch = out_block.output_var[2]
                    if out_branch.complexity_factor < br.complexity_factor
                        br.complexity_factor = out_branch.complexity_factor
                        push!(sc.updated_cost_options, br)
                    end
                end
            end
        end
    end
    for br in inp_branches
        _push_factor_diff_to_input(sc, br)
    end
end

function _push_best_complexity_to_output(
    sc,
    branch::EntryBranch,
    fixed_branches,
    active_constraints,
    best_complexity,
    unmatched_complexity,
)
    if branch.best_complexity > best_complexity || branch.unmatched_complexity > unmatched_complexity
        branch.best_complexity = min(branch.best_complexity, best_complexity)
        branch.unmatched_complexity = min(branch.unmatched_complexity, unmatched_complexity)
        for out_block in branch.outgoing_blocks
            new_branches = copy(fixed_branches)
            new_constraints = active_constraints
            in_complexity = 0.0
            un_complexity = 0.0
            for (in_key, in_root_branch) in out_block.input_vars
                if haskey(new_branches, in_key)
                    in_branch = new_branches[in_key]
                else
                    in_branch = get_branch_with_constraints(sc, in_key, new_constraints, in_root_branch)
                end
                in_complexity += in_branch.best_complexity
                un_complexity += in_branch.unmatched_complexity
                new_branches[in_key] = in_branch
                if all(!constraints_key(constraint, in_key) for constraint in new_constraints)
                    new_constraints = union(new_constraints, in_branch.constraints)
                end
            end
            out_branch =
                get_branch_with_constraints(sc, out_block.output_var[1], new_constraints, out_block.output_var[2])
            if all(!constraints_key(constraint, out_branch.key) for constraint in new_constraints)
                new_constraints = union(new_constraints, out_branch.constraints)
            end
            new_branches[out_block.output_var[1]] = out_branch
            _push_best_complexity_to_output(sc, out_branch, new_branches, new_constraints, in_complexity, un_complexity)
        end
    end
end

function _push_unmatched_complexity_to_input(branch::EntryBranch, fixed_branches, unmatched_complexity)
    if branch.unmatched_complexity > unmatched_complexity
        branch.unmatched_complexity = unmatched_complexity
        for in_block in branch.incoming_blocks
            if isa(in_block, ReverseProgramBlock)
                un_complexity = sum(
                    (haskey(fixed_branches, k) ? fixed_branches[k].unmatched_complexity : b.unmatched_complexity)
                    for (k, b) in in_block.output_vars
                )
            else
                k = in_block.output_var[1]
                un_complexity =
                    haskey(fixed_branches, k) ? fixed_branches[k].unmatched_complexity :
                    in_block.output_var[2].unmatched_complexity
            end
            for (in_key, in_branch) in in_block.input_vars
                if haskey(fixed_branches, in_key)
                    in_branch = fixed_branches[in_key]
                end
                _push_unmatched_complexity_to_input(in_branch, fixed_branches, un_complexity)
            end
        end
    end
end

function update_complexity_factors(sc, bl::ProgramBlock, input_branches, output_branches, new_paths, active_constraints)
    out_branch = first(br for br in output_branches if br.key == bl.output_var[1])
    if !isempty(bl.input_vars) && all(!input_branches[in_key].is_known for (in_key, _) in bl.input_vars)
        if any(isnothing(input_branches[in_key].complexity) for (in_key, _) in bl.input_vars)
            return Set()
        end
        in_complexity = sum(input_branches[in_key].complexity for (in_key, _) in bl.input_vars)

        _push_best_complexity_to_output(
            sc,
            out_branch,
            input_branches,
            active_constraints,
            in_complexity,
            in_complexity,
        )
        return out_branch.related_complexity_branches
    elseif all(input_branches[inp_branch_key].is_known for (inp_branch_key, _) in bl.input_vars)
        # @info out_branch
        if isempty(bl.input_vars)
            parents = out_branch.parents
            if isempty(parents)
                error("No parents for branch $out_branch")
            end
            parent_complexities = Set()
            best_parent = nothing
            for parent in parents
                if !isnothing(parent.complexity)
                    push!(parent_complexities, parent.complexity)
                end
                if isnothing(best_parent) || parent.complexity_factor > best_parent.complexity_factor
                    best_parent = parent
                end
            end
            if isnothing(out_branch.complexity_factor) || best_parent.complexity_factor < out_branch.complexity_factor
                out_branch.complexity_factor = best_parent.complexity_factor
                out_branch.added_upstream_complexity = out_branch.complexity_factor - out_branch.complexity
                # out_branch.related_complexity_branches = best_parent.related_complexity_branches
                push!(sc.updated_cost_options, out_branch)
            end
            # if !isempty(parent_complexities) && new_complexity < maximum(parent_complexities)
            #     _push_factor_diff_to_output(sc, out_branch, maximum(parent_complexities) - new_complexity)
            # end
        else
            related_branches = Set()
            in_complexity = 0.0
            added_upstream_complexity = 0.0
            for (inp_branch_key, _) in bl.input_vars
                inp_branch = input_branches[inp_branch_key]
                # @info inp_branch

                in_complexity += inp_branch.complexity
                added_upstream_complexity += inp_branch.added_upstream_complexity
                union!(related_branches, inp_branch.related_complexity_branches)
            end

            for path in new_paths[out_branch]
                filtered_related_branches = Set(b for b in related_branches if !haskey(path, b.key))
                if isa(bl.p, FreeVar) || bl.is_reversible
                    new_added_complexity = added_upstream_complexity
                else
                    new_added_complexity = added_upstream_complexity + max(out_branch.complexity - in_complexity, 0.0)
                end
                new_complexity_factor =
                    out_branch.complexity +
                    new_added_complexity +
                    sum(
                        (b.is_known == out_branch.is_known ? b.best_complexity : b.complexity) for
                        b in filtered_related_branches;
                        init = 0.0,
                    )
                if isnothing(out_branch.complexity_factor) || new_complexity_factor < out_branch.complexity_factor
                    out_branch.complexity_factor = new_complexity_factor
                    out_branch.added_upstream_complexity = new_added_complexity
                    out_branch.related_complexity_branches = filtered_related_branches
                    push!(sc.updated_cost_options, out_branch)
                end
            end
        end
        # @info out_branch

        for parent in out_branch.parents
            if !isnothing(parent.complexity)
                _push_best_complexity_to_output(
                    sc,
                    parent,
                    input_branches,
                    active_constraints,
                    parent.best_complexity,
                    0.0,
                )
                for (inp_branch_key, _) in bl.input_vars
                    inp_branch = input_branches[inp_branch_key]
                    _push_unmatched_complexity_to_input(inp_branch, input_branches, 0.0)
                end
            end
        end

        return union(
            Set(b for b in output_branches if b.key != out_branch.key),
            out_branch.related_complexity_branches,
            [p.related_complexity_branches for p in out_branch.parents]...,
        )

        # for output_branch in output_branches
        #     if output_branch.key == out_branch.key
        #         continue
        #     end
        #     # @info output_branch
        #     if !output_branch.is_known
        #         if !isnothing(output_branch.complexity)
        #             new_factor =
        #                 output_branch.complexity +
        #                 output_branch.added_upstream_complexity +
        #                 sum(
        #                     (b.is_known == output_branch.is_known ? b.best_complexity : b.complexity) for
        #                     b in output_branch.related_complexity_branches;
        #                     init = 0.0,
        #                 )
        #             if new_factor != output_branch.complexity_factor
        #                 output_branch.complexity_factor = new_factor
        #                 push!(sc.updated_cost_options, output_branch)
        #             end
        #             # elseif !isempty(output_branch.related_complexity_branches)
        #             #     error("Not implemented")
        #         end
        #     else
        #         error("Not implemented")
        #     end
        #     # @info output_branch
        # end
    else
        error("Not implemented")
    end
end

function _push_factor_diff_reverse_to_output(sc, branch::EntryBranch)
    out_branches = Set()
    # TODO: trace correct children branches
    new_factor =
        branch.complexity +
        branch.added_upstream_complexity +
        sum(
            (b.is_known == branch.is_known ? b.best_complexity : b.complexity) for
            b in branch.related_complexity_branches;
            init = 0.0,
        )
    if branch.complexity_factor > new_factor
        branch.complexity_factor = new_factor
        push!(sc.updated_cost_options, branch)
        for out_block in branch.outgoing_blocks
            if isa(out_block, ReverseProgramBlock)
                union!(out_branches, (b for (_, b) in out_block.output_vars))
            else
                push!(out_branches, out_block.output_var[2])
            end
        end
    end

    for br in out_branches
        _push_factor_diff_reverse_to_output(sc, br)
    end
end

function _push_factor_diff_reverse_to_input(sc, branch::EntryBranch, best_complexity, unmatched_complexity)
    if branch.best_complexity > best_complexity || branch.unmatched_complexity > unmatched_complexity
        branch.best_complexity = min(branch.best_complexity, best_complexity)
        branch.unmatched_complexity = min(branch.unmatched_complexity, unmatched_complexity)
        for in_block in branch.incoming_blocks
            if !isa(in_block, ReverseProgramBlock)
                continue
            end
            out_complexity = sum(b.best_complexity for (_, b) in in_block.output_vars)
            un_complexity = sum(b.unmatched_complexity for (_, b) in in_block.output_vars)
            _push_factor_diff_reverse_to_input(sc, in_block.input_vars[1][2], out_complexity, un_complexity)
        end
    end
end

function update_complexity_factors(
    sc,
    bl::ReverseProgramBlock,
    input_branches,
    output_branches,
    new_paths,
    active_constraints,
)
    out_keys = Set(key for (key, _) in bl.output_vars)
    in_branch = input_branches[bl.input_vars[1][1]]
    out_complexity = sum(branch.complexity for branch in output_branches if in(branch.key, out_keys))
    _push_factor_diff_reverse_to_input(sc, in_branch, out_complexity, out_complexity)
    return in_branch.related_complexity_branches
    # _push_factor_diff_reverse_to_output(sc, rel_branch)
end

function update_related_branch(sc, branch)
    if branch.is_known
        _push_factor_diff_reverse_to_output(sc, branch)
    else
        _push_factor_diff_to_input(sc, branch)
    end
end

function insert_operation(sc::SolutionContext, updates)
    new_paths = Dict()
    related_branches_to_update = Set()
    for (bl, new_branches, input_branches, active_constraints) in updates
        # @info new_branches
        # @info input_branches
        is_new_block = false
        for new_branch in new_branches
            is_new_block |= check_insert_new_branch(sc, new_branch)
        end
        for (inp_branch_key, _) in bl.input_vars
            check_insert_new_branch(sc, input_branches[inp_branch_key])
            if !in(bl, input_branches[inp_branch_key].outgoing_blocks)
                is_new_block = true
                push!(input_branches[inp_branch_key].outgoing_blocks, bl)
            end
            update_prev_follow_keys(sc, inp_branch_key, bl)
        end
        check_incoming_blocks(bl, new_branches)

        if all(input_branches[inp_branch_key].is_known for (inp_branch_key, _) in bl.input_vars)
            get_new_paths_for_block(sc, bl, is_new_block, new_paths, new_branches, input_branches)
        end
        # @info "Is new block $is_new_block"
        if is_new_block
            union!(
                related_branches_to_update,
                update_complexity_factors(sc, bl, input_branches, new_branches, new_paths, active_constraints),
            )
        end
    end
    for related_branch in related_branches_to_update
        update_related_branch(sc, related_branch)
    end
    new_full_paths = []
    for br in get_known_children(sc.var_data[sc.target_key])
        if haskey(new_paths, br)
            append!(new_full_paths, new_paths[br])
        end
    end
    return new_full_paths
end


keys_in_loop(sc, known_key, unknown_key) =
    !isempty(intersect(sc.previous_keys[known_key], sc.following_keys[unknown_key]))


function assert_context_consistency(sc::SolutionContext)
    function _iter_children(branch)
        return vcat([branch], [_iter_children(child) for child in branch.children]...)
    end
    function _get_roots(branch)
        if isempty(branch.parents)
            return Set([branch])
        else
            roots = union([_get_roots(parent) for parent in branch.parents]...)
            if length(roots) != 1
                error("Multiple roots for branch $branch")
            end
            return roots
        end
    end
    function _validate_branch(branch::EntryBranch)
        if branch.is_known
            if !isempty(branch.children)
                error("Known branch $branch has children")
            end
            if !in(branch, sc.known_branches[branch.type])
                error("Known branch $branch is not in known_branches")
            end
            if in(branch, sc.unknown_branches[branch.type])
                error("Known branch $branch is in unknown_branches")
            end
        else
            if in(branch, sc.known_branches[branch.type])
                error("Unknown branch $branch is in known_branches")
            end
            if !in(branch, sc.unknown_branches[branch.type])
                error("Unnown branch $branch is not in unknown_branches")
            end
        end
        for block in branch.outgoing_blocks
            if isempty(branch.parents)
                if !in((branch.key, branch), block.input_vars)
                    error("Branch $branch is not in inputs of block $block")
                end
            end
            if isa(block, ProgramBlock)
                out_roots = _get_roots(block.output_var[2])
            else
                out_roots = union([_get_roots(br) for (_, br) in block.output_vars]...)
            end
            for out_root in out_roots
                if !haskey(sc.var_data, out_root.key) || sc.var_data[out_root.key] != out_root
                    error("Branch $out_root is not in var_data")
                end
            end
        end
        for parent in branch.parents
            if !in(branch, parent.children)
                error("Branch $branch is not in parent $parent")
            end
        end
        for child in branch.children
            if !in(branch, child.parents)
                error("Branch $branch is not in child $child")
            end
            if !issubset(branch.outgoing_blocks, child.outgoing_blocks)
                error("Branch $branch outgoing blocks are missing from child $child outgoing blocks")
            end
            if branch.key != child.key
                error("Branch $branch key differs from child $child key")
            end
        end
        for constraint in branch.constraints
            if constraint.branches[branch.key] != branch
                error("Branch $branch is not in constraint $constraint")
            end
            for (_, other_branch) in constraint.branches
                for other_root in _get_roots(other_branch)
                    if !haskey(sc.var_data, other_root.key) || sc.var_data[other_root.key] != other_root
                        error("Branch $other_root is not in var_data")
                    end
                end
            end
        end

    end
    for (key, branch) in sc.var_data
        if !isempty(branch.parents)
            error("Root branch $branch has parents")
        end
        for br in _iter_children(branch)
            _validate_branch(br)
        end
    end
end
