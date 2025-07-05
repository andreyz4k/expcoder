
using StitchBindings

function extract_programs_and_tasks(traces)
    programs = String[]
    tasks = String[]
    all_hits = []
    for (task_name, hits) in traces
        for (hit, cost) in hits
            push!(programs, hit.hit_program)
            push!(tasks, task_name)
            push!(all_hits, (hit, cost))
        end
    end
    return programs, tasks, all_hits
end

function store_precompressed_traces(traces, grammar)
    traces_dir = "compressed_traces"
    if !isdir(traces_dir)
        mkdir(traces_dir)
    end
    fname = joinpath(traces_dir, string(Dates.now()))
    Serialization.serialize(fname, (traces, [string(p) for p in grammar]))
    @info "Stored precompressed traces to $fname"
end

function check_repeating_blocks(task, program)
    in_blocks, out_blocks, copy_blocks, vars_mapping, var_types = _extract_blocks(TypeStorage(), task, program, false)
    for (var, blocks) in Iterators.flatten([out_blocks, in_blocks])
        for (i, block) in enumerate(blocks)
            if isa(block.p, FreeVar)
                continue
            end
            for j in 1:i-1
                if !isa(blocks[j].p, FreeVar) && is_on_path(block.p, blocks[j].p, Dict())
                    return false
                end
            end
        end
    end
    return true
end

function _get_noncopy_free_vars(p::LetClause)
    if isa(p.v, FreeVar)
        return _get_noncopy_free_vars(p.b)
    end
    return merge(_get_free_vars(p.v), _get_noncopy_free_vars(p.b))
end

function _get_noncopy_free_vars(p::LetRevClause)
    return merge(_get_free_vars(p.v), _get_noncopy_free_vars(p.b))
end

_get_noncopy_free_vars(p::Program) = _get_free_vars(p)

function _insert_copy_blocks(
    p::LetRevClause,
    next_var_id::UInt64,
    replacements::Dict{Any,Any},
    base_mapping::Dict{Any,Any},
)
    return LetRevClause(p.var_ids, p.inp_var_id, p.v, _insert_copy_blocks(p.b, next_var_id, replacements, base_mapping))
end

function _insert_copy_blocks(
    p::LetClause,
    next_var_id::UInt64,
    replacements::Dict{Any,Any},
    base_mapping::Dict{Any,Any},
)
    used_vars = _get_free_vars(p.v)
    used_body_vars = keys(_get_noncopy_free_vars(p.b))
    new_v = alpha_substitution(p.v, replacements, Set(), Set(), next_var_id, Dict())[1]
    copy_blocks = []
    if !isa(new_v, FreeVar)
        for v in keys(used_vars)
            if in(v, used_body_vars)
                push!(copy_blocks, (v, next_var_id))
                replacements[v] = next_var_id
                next_var_id += 1
            end
        end
    else
        base_mapping[p.var_id] = p.v.var_id
    end
    new_b = _insert_copy_blocks(p.b, next_var_id, replacements, base_mapping)
    for (v, copy_v) in copy_blocks
        if haskey(base_mapping, v)
            new_b = LetClause(copy_v, FreeVar(used_vars[v][1], used_vars[v][2], base_mapping[v], nothing), new_b)
        else
            new_b = LetClause(copy_v, FreeVar(used_vars[v][1], used_vars[v][2], v, nothing), new_b)
        end
    end
    return LetClause(p.var_id, new_v, new_b)
end

function _insert_copy_blocks(p::Program, next_var_id::UInt64, replacements::Dict{Any,Any}, base_mapping::Dict{Any,Any})
    return alpha_substitution(p, replacements, Set(), Set(), next_var_id, Dict())[1]
end

function compress_traces(tasks, traces, grammar)
    if isempty(traces)
        return traces, grammar
    end
    tasks_dict = Dict(task.name => task for task in tasks)
    # store_precompressed_traces(traces, grammar)
    existing_inventions = String[string(p) for p in grammar if isa(p, Invented)]
    programs, tasks, hits = extract_programs_and_tasks(traces)
    iterations = 0
    max_arity = 3
    silent = false
    threads = 1
    panic_loud = true
    rewritten_dreamcoder = true
    new_abstractions, rewritten_programs = compress_backend(
        programs,
        tasks,
        existing_inventions,
        iterations,
        max_arity,
        threads,
        silent,
        panic_loud,
        rewritten_dreamcoder,
        ;
        eta_long = true,
        utility_by_rewrite = true,
    )
    new_grammar = Program[p for p in grammar]
    for abst_dict in new_abstractions
        new_abstraction = parse_program(abst_dict["body"])
        if !in(new_abstraction, new_grammar)
            push!(new_grammar, new_abstraction)
        end
    end
    new_traces = Dict()
    for ((hit, cost), task_name, new_program_str) in zip(hits, tasks, rewritten_programs)
        new_program = parse_program(new_program_str)
        replacements = Dict{Any,Any}("output" => "output")
        argument_types = arguments_of_type(tasks_dict[task_name].task_type)
        for (key, t) in argument_types
            replacements[key] = key
        end

        rewritten_program = _insert_copy_blocks(
            new_program,
            maximum(filter(k -> isa(k, UInt64), keys(_get_free_vars(new_program))); init = UInt64(0)) + UInt64(1),
            Dict(),
            Dict(),
        )
        rewritten_program = alpha_substitution(rewritten_program, replacements, Set(), Set(), UInt64(1), Dict())[1]
        if !check_repeating_blocks(tasks_dict[task_name], rewritten_program)
            continue
        end
        trace_values = Dict()
        for (var_id, val) in hit.trace_values
            if haskey(replacements, var_id)
                trace_values[replacements[var_id]] = val
            end
        end
        if !haskey(new_traces, task_name)
            new_traces[task_name] = PriorityQueue{HitResult,Float64}()
        end
        new_hit = HitResult(string(rewritten_program), hit.hit_prior, hit.hit_likelihood, hit.hit_time, trace_values)
        new_traces[task_name][new_hit] = cost
    end
    return new_traces, new_grammar
end
