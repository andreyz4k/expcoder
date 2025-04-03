
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
    in_blocks, out_blocks, copy_blocks, vars_mapping = _extract_blocks(task, program, false)
    for (var, blocks) in Iterators.flatten([out_blocks, in_blocks])
        for (i, block) in enumerate(blocks)
            if isa(block.p, FreeVar)
                continue
            end
            for j in 1:i-1
                if !isa(blocks[j].p, FreeVar) && is_on_path(block.p, blocks[j].p, Dict(), true)
                    return false
                end
            end
        end
    end
    return true
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
        rewritten_program = alpha_substitution(new_program, replacements, Set(), Set(), UInt64(1), Dict())[1]
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
