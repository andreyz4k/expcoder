
using DataStructures


get_enumeration_timeout(timeout) = time() + timeout
enumeration_timed_out(timeout) = time() > timeout

struct Entry
    type::Tp
    values::Vector
end

mutable struct SolutionBranch
    known_vars::Dict{String,Entry}
    unknown_vars::Dict{String,Entry}
    fill_percentages::Dict{String,Float64}
    operations::Vector{ProgramBlock}
    parent::Union{Nothing,SolutionBranch}
    children::Vector{SolutionBranch}
    example_count::Int64
    created_vars::Int64
    ops_by_input::Dict{String,Vector{ProgramBlock}}
    ops_by_output::Dict{String,Vector{ProgramBlock}}
end


function create_start_solution(task::Task)::SolutionBranch
    known_vars = Dict{String,Entry}()
    fill_percentages = Dict{String,Float64}()
    argument_types = arguments_of_type(task.task_type)
    for (i, (t, values)) in enumerate(zip(argument_types, zip(task.train_inputs...)))
        key = "\$$i"
        known_vars[key] = Entry(t, collect(values))
        fill_percentages[key] = 1.0
    end
    unknown_vars = Dict{String,Entry}("out" => Entry(return_of_type(task.task_type), task.train_outputs))
    example_count = length(task.train_outputs)
    SolutionBranch(
        known_vars,
        unknown_vars,
        fill_percentages,
        [],
        nothing,
        [],
        example_count,
        0,
        Dict(),
        Dict()
    )
end


function enumerate_for_task(g::ContextualGrammar, timeout, task, maximum_frontier, verbose = true)
    #    Returns, for each task, (program,logPrior) as well as the total number of enumerated programs
    enumeration_timeout = get_enumeration_timeout(timeout)

    start_solution_ctx = create_start_solution(task)

    # Store the hits in a priority queue
    # We will only ever maintain maximumFrontier best solutions
    hits = PriorityQueue()


    total_number_of_enumerated_programs = 0
    maxFreeParameters = 2

    pq = PriorityQueue()

    #   SolutionCtx.iter_known_vars start_solution_ctx ~f:(fun ~key ~data ->
    #       List.iter (get_candidates_for_known_var start_solution_ctx key data g) ~f:(fun candidate ->
    #           Heap.add pq (start_solution_ctx, candidate)));
    #   SolutionCtx.iter_unknown_vars start_solution_ctx ~f:(fun ~key ~data ->
    #       List.iter (get_candidates_for_unknown_var start_solution_ctx key data g) ~f:(fun candidate ->
    #           Heap.add pq (start_solution_ctx, candidate)));

    while (!(enumeration_timed_out(enumeration_timeout))) && !isempty(pq) && length(hits) < maximumFrontier
        (s_ctx, bp), pr = peek(pq)
        dequeue!(pq)
        for child in block_state_successors(maxFreeParameters, g, bp.state)

            if state_finished(child)
                p, ts = capture_free_vars(child.skeleton)

                new_vars = map(ts) do
                    ntv = no_data_task_val(t)
                    key = "v"^String(create_next_var(s_ctx))
                    add_unknown_var(s_ctx, key, ntv)
                    key
                end

                new_block = Block(p, inputs = new_vars, outputs = bp.output_vals)
                new_sctx = add_new_block(s_ctx, new_block)
                matches = get_matches(new_sctx, new_block.inputs)

            else

                pq[(s_ctx, BlockPrototype(state = child, input_vals = bp.input_vals, output_vals = bp.output_vals))] = 0
            end
        end
    end

    (collect(keys(hits)), total_number_of_enumerated_programs)

end
