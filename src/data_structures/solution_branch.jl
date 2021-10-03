
using DataStructures

mutable struct SolutionBranch
    known_vars::Dict{String,ValueEntry}
    unknown_vars::Dict{String,Entry}
    fill_percentages::Dict{String,Float64}
    operations::Vector{ProgramBlock}
    parent::Union{Nothing,SolutionBranch}
    children::Vector{SolutionBranch}
    example_count::Int64
    created_vars::Int64
    ops_by_input::MultiDict{String,ProgramBlock}
    ops_by_output::MultiDict{String,ProgramBlock}
end


function create_start_solution(task::Task)::SolutionBranch
    known_vars = Dict{String,ValueEntry}()
    fill_percentages = Dict{String,Float64}()
    argument_types = arguments_of_type(task.task_type)
    for (i, (t, values)) in enumerate(zip(argument_types, zip(task.train_inputs...)))
        key = "\$$i"
        known_vars[key] = ValueEntry(t, collect(values))
        fill_percentages[key] = 1.0
    end
    unknown_vars = Dict{String,Entry}("out" => ValueEntry(return_of_type(task.task_type), task.train_outputs))
    fill_percentages["out"] = 0.0
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
        MultiDict{String,ProgramBlock}(),
        MultiDict{String,ProgramBlock}(),
    )
end

function create_next_var(solution_ctx)
    solution_ctx.created_vars += 1
    solution_ctx.created_vars - 1
end

iter_unknown_vars(solution_ctx) = solution_ctx.unknown_vars
