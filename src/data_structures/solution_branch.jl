
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
    updated_keys::Set{String}
    target_key::String
    input_keys::Vector{String}
end


function create_start_solution(task::Task)::SolutionBranch
    known_vars = Dict{String,ValueEntry}()
    fill_percentages = Dict{String,Float64}()
    argument_types = arguments_of_type(task.task_type)
    input_keys = []
    for (i, (t, values)) in enumerate(zip(argument_types, zip(task.train_inputs...)))
        key = "\$i$i"
        known_vars[key] = ValueEntry(t, collect(values))
        fill_percentages[key] = 1.0
        push!(input_keys, key)
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
        Set{String}(),
        "out",
        input_keys,
    )
end

function Base.getindex(branch::SolutionBranch, key)
    if haskey(branch.known_vars, key)
        return branch.known_vars[key]
    elseif haskey(branch.unknown_vars, key)
        return branch.unknown_vars[key]
    elseif !isnothing(branch.parent)
        return branch.parent[key]
    else
        throw(KeyError(key))
    end
end

Base.haskey(branch::SolutionBranch, key) =
    haskey(branch.known_vars, key) ||
    haskey(branch.unknown_vars, key) ||
    (!isnothing(branch.parent) && haskey(branch.parent, key))


function set_known(branch::SolutionBranch, key, value)
    branch.known_vars[key] = value
    push!(branch.updated_keys, key)
    branch.fill_percentages[key] = 1.0
end

function set_unknown(branch::SolutionBranch, key, value)
    branch.unknown_vars[key] = value
    push!(branch.updated_keys, key)
end

function move_to_known(branch::SolutionBranch, key, value)
    if haskey(branch.unknown_vars, key)
        delete!(branch.unknown_vars, key)
    end
    branch.known_vars[key] = value
    push!(branch.updated_keys, key)
    branch.fill_percentages[key] = 1.0
end

function reset_updated_keys(branch::SolutionBranch)
    branch.updated_keys = Set{String}()
end


function isknown(branch::SolutionBranch, key)
    if haskey(branch.known_vars, key)
        true
    elseif !isnothing(branch.parent)
        isknown(branch.parent, key)
    else
        false
    end
end

function create_next_var(solution_ctx)
    if !isnothing(solution_ctx.parent)
        return create_next_var(solution_ctx.parent)
    else
        solution_ctx.created_vars += 1
        solution_ctx.created_vars - 1
    end
end

function insert_operation(sc::SolutionBranch, block)
    push!(sc.operations, block)
    for key in block.inputs
        insert!(sc.ops_by_input, key, block)
    end
    insert!(sc.ops_by_output, block.output, block)
end

function downstream_ops(sc::SolutionBranch, key)
    outs = []
    if haskey(sc.ops_by_input, key)
        push!(outs, sc.ops_by_input[key])
    end
    if !isnothing(sc.parent)
        push!(outs, downstream_ops(sc.parent, key))
    end
    flatten(outs)
end

iter_unknown_vars(sc::SolutionBranch) = sc.unknown_vars

function iter_known_vars(sc::SolutionBranch)
    if !isnothing(sc.parent)
        flatten([sc.known_vars, (k => v for (k, v) in iter_known_vars(sc.parent) if !haskey(sc.known_vars, k))])
    else
        sc.known_vars
    end
end

is_solved(sc::SolutionBranch) = isknown(sc, sc.target_key)

iter_operations(sc::SolutionBranch) =
    if isnothing(sc.parent)
        sc.operations
    else
        flatten([sc.operations, iter_operations(sc.parent)])
    end
