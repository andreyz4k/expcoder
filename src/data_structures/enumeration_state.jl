

abstract type Turn end

struct LeftTurn <: Turn end
struct RightTurn <: Turn end
struct ArgTurn <: Turn
    type::Tp
end

struct EnumerationState
    skeleton::Program
    context::Context
    path::Vector{Turn}
    cost::Float64
    free_parameters::Int64
end


struct BlockPrototype
    state::EnumerationState
    request::Tp
    input_vals::Vector{Union{Tuple{String,UInt64},Nothing}}
    output_val::Union{Tuple{String,UInt64},Nothing}
end


initial_enumeration_state(request, g::Grammar) = EnumerationState(Hole(request, g), empty_context, [], 0.0, 0)


initial_block_prototype(request, g::Grammar, inputs, output) =
    BlockPrototype(initial_enumeration_state(request, g), request, inputs, output)


function get_candidates_for_unknown_var(sol_ctx, key, g)
    [
        initial_block_prototype(option.value.type, g.no_context, [], (key, entry_hash)) for
        (entry_hash, option) in sol_ctx.var_data[key].options
    ]
end

function get_candidates_for_known_var(sol_ctx, key, g::ContextualGrammar)
    candidates = []
    for (entry_hash, option) in sol_ctx.var_data[key].options
        for (p, t, context, ll, i) in following_expressions(g.no_context, option.value.type)
            skeleton = p
            path = []
            for (j, arg_type) in enumerate(arguments_of_type(t))
                if j == i
                    skeleton = Apply(skeleton, FreeVar(type, key))
                    if !isempty(path)
                        path = vcat([LeftTurn()], path)
                    end
                else
                    skeleton = Apply(skeleton, Hole(arg_type, g.contextual_library[p][j]))
                    if isempty(path)
                        path = [RightTurn()]
                    else
                        path = vcat([LeftTurn()], path)
                    end
                end
            end
            state = EnumerationState(skeleton, context, path, ll + g.no_context.log_variable, 1)
            push!(
                candidates,
                BlockPrototype(
                    state,
                    return_of_type(t),
                    [j == i ? (key, entry_hash) : nothing for j = 1:length(arguments_of_type(t))],
                    nothing,
                ),
            )
        end
    end
    candidates
end

state_finished(state::EnumerationState) =
    if isa(state.skeleton, Hole)
        false
    else
        isempty(state.path)
    end
