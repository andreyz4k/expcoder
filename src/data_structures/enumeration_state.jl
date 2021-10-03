

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
    input_vals::Vector{String}
    output_vals::Vector{String}
end


initial_enumeration_state(request, g::Grammar) =
    EnumerationState(Hole(request, g), empty_context, [], 0.0, 0)


initial_block_prototype(request, g::Grammar, inputs, outputs) =
    BlockPrototype(initial_enumeration_state(request, g), inputs, outputs)


get_candidates_for_unknown_var(sol_ctx, key, value, g) = [initial_block_prototype(value.type, g.no_context, [], [key])]

state_finished(state::EnumerationState) =
    if isa(state.skeleton, Hole)
        false
    else
        isempty(state.path)
    end
