
mutable struct DummyGuidingModel <: AbstractGuidingModel
    grammar::Any
    preset_weights::Dict
    log_variable::Float64
    log_lambda::Float64
    log_free_var::Float64
end

function DummyGuidingModel()
    return DummyGuidingModel(nothing, Dict(), 0.0, -3.0, -3.0)
end

function set_current_grammar!(guiding_model::DummyGuidingModel, grammar)
    full_grammar = vcat(grammar, [Index(0), "lambda", FreeVar(t0, t0, UInt64(1), nothing)])
    guiding_model.grammar = full_grammar
end

function clear_model_cache(guiding_model::DummyGuidingModel)
    guiding_model.grammar = nothing
end

function run_guiding_model(guiding_model::DummyGuidingModel, model_inputs)
    start = time()
    grammar_len = length(guiding_model.grammar)
    batch_size = length(model_inputs[4])

    result = zeros(grammar_len, batch_size)
    result[grammar_len-2, :] .= guiding_model.log_variable
    result[grammar_len-1, :] .= guiding_model.log_lambda
    result[grammar_len, :] .= guiding_model.log_free_var

    for (fname, weight) in guiding_model.preset_weights
        prim = every_primitive[fname]
        i = findfirst(isequal(prim), guiding_model.grammar)
        result[i, :] .= weight
    end

    return Dict("run" => time() - start), result
end

function update_guiding_model(guiding_model::DummyGuidingModel, traces)
    return guiding_model
end

using JLD2

function save_guiding_model(m::DummyGuidingModel, path)
    model_state = (m.preset_weights, m.log_variable, m.log_lambda, m.log_free_var)
    jldsave(path; type = "dummy", model_state)
end

function load_guiding_model(::Type{DummyGuidingModel}, model_state)
    m = DummyGuidingModel()
    (m.preset_weights, m.log_variable, m.log_lambda, m.log_free_var) = model_state
    return m
end

function get_encoded_value_length(model::DummyGuidingModel, max_summary)
    return 1
end
