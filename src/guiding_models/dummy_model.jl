
mutable struct DummyGuidingModel
    preset_weights::Dict
    log_variable::Float64
    log_lambda::Float64
    log_free_var::Float64
end

function DummyGuidingModel()
    return DummyGuidingModel(Dict(), 0.0, -3.0, -3.0)
end

function run_guiding_model(guiding_model::DummyGuidingModel, model_inputs)
    start = time()
    grammar = model_inputs[1]
    grammar_len = length(grammar)
    batch_size = length(model_inputs[2])

    result = zeros(grammar_len, batch_size)
    result[grammar_len-2, :] .= guiding_model.log_variable
    result[grammar_len-1, :] .= guiding_model.log_lambda
    result[grammar_len, :] .= guiding_model.log_free_var

    for (fname, weight) in guiding_model.preset_weights
        prim = every_primitive[fname]
        i = findfirst(isequal(prim), grammar)
        result[i, :] .= weight
    end

    return time() - start, result
end

function update_guiding_model(guiding_model::DummyGuidingModel, traces)
    return guiding_model
end

function get_encoded_value_length(model::DummyGuidingModel, max_summary)
    return 1
end
