
using PythonCall

mutable struct PythonGuidingModel <: AbstractGuidingModel
    py_model::Any
end

function __init__()
    sys = pyimport("sys")
    sys.path = pylist([@__DIR__]) + sys.path
end

function PythonGuidingModel()
    PythonCall.GIL.@lock begin
        py_module = pyimport("guiding_model")
        importlib = pyimport("importlib")
        importlib.reload(py_module)
        return PythonGuidingModel(py_module.create_model())
    end
end

function set_current_grammar!(guiding_model::PythonGuidingModel, grammar)
    PythonCall.GIL.@lock begin
        full_grammar = vcat([string(g) for g in grammar], ["\$0", "lambda", "\$v1"])
        guiding_model.py_model.set_current_grammar(pylist(full_grammar))
    end
end

function clear_model_cache(guiding_model::PythonGuidingModel) end

function build_train_set(all_traces, guiding_model::PythonGuidingModel, batch_size)
    groups = pylist()

    for (grammar, gr_traces) in values(all_traces)
        full_grammar = vcat([string(g) for g in grammar], ["\$0", "lambda", "\$v1"])

        X_data = []
        summaries = []
        for (task_name, traces) in gr_traces
            for (hit, cost) in traces
                inputs = [v[2] for (k, v) in hit.trace_values if isa(k, String) && k != "output"]
                outputs = hit.trace_values["output"][2]
                if any(isa(v, PatternWrapper) for v in outputs)
                    continue
                end

                blocks = extract_program_blocks(hit.hit_program)
                for (var_id, p, is_rev) in blocks
                    trace_val = hit.trace_values[var_id]
                    summary = build_likelihood_summary(grammar, trace_val[1], p, is_rev)
                    if isempty(summary[2])
                        continue
                    end
                    push!(
                        X_data,
                        (
                            _preprocess_inputs(inputs),
                            _preprocess_output(outputs),
                            _unfold_trace_value(trace_val...),
                            is_rev,
                        ),
                    )
                    summary =
                        (Py(summary[1]).to_numpy(), Py(summary[2]).to_numpy(), Py(summary[3]).to_numpy(), summary[4])
                    push!(summaries, summary)
                end
            end
        end
        if !isempty(X_data)
            groups.append(guiding_model.py_model.build_dataset(full_grammar, X_data, summaries, batch_size))
        end
    end
    return groups
end

function update_guiding_model(guiding_model::PythonGuidingModel, traces)
    @info "Updating guiding model"
    PythonCall.GIL.@lock begin
        @info "Got GIL"
        train_set = build_train_set(traces, guiding_model, 40)
        if isempty(train_set)
            return guiding_model
        end
        guiding_model.py_model.run_training(train_set)
        return guiding_model
    end
end

function __unfold_trace_value(val)
    return [val], ones(Float32, 1, 1)
end

function __unfold_trace_value(val::EitherOptions)
    output = []
    next_masks = []
    for op in values(val.options)
        vals, mask = __unfold_trace_value(op)
        append!(output, vals)
        push!(next_masks, mask)
    end

    cur_m = fill(1 / Float32(length(val.options)), length(val.options))
    out_mask = _make_next_mask(next_masks) * cur_m

    return output, out_mask
end

function _unfold_trace_value(tp, trace_val)
    output = []
    next_masks = []
    for val in trace_val
        vals, mask = __unfold_trace_value(val)
        for v in vals
            push!(output, string((tp, v)))
        end
        push!(next_masks, mask)
    end
    cur_m = fill(1 / Float32(length(trace_val)), length(trace_val))
    return pylist(output), Py(_make_next_mask(next_masks) * cur_m).to_numpy()
end

function _unfold_trace_values(model::PythonGuidingModel, trace_vals)
    output = pylist()
    masks = pylist()
    for (tp, value) in trace_vals
        vals, mask = _unfold_trace_value(tp, value)
        output.extend(vals)
        masks.append(mask)
    end
    out_mask = model.py_model.combine_masks(masks)

    return output, out_mask
end

function _preprocess_inputs(inputs)
    var_count = length(inputs)
    example_count = length(inputs[1])
    subbatch_mask = fill(1 / (example_count * var_count), example_count * var_count, 1)

    max_x = maximum(size(v, 1) for var in inputs for v in var; init = 3)
    max_y = maximum(size(v, 2) for var in inputs for v in var; init = 3)
    input_matrix = fill(10, example_count * var_count, max_x, max_y)
    input_mask = zeros32(example_count * var_count, max_x, max_y)

    i = 1
    for var_examples in inputs
        for example in var_examples
            k, l = size(example)
            input_matrix[i, 1:k, 1:l] = example
            input_mask[i, 1:k, 1:l] .= 1.0

            i += 1
        end
    end
    input_batch = onehotbatch(input_matrix, 0:10)[1:10, :, :, :]
    input_batch = permutedims(input_batch, [2, 1, 3, 4])
    return Py(input_batch).to_numpy(), Py(input_mask).to_numpy(), Py(subbatch_mask).to_numpy()
end

function _preprocess_input_batch(model::PythonGuidingModel, inputs)
    processed_inputs = [_preprocess_inputs(i) for i in inputs]
    return model.py_model.process_input_output_batch(processed_inputs)
end

function _preprocess_output(output)
    example_count = length(output)
    subbatch_mask = fill(1 / (example_count), example_count, 1)

    max_x = maximum(size(v, 1) for v in output; init = 3)
    max_y = maximum(size(v, 2) for v in output; init = 3)
    output_matrix = fill(10, example_count, max_x, max_y)
    output_mask = zeros32(example_count, max_x, max_y)
    for (j, example) in enumerate(output)
        k, l = size(example)
        output_matrix[j, 1:k, 1:l] = example
        output_mask[j, 1:k, 1:l] .= 1.0
    end
    output_batch = onehotbatch(output_matrix, 0:10)[1:10, :, :, :]
    output_batch = permutedims(output_batch, [2, 1, 3, 4])
    return Py(output_batch).to_numpy(), Py(output_mask).to_numpy(), Py(subbatch_mask).to_numpy()
end

function _preprocess_output_batch(model::PythonGuidingModel, outputs)
    processed_outputs = [_preprocess_output(o) for o in outputs]
    return model.py_model.process_input_output_batch(processed_outputs)
end

function run_guiding_model(guiding_model::PythonGuidingModel, model_inputs)
    times = Dict()
    start = time()
    inputs, outputs, trace_val, is_reversed, task_names = model_inputs

    PythonCall.GIL.@lock begin
        trace_val_batch = _unfold_trace_values(guiding_model, trace_val)
        inputs_batch = _preprocess_input_batch(guiding_model, inputs)
        outputs_batch = _preprocess_output_batch(guiding_model, outputs)

        times["preprocessing"] = time() - start
        start = time()

        is_reversed = Py(permutedims(is_reversed, [2, 1])).to_numpy()

        result, m_times = guiding_model.py_model.predict(inputs_batch, outputs_batch, trace_val_batch, is_reversed)
        for (k, t) in m_times.items()
            times[pyconvert(String, k)] = pyconvert(Float32, t)
        end

        result = permutedims(pyconvert(Array, result), [2, 1])
        # PythonCall.GC.gc()

        times["run"] = time() - start
        return times, result
    end
end

function save_guiding_model(m::PythonGuidingModel, path)
    PythonCall.GIL.@lock begin
        py_path = path * ".pt"
        m.py_model.save(py_path)
        model_state = Dict("py_model" => py_path)
        jldsave(path; type = "python", model_state)
    end
end

function load_guiding_model(::Type{PythonGuidingModel}, model_state)
    m = PythonGuidingModel()
    py_path = model_state["py_model"]
    PythonCall.GIL.@lock begin
        m.py_model.load(py_path)
        return m
    end
end

function get_encoded_value_length(model::PythonGuidingModel, max_summary)
    sum(token_weights[tname] * count for (tname, count) in max_summary; init = 0)
end
