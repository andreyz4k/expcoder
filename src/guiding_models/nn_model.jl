
using Flux
using NNlib

using Transformers

d_emb = 384

d_state_in = d_emb * 4 + 1
d_state_h = 512
d_state_out = 384

d_dec_h = 64
head_num = 4

using Transformers.TextEncoders: TransformerTextEncoder

vocab = vcat(
    ["pr_$n" for (n, p) in every_primitive],
    [string(i) for i in 0:9],
    ["i$i" for i in 0:9],
    ["v$i" for i in 0:9],
    [" $i" for i in 0:9],
    ["c$i" for i in 0:9],
    [
        "(",
        ")",
        "\$",
        "\$v",
        "lambda",
        "inp",
        "SetConst",
        "#",
        "[",
        "]",
        ";",
        ",",
        "any_object",
        "nothing",
        "[[",
        "]]",
        "{",
        "}",
        "EitherOptions(",
        "PatternWrapper(",
        "AbductibleValue(",
    ],
)

tokenize(p::Primitive) = ["pr_$p"]
tokenize(p::Abstraction) = vcat(["(", "lambda"], tokenize(p.b), [")"])
tokenize(p::Index) = vcat(["\$"], ["i$s" for s in split(string(p), "")])
function tokenize(p::FreeVar)
    if isa(p.var_id, String)
        if startswith(p.var_id, "inp")
            vcat(["\$v", "inp"], ["v$s" for s in split(string(p), "")[4:end]])
        else
            error("Unknown free var id: $(p.var_id)")
        end
    else
        vcat(["\$v"], ["v$s" for s in split(string(p), "")])
    end
end
tokenize(p::Apply) = vcat(["("], tokenize(p.f), tokenize(p.x), [")"])
tokenize(p::SetConst) = vcat(["SetConst"], tokenize(p.t, p.value))
tokenize(p::Invented) = vcat(["#"], tokenize(p.b))

function tokenize(t::Tp, v::Int)
    if t == tint
        chars = split(string(v), "")
        return vcat([" $(chars[1])"], chars[2:end])
    elseif t == tcolor
        return ["c$v"]
    else
        error("Unknown type for int: $t")
    end
end
tokenize(t, v::AnyObject) = ["any_object"]
tokenize(t, v::Nothing) = ["nothing"]

function tokenize(t, v::Vector)
    tokens = ["["]
    for (i, x) in enumerate(v)
        # if i > 1
        #     push!(tokens, ",")
        # end
        append!(tokens, tokenize(t.arguments[1], x))
    end
    push!(tokens, "]")
    return tokens
end

function tokenize(t, v::Set)
    tokens = ["{"]
    for (i, x) in enumerate(v)
        # if i > 1
        #     push!(tokens, ",")
        # end
        append!(tokens, tokenize(t.arguments[1], x))
    end
    push!(tokens, "}")
    return tokens
end

function tokenize(t::TypeConstructor, v::Matrix)
    tokens = ["[["]
    for i in 1:size(v, 1)
        if i > 1
            push!(tokens, ";")
        end
        for j in 1:size(v, 2)
            # if j > 1
            #     push!(tokens, ",")
            # end
            append!(tokens, tokenize(t.arguments[1], v[i, j]))
        end
    end
    push!(tokens, "]]")
    return tokens
end
tokenize(t::TypeConstructor, v::Tuple) =
# vcat(["("], tokenize(t.arguments[1], v[1]), [","], tokenize(t.arguments[2], v[2]), [")"])
    vcat(["("], tokenize(t.arguments[1], v[1]), tokenize(t.arguments[2], v[2]), [")"])

function tokenize(t, v::EitherOptions)
    return [tokenize(t, x) for (_, x) in v.options]
end

tokenize(t, v::PatternWrapper) = vcat(["PatternWrapper("], tokenize(t, v.value), [")"])
tokenize(t, v::AbductibleValue) = vcat(["AbductibleValue("], tokenize(t, v.value), [")"])

token_weights = Dict(
    "int" => 1,
    "list" => 2,
    "color" => 1,
    "bool" => 1,
    "float" => 1,
    "grid" => 2,
    "tuple2" => 2,
    "coord" => 1,
    "set" => 2,
    "any" => 1,
    "nothing" => 1,
)

struct ValueWrapper
    value::Any
end
Base.isempty(::ValueWrapper) = false

using Transformers.TextEncoders.TextEncodeBase: Sentence, Batch, Token, TokenStage, TokenStages

annotate_objects(x::Program) = Sentence(x, (is_batch = false,))
annotate_objects(x::Vector) = Batch{Sentence}(x, (is_batch = true,))

annotate_objects(x::Tuple) = Batch{Sentence}([ValueWrapper(v) for v in x[2]], (tp = x[1], is_batch = false))
annotate_objects(x::Vector{<:Tuple}) = Batch{Batch{Sentence}}(x, (is_batch = true,))

annotate_objects(x::Dict) = Batch{Batch{Sentence}}(collect(values(x)), (is_batch = false,))
annotate_objects(x::Vector{<:Dict}) = Batch{Batch{Batch{Sentence}}}(x, (is_batch = true,))

Base.isempty(::Program) = false
struct ExpCoderTokenization <: TextEncoders.AbstractTokenization end

TextEncoders.TextEncodeBase.splittability(::ExpCoderTokenization, w::Sentence) =
    TextEncoders.TextEncodeBase.Splittable()
TextEncoders.TextEncodeBase.splittability(::ExpCoderTokenization, ::Batch) = TextEncoders.TextEncodeBase.Splittable()

function TextEncoders.TextEncodeBase.splitting(::ExpCoderTokenization, s::Batch)
    s.x
end

function TextEncoders.TextEncodeBase.splitting(::ExpCoderTokenization, x::Sentence{S}) where {S<:Program}
    return tokenize(TextEncoders.TextEncodeBase.getvalue(x))
end

function TextEncoders.TextEncodeBase.splitting(::ExpCoderTokenization, x::Sentence{String})
    return [TextEncoders.TextEncodeBase.getvalue(x)]
end

function TextEncoders.TextEncodeBase.splitting(::ExpCoderTokenization, x::Sentence)
    return tokenize(TextEncoders.TextEncodeBase.getmeta(x).tp, TextEncoders.TextEncodeBase.getvalue(x).value)
end

function TextEncoders.TextEncodeBase.wrap(::solver.ExpCoderTokenization, ::Batch{S}, ::TokenStages) where {S}
    error("Inaccessible")
end

function TextEncoders.TextEncodeBase.wrap(::ExpCoderTokenization, b::Batch{S}, x) where {S}
    S(x, TextEncoders.TextEncodeBase.getmeta(b))
end

function TextEncoders.TextEncodeBase.wrap(::ExpCoderTokenization, b::Batch{S}, x::Tuple) where {S}
    S([ValueWrapper(v) for v in x[2]], merge(TextEncoders.TextEncodeBase.getmeta(b), (tp = x[1],)))
end

function TextEncoders.TextEncodeBase.wrap(::ExpCoderTokenization, b::Batch{S}, x::Dict) where {S}
    S(collect(values(x)), TextEncoders.TextEncodeBase.getmeta(b))
end

TextEncoders.TextEncodeBase.wrap(::ExpCoderTokenization, b::Sentence, t) =
    Token(t, TextEncoders.TextEncodeBase.getmeta(b).is_batch)
TextEncoders.TextEncodeBase.wrap(::ExpCoderTokenization, ::Sentence, t::TokenStages) = t
TextEncoders.TextEncodeBase.wrap(::ExpCoderTokenization, t::TokenStage) = t

_is_in_batch(token::Token) = TextEncoders.TextEncodeBase.getmeta(token)
_is_in_batch(tokens) = _is_in_batch(tokens[1])

function _make_next_mask(next_masks)
    next_count = sum(max(length(m), 1) for m in next_masks)
    next_mask = zeros(Float32, next_count, length(next_masks))

    i = 1
    for (j, m) in enumerate(next_masks)
        if isempty(m)
            next_mask[i, j] = 1
            i += 1
        else
            next_mask[i:i+length(m)-1, j] = m
            i += length(m)
        end
    end
    return next_mask
end

function _subbatch_masks(tokens::Vector{<:AbstractString})
    return []
end

function _subbatch_masks(tokens::Vector{TokenStage})
    if typeof(tokens[1]) <: Token{String}
        return []
    end
    batch_size = length(tokens)
    cur_m = fill(1 / Float32(batch_size), batch_size)
    next_masks = [_subbatch_masks(TextEncoders.TextEncodeBase.getvalue(t)) for t in tokens]
    if all(isempty, next_masks)
        return cur_m
    end

    return _make_next_mask(next_masks) * cur_m
end

function _subbatch_masks(tokens)
    batch_size = length(tokens)
    cur_m = fill(1 / Float32(batch_size), batch_size)
    next_masks = [_subbatch_masks(t) for t in tokens]
    if all(isempty, next_masks)
        return cur_m
    end

    return _make_next_mask(next_masks) * cur_m
end

function subbatch_masks(tokens)
    if !_is_in_batch(tokens)
        return _subbatch_masks(tokens)
    else
        next_masks = [_subbatch_masks(t) for t in tokens]
        return _make_next_mask(next_masks)
    end
end

function flatten_tokens(tokens::Vector{<:AbstractString})
    return [[Token(t) for t in tokens]]
end

function flatten_tokens(tokens::Vector{TokenStage})
    if typeof(tokens[1]) <: Token{String}
        return [tokens]
    end
    return vcat([flatten_tokens(TextEncoders.TextEncodeBase.getvalue(t)) for t in tokens]...)
end

function flatten_tokens(tokens)
    vcat([flatten_tokens(t) for t in tokens]...)
end

struct Embedder
    encoder::Any
end

using Transformers.HuggingFace: bert_ones_like

using Transformers.Layers:
    ApplyEmbed, CompositeEmbedding, Embed, LayerNorm, SinCosPositionEmbed, TransformerBlock, DropoutLayer

function Embedder()
    encoder = Chain(
        CompositeEmbedding(
            token = Embed(d_emb, length(vocab) + 4),
            position = ApplyEmbed(.+, SinCosPositionEmbed(d_emb)),
            segment = ApplyEmbed(.+, Embed(d_emb, 2), bert_ones_like),
        ),
        DropoutLayer(LayerNorm(d_emb, ϵ = 1.0e-12), nothing),
        Transformer(TransformerBlock, 2, head_num, d_emb, d_emb ÷ head_num, d_emb),
    )

    return Embedder(encoder)
end

function (e::Embedder)(inputs)
    outputs = e.encoder(inputs)
    while any(isnan, outputs.hidden_state)
        error("NaN detected in encoder output")
    end

    pooled = outputs.hidden_state[:, 1, :]

    return pooled * outputs.subbatch_mask
end

function Base.show(io::IO, e::Embedder)
    print(io, "Embedder(", e.encoder, ")")
end
Flux.@layer :expand Embedder

struct GrammarEncoder end

function (m::GrammarEncoder)(func_encodings)
    grammar_encoding = sum(func_encodings, dims = 2) ./ size(func_encodings, 2)

    return grammar_encoding
end

Flux.@layer GrammarEncoder

struct InputOutputEncoder
    chain::Chain
    linear1::Dense
    linear2::Dense
end

hidden_channels = 32
d_emb_in = hidden_channels * 3 * 3

function InputOutputEncoder()
    chain = Chain(
        Conv((3, 3), 10 => hidden_channels, relu; pad = SamePad()),
        Conv((3, 3), hidden_channels => hidden_channels, relu; pad = SamePad()),
        Conv((3, 3), hidden_channels => hidden_channels, relu; pad = SamePad()),
        Conv((3, 3), hidden_channels => hidden_channels, relu; pad = SamePad()),
        AdaptiveMeanPool((3, 3)),
    )
    linear1 = Dense(d_emb_in, d_emb, relu)
    linear2 = Dense(d_emb, d_emb, relu)
    return InputOutputEncoder(chain, linear1, linear2)
end

function (m::InputOutputEncoder)(inputs, subbatch_mask)
    convoluted = Flux.MLUtils.flatten(m.chain(inputs))
    l1 = m.linear1(convoluted)
    batched = l1 * subbatch_mask
    return m.linear2(batched)
end

Flux.@layer :expand InputOutputEncoder

mutable struct NNGuidingModel
    preprocessor::Any

    embedder::Embedder
    grammar_encoder::GrammarEncoder
    input_output_encoder::InputOutputEncoder

    state_processor::Chain
    decoder::Chain

    grammar_cache::Any
end

function _create_tokenizer_process(e)
    tail = e.process.pipes[2:end-1]
    p =
        TextEncoders.Pipeline{:subbatch_mask}(subbatch_masks, 1) |>
        TextEncoders.Pipeline{:token}(flatten_tokens, 1) |>
        TextEncoders.Pipeline{:token}(TextEncoders.TextEncodeBase.nestedcall(TextEncoders.string_getvalue), :token)
    for t in tail
        p = p |> t
    end
    return p |> TextEncoders.PipeGet{(:token, :attention_mask, :sequence_mask, :subbatch_mask)}()
end

function NNGuidingModel()
    enable_gpu()
    embedder = Embedder() |> todevice
    grammar_encoder = GrammarEncoder() |> todevice
    input_output_encoder = InputOutputEncoder() |> todevice
    state_processor =
        Chain(
            Dense(d_state_in, d_state_h, relu),
            Dense(d_state_h, d_state_h, relu),
            Dense(d_state_h, d_state_out, relu),
        ) |> todevice
    decoder = Chain(Dense(d_state_out + d_emb, d_dec_h, relu), Dense(d_dec_h, 1)) |> todevice
    return NNGuidingModel(
        Preprocessor(),
        embedder,
        grammar_encoder,
        input_output_encoder,
        state_processor,
        decoder,
        nothing,
    )
end

function (m::NNGuidingModel)(grammar_func_encodings, grammar_encodings, input_batch)
    inputs, outputs, trace_val_tokens, is_reversed = input_batch
    trace_val_encodings = m.embedder(trace_val_tokens)
    input_encodings = m.input_output_encoder(inputs...)
    output_encodings = m.input_output_encoder(outputs...)

    state_emb = vcat(
        repeat(grammar_encodings, 1, size(input_encodings, 2)),
        input_encodings,
        output_encodings,
        trace_val_encodings,
        is_reversed,
    )
    state = m.state_processor(state_emb)
    broadcasted_state =
        repeat(reshape(state, size(state, 1), 1, size(state)[2:end]...), 1, size(grammar_func_encodings, 2))
    broadcasted_f_emb = repeat(grammar_func_encodings, 1, 1, size(state, 2))
    result = m.decoder(vcat(broadcasted_state, broadcasted_f_emb))
    return reshape(result, size(result)[2:end]...)
end

function clear_model_cache(m::NNGuidingModel)
    m.grammar_cache = nothing
end

function set_current_grammar!(m::NNGuidingModel, grammar)
    full_grammar = vcat(grammar, [Index(0), "lambda", FreeVar(t0, UInt64(1), nothing)])
    grammar_tokens = _preprocess_value(m.preprocessor, full_grammar) |> todevice
    grammar_func_encodings = m.embedder(grammar_tokens)
    grammar_encodings = m.grammar_encoder(grammar_func_encodings)
    m.grammar_cache = (grammar_func_encodings, grammar_encodings)
end

Flux.trainable(m::NNGuidingModel) = (
    embedder = m.embedder,
    input_output_encoder = m.input_output_encoder,
    state_processor = m.state_processor,
    decoder = m.decoder,
)

Flux.@layer :expand NNGuidingModel

function _extract_program_blocks(p::LetRevClause, blocks)
    push!(blocks, (p.inp_var_id, p.v, true))
    return _extract_program_blocks(p.b, blocks)
end

function _extract_program_blocks(p::LetClause, blocks)
    push!(blocks, (p.var_id, p.v, false))
    return _extract_program_blocks(p.b, blocks)
end

function _extract_program_blocks(p::FreeVar, blocks)
    return blocks
end

function _extract_program_blocks(p, blocks)
    push!(blocks, ("output", p, false))
    return blocks
end

function extract_program_blocks(program_str)
    p = parse_program(program_str)
    return _extract_program_blocks(p, [])
end

mutable struct LikelihoodSummary
    uses::Dict
    normalizers::Dict
    constant::Float32
end

function LikelihoodSummary()
    return LikelihoodSummary(Dict(), Dict(), 0.0)
end

function _build_likelihood_summary(
    grammar,
    full_p,
    request,
    p::SetConst,
    context,
    environment,
    checker,
    path,
    locations,
    var_types,
    summary,
)
    return context, summary
end

function _build_likelihood_summary(
    grammar,
    full_p,
    request,
    p,
    context,
    environment,
    checker,
    path,
    locations,
    var_types,
    summary,
)
    if isarrow(request)
        if !isa(p, Abstraction)
            error("Expected abstraction, got $p")
        end
        return _build_likelihood_summary(
            grammar,
            full_p,
            request.arguments[2],
            p.b,
            context,
            vcat([request.arguments[1]], environment),
            step_arg_checker(checker, ArgTurn(request.arguments[1])),
            vcat(path, [ArgTurn(request.arguments[1])]),
            locations,
            var_types,
            summary,
        )
    end

    f, xs = application_parse(p)

    candidates = []
    next_requests = nothing

    if length(path) >= 2 && isa(path[end], ArgTurn) && isa(path[end-1], LeftTurn)
        in_lambda_wrapper = true
    else
        in_lambda_wrapper = false
    end

    for (i, p) in enumerate(grammar)
        if in_lambda_wrapper && p != every_primitive["rev_fix_param"]
            continue
        end

        for (f, ind) in locations
            if violates_symmetry(f, p, ind)
                continue
            end
        end

        if !checker(p, full_p, path)
            continue
        end

        if might_unify(return_of_type(p.t), request)
            new_context, t = instantiate(p.t, context)
            new_context = unify(new_context, return_of_type(t), request)
            if isnothing(new_context)
                continue
            end
            push!(candidates, i)
            if p == f
                summary.uses[i] = get(summary.uses, i, 0) + 1

                (new_context, t) = apply_context(new_context, t)
                next_requests = (arguments_of_type(t), new_context)
            end
        end
    end

    grammar_length = length(grammar)

    if !isempty(candidates)
        lambda_context, arg_type = instantiate(t0, context)
        lambda_context, lambda_type = apply_context(lambda_context, request)
        push!(candidates, grammar_length + 2)

        if isa(f, Abstraction)
            summary.uses[grammar_length+2] = get(summary.uses, grammar_length + 2, 0) + 1
            next_requests = ([lambda_type, arg_type], lambda_context)
        end
    end

    if !in_lambda_wrapper
        variable_candidates = 0
        is_index = false
        for (j, t) in enumerate(environment)
            p = Index(j - 1)
            if !checker(p, full_p, path)
                continue
            end
            (new_context, t) = apply_context(context, t)
            return_type = return_of_type(t)
            if might_unify(return_type, request)
                new_context = unify(new_context, return_type, request)
                if isnothing(new_context)
                    continue
                end
                variable_candidates += 1

                if p == f
                    is_index = true
                    summary.uses[grammar_length+1] = get(summary.uses, grammar_length + 1, 0) + 1

                    (new_context, t) = apply_context(new_context, t)
                    next_requests = (arguments_of_type(t), new_context)
                end
            end
        end
        if variable_candidates > 0
            push!(candidates, grammar_length + 1)
            if is_index
                summary.constant -= log(variable_candidates)
            end
        end
    end

    if checker.can_have_free_vars
        free_var_candidates = 0
        is_free_var = false

        for (var_id, t) in var_types
            (new_context, t) = apply_context(context, t)
            return_type = return_of_type(t)
            if might_unify(return_type, request)
                new_context = unify(new_context, return_type, request)
                if isnothing(new_context)
                    continue
                end
                free_var_candidates += 1
                if isa(f, FreeVar) && f.var_id == var_id
                    (new_context, t) = apply_context(new_context, t)
                    var_types[f.var_id] = t
                    is_free_var = true
                    next_requests = ([], new_context)
                end
            end
        end

        if !isa(full_p, FreeVar)
            p = FreeVar(request, nothing, isempty(locations) ? nothing : locations[1])
            if checker(p, full_p, path)
                free_var_candidates += 1
                if isa(f, FreeVar) && !haskey(var_types, f.var_id)
                    var_types[f.var_id] = request
                    is_free_var = true
                    next_requests = ([], context)
                end
            end
        end

        if free_var_candidates > 0
            push!(candidates, grammar_length + 3)
            if is_free_var
                summary.uses[grammar_length+3] = get(summary.uses, grammar_length + 3, 0) + 1
                summary.constant -= log(free_var_candidates)
            end
        end
    end

    if isnothing(next_requests)
        error("$f is not in possible candidates for $request")
    end

    summary.normalizers[candidates] = get(summary.normalizers, candidates, 0) + 1

    arg_types = next_requests[1]
    context = next_requests[2]

    if isa(f, Abstraction)
        context, summary = _build_likelihood_summary(
            grammar,
            full_p,
            arg_types[1],
            f.b,
            context,
            vcat([arg_types[2]], environment),
            step_arg_checker(checker, ArgTurn(arg_types[2])),
            vcat(path, [LeftTurn(), ArgTurn(arg_types[2])]),
            locations,
            var_types,
            summary,
        )
        return _build_likelihood_summary(
            grammar,
            full_p,
            arg_types[2],
            xs[1],
            context,
            environment,
            checker,
            vcat(path, [RightTurn()]),
            [],
            var_types,
            summary,
        )
    end

    if !isempty(arg_types)
        custom_arg_checkers = _get_custom_arg_checkers(f)
        custom_checkers_args_count = length(custom_arg_checkers)

        for (i, (arg_type, x)) in enumerate(zip(arg_types, xs))
            current_checker = step_arg_checker(checker, (f, i))

            if i > custom_checkers_args_count || isnothing(custom_arg_checkers[i])
                arg_checker = current_checker
            else
                arg_checker = combine_arg_checkers(current_checker, custom_arg_checkers[i])
            end

            context, summary = _build_likelihood_summary(
                grammar,
                full_p,
                arg_type,
                x,
                context,
                environment,
                arg_checker,
                vcat(path, [LeftTurn() for _ in i+1:length(xs)], [RightTurn()]),
                [(f, i)],
                var_types,
                summary,
            )
        end
    end
    return context, summary
end

function _preprocess_summary(summary::LikelihoodSummary, grammar_length)
    uses = zeros(Float32, grammar_length)
    for (i, count) in summary.uses
        uses[i] = count
    end
    mask = fill(-Inf32, grammar_length, length(summary.normalizers))
    N = zeros(Float32, length(summary.normalizers))
    for (i, (norm_set, count)) in enumerate(summary.normalizers)
        N[i] = count
        mask[norm_set, i] .= 0
    end
    return (uses, mask, N, summary.constant)
end

function build_likelihood_summary(grammar, request, p, is_reversed)
    summary = LikelihoodSummary()
    context, request = instantiate(request, empty_context)
    _, summary = _build_likelihood_summary(
        grammar,
        p,
        request,
        p,
        context,
        [],
        CombinedArgChecker([SimpleArgChecker(is_reversed, -1, true)]),
        [],
        [],
        Dict(),
        summary,
    )
    return _preprocess_summary(summary, length(grammar) + 3)
end

using Flux: DataLoader

function lookup(e, x::NamedTuple{name}) where {name}
    xt = Tuple(x)
    return NamedTuple{name}((TextEncoders.lookup(getfield(e, :vocab), xt[1]), Base.tail(xt)...))
end

struct Preprocessor
    tokenizer::Any
    tokenizer_cache::Any
    inputs_cache::Any
    output_cache::Any
end

function Preprocessor()
    tokenizer = TransformerTextEncoder(ExpCoderTokenization(), vocab)
    tokenizer = TextEncoders.set_annotate(_ -> solver.annotate_objects, tokenizer)
    tokenizer = TextEncoders.set_process(_create_tokenizer_process, tokenizer)
    return Preprocessor(tokenizer, Dict(), Dict(), Dict())
end

function _preprocess_value(p::Preprocessor, val)
    if !haskey(p.tokenizer_cache, val)
        p.tokenizer_cache[val] = Transformers.encode(p.tokenizer, val)
    end
    return p.tokenizer_cache[val]
end

using Flux.OneHotArrays: onehotbatch

function _preprocess_inputs(p::Preprocessor, inputs)
    if !haskey(p.inputs_cache, inputs)
        var_count = length(inputs)
        example_count = length(inputs[1])
        subbatch_mask = fill(1 / (example_count * var_count), example_count * var_count, 1)

        max_x = maximum(size(v, 1) for var in inputs for v in var; init = 3)
        max_y = maximum(size(v, 2) for var in inputs for v in var; init = 3)
        input_matrix = fill(10, max_x, max_y, example_count * var_count)
        i = 1
        for var_examples in inputs
            for example in var_examples
                k, l = size(example)
                input_matrix[1:k, 1:l, i] = example
                i += 1
            end
        end
        input_batch = onehotbatch(input_matrix, 0:10)[1:10, :, :, :]
        input_batch = permutedims(input_batch, [2, 3, 1, 4])
        p.inputs_cache[inputs] = input_batch, subbatch_mask
    end
    return p.inputs_cache[inputs]
end

function _preprocess_input_batch(p::Preprocessor, inputs)
    batch_size = length(inputs)

    processed_inputs = [_preprocess_inputs(p, i) for i in inputs]

    example_count = sum(m -> length(m[2]), processed_inputs)

    input_subbatch_mask = zeros(Float32, example_count, batch_size)

    max_x = maximum(size(v, 1) for (v, _) in processed_inputs; init = 3)
    max_y = maximum(size(v, 2) for (v, _) in processed_inputs; init = 3)
    input_batch_matrix = fill(false, max_x, max_y, 10, example_count)

    i = 1
    for (j, (input_matrix, subbatch_mask)) in enumerate(processed_inputs)
        input_subbatch_mask[i:i+length(subbatch_mask)-1, j] = subbatch_mask
        input_batch_matrix[1:size(input_matrix, 1), 1:size(input_matrix, 2), :, i:i+length(subbatch_mask)-1] =
            input_matrix
        i += length(subbatch_mask)
    end
    return input_batch_matrix, input_subbatch_mask
end

function _preprocess_output_batch(p::Preprocessor, outputs)
    batch_size = length(outputs)
    processed_outputs = [_preprocess_output(p, o) for o in outputs]
    example_count = sum(m -> length(m[2]), processed_outputs)
    output_subbatch_mask = zeros(Float32, example_count, batch_size)

    max_x = maximum(size(v, 1) for (v, _) in processed_outputs; init = 3)
    max_y = maximum(size(v, 2) for (v, _) in processed_outputs; init = 3)
    output_batch_matrix = fill(false, max_x, max_y, 10, example_count)

    i = 1
    for (j, (output_matrix, subbatch_mask)) in enumerate(processed_outputs)
        output_subbatch_mask[i:i+length(subbatch_mask)-1, j] = subbatch_mask
        output_batch_matrix[1:size(output_matrix, 1), 1:size(output_matrix, 2), :, i:i+length(subbatch_mask)-1] =
            output_matrix
        i += length(subbatch_mask)
    end
    return output_batch_matrix, output_subbatch_mask
end

function _preprocess_output(p::Preprocessor, output)
    if !haskey(p.output_cache, output)
        example_count = length(output)
        subbatch_mask = fill(1 / (example_count), example_count, 1)

        max_x = maximum(size(v, 1) for v in output; init = 3)
        max_y = maximum(size(v, 2) for v in output; init = 3)
        output_matrix = fill(10, max_x, max_y, example_count)
        for (j, example) in enumerate(output)
            k, l = size(example)
            output_matrix[1:k, 1:l, j] = example
        end
        output_batch = onehotbatch(output_matrix, 0:10)[1:10, :, :, :]
        output_batch = permutedims(output_batch, [2, 3, 1, 4])
        p.output_cache[output] = output_batch, subbatch_mask
    end
    return p.output_cache[output]
end

struct DataBlock
    preprocessor::Any
    grammar::Any
    values::Any
    labels::Any
    cache::Dict

    function DataBlock(preprocessor, grammar, values, labels)
        return new(preprocessor, grammar, values, labels, Dict())
    end
end

Base.length(d::DataBlock) = length(d.values)

function Base.getindex(d::DataBlock, i::Int)
    if !haskey(d.cache, i)
        inputs, outputs, trace_val, is_rev = d.values[i]

        is_rev_shaped = [is_rev]
        uses, mask, N, constant = d.labels[i]
        constant = [constant]
        d.cache[i] = (
            (
                _preprocess_value(d.preprocessor, d.grammar),
                _preprocess_inputs(d.preprocessor, inputs),
                _preprocess_output(d.preprocessor, outputs),
                _preprocess_value(d.preprocessor, trace_val),
                is_rev_shaped,
            ),
            (uses, mask, N, constant),
        )
    end
    return d.cache[i]
end

function Base.getindex(d::DataBlock, ind)
    if !haskey(d.cache, ind)
        inputs, outputs, trace_val, is_rev = zip(d.values[ind]...)

        is_rev_shaped = reshape(collect(is_rev), 1, :)
        uses, mask, N, constant = zip(d.labels[ind]...)
        uses = hcat(uses...)
        max_norm_count = maximum(length, N)
        merged_mask = zeros(Float32, length(d.grammar), max_norm_count, length(N))
        merged_N = zeros(Float32, max_norm_count, length(N))
        for (i, counts) in enumerate(N)
            merged_N[1:length(counts), i] = counts
            merged_mask[:, 1:length(counts), i] = mask[i]
        end

        constant = reshape(collect(constant), 1, :)

        d.cache[ind] = (
            (
                _preprocess_value(d.preprocessor, d.grammar),
                _preprocess_input_batch(d.preprocessor, inputs),
                _preprocess_output_batch(d.preprocessor, outputs),
                _preprocess_value(d.preprocessor, collect(trace_val)),
                is_rev_shaped,
            ),
            (uses, merged_mask, merged_N, constant),
        )
    end
    return d.cache[ind]
end

function _preprocess_model_inputs(m::NNGuidingModel, batch)
    inputs, outputs, trace_val, is_reversed = batch
    return (
        _preprocess_input_batch(m.preprocessor, inputs),
        _preprocess_output_batch(m.preprocessor, outputs),
        _preprocess_value(m.preprocessor, trace_val),
        is_reversed,
    )
end

function expand_traces(all_traces, preprocessor, batch_size = 1)
    groups = []

    for (grammar, gr_traces) in values(all_traces)
        full_grammar = vcat(grammar, [Index(0), "lambda", FreeVar(t0, UInt64(1), nothing)])

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
                    push!(X_data, (inputs, outputs, trace_val, is_rev))
                    push!(summaries, summary)
                end
            end
        end
        if !isempty(X_data)
            push!(
                groups,
                DataLoader(
                    DataBlock(preprocessor, full_grammar, X_data, summaries),
                    batchsize = batch_size,
                    parallel = true,
                ),
            )
        end
    end
    return groups
end

using Statistics
function loss(result, summary)
    uses, mask, N, constant = summary
    uses = uses
    mask = mask
    N = N
    constant = constant

    numenator = sum(result .* uses, dims = 1) .+ constant

    z = (mask .+ repeat(reshape(result, size(result, 1), 1, size(result)[2:end]...), 1, size(mask, 2), 1))
    z = logsumexp(z, dims = 1)
    z = reshape(z, size(z)[2:end]...)

    denominator = sum(N .* z, dims = 1)

    return mean(denominator .- numenator)
end

using ProgressMeter

function update_guiding_model(guiding_model::NNGuidingModel, traces)
    train_set = expand_traces(traces, guiding_model.preprocessor, 32)
    if isempty(train_set)
        return guiding_model
    end

    opt_state = Flux.setup(Adam(0.001, (0.9, 0.999), 1e-8), guiding_model)

    train_set_size = sum(length, train_set)
    epochs = 10
    for e in 1:epochs
        p = Progress(train_set_size)
        losses = Float32[]

        for (i, data_group) in enumerate(train_set)
            for (j, batch) in enumerate(data_group)
                # Unpack this element (for supervised training):
                inputs, summaries = batch |> todevice

                # Calculate the gradient of the objective
                # with respect to the parameters within the model:
                loss_val, grads = Flux.withgradient(guiding_model) do m
                    grammar_func_encodings = m.embedder(inputs[1])
                    grammar_encodings = m.grammar_encoder(grammar_func_encodings)
                    result = m(grammar_func_encodings, grammar_encodings, inputs[2:end])
                    loss(result, summaries)
                end
                push!(losses, loss_val)

                if !isfinite(loss_val)
                    @warn "loss is $loss_val on item $i $j"
                else
                    # Update the parameters so as to reduce the objective,
                    # according the chosen optimisation rule:
                    Flux.update!(opt_state, guiding_model, grads[1])
                end
                next!(p, showvalues = [("loss", loss_val)])
            end
        end
        finish!(p)
        @info "Average loss for epoch $e: $(mean(losses))"
    end

    return guiding_model
end

function get_encoded_value_length(model::NNGuidingModel, max_summary)
    sum(token_weights[tname] * count for (tname, count) in max_summary; init = 0)
end

function split_model_inputs(model_inputs)
    grammar, inputs, outputs, trace_val, is_reversed = model_inputs
    new_batch_size = ceil(Int, length(is_reversed) / 2)
    b1 = (
        grammar,
        inputs[1:new_batch_size],
        outputs[1:new_batch_size],
        trace_val[1:new_batch_size],
        is_reversed[:, 1:new_batch_size],
    )
    b2 = (
        grammar,
        inputs[new_batch_size+1:end],
        outputs[new_batch_size+1:end],
        trace_val[new_batch_size+1:end],
        is_reversed[:, new_batch_size+1:end],
    )
    return [b1, b2]
end

function run_guiding_model(guiding_model::NNGuidingModel, model_inputs)
    times = Dict()
    start = time()
    preprocessed_inputs = _preprocess_model_inputs(guiding_model, model_inputs[1:4]) |> todevice
    times["preprocessing"] = time() - start
    start = time()
    result = try
        grammar_func_encodings, grammar_encodings = guiding_model.grammar_cache
        guiding_model(grammar_func_encodings, grammar_encodings, preprocessed_inputs) |> cpu
    catch e
        @error size(preprocessed_inputs[3].token)
        # if isa(e, CUDNNError) && length(model_inputs[end]) > 1
        #     @error "Splitting batch due to CUDA error"
        #     batches = split_model_inputs(model_inputs)
        #     hcat([run_guiding_model(guiding_model, b)[2] for b in batches]...)
        # else
        rethrow()
        # end
    end
    return time() - start, times, result
end
