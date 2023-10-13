
all_abstractors = Dict{Program,Tuple{Vector,Any}}()

function _get_custom_arg_checkers(p::Primitive)
    if haskey(all_abstractors, p)
        [c[2] for c in all_abstractors[p][1]]
    else
        []
    end
end

_get_custom_arg_checkers(p::Index) = []
_get_custom_arg_checkers(p::FreeVar) = []

function _get_custom_arg_checkers(p::Invented)
    checkers, indices_checkers = __get_custom_arg_chekers(p, nothing, Dict())
    @assert isempty(indices_checkers)
    return checkers
end

function __get_custom_arg_chekers(p::Primitive, checker::Nothing, indices_checkers::Dict)
    if haskey(all_abstractors, p)
        all_abstractors[p][1], indices_checkers
    else
        [], indices_checkers
    end
end

function __get_custom_arg_chekers(p::Primitive, checker, indices_checkers::Dict)
    arg_count = length(arguments_of_type(p.t))
    if haskey(all_abstractors, p)
        custom_checkers = all_abstractors[p][1]
        out_checkers = []
        for c in custom_checkers
            if c[2] == checker
                push!(out_checkers, c[2])
            else
                combined = (args...) -> c[2](args...) && checker(args...)
                push!(out_checkers, combined)
            end
        end
        for _ in 1:arg_count-length(custom_checkers)
            push!(out_checkers, checker)
        end
        out_checkers, indices_checkers
    else
        [checker for _ in 1:arg_count], indices_checkers
    end
end

function __get_custom_arg_chekers(p::Invented, checker, indices_checkers::Dict)
    return __get_custom_arg_chekers(p.b, checker, indices_checkers)
end

function __get_custom_arg_chekers(p::Apply, checker, indices_checkers::Dict)
    checkers, indices_checkers = __get_custom_arg_chekers(p.f, checker, indices_checkers)
    if !isempty(checkers)
        arg_checkers, indices_checkers = __get_custom_arg_chekers(p.x, checkers[1], indices_checkers)
    else
        arg_checkers, indices_checkers = __get_custom_arg_chekers(p.x, nothing, indices_checkers)
    end
    @assert isempty(arg_checkers)
    out_checkers = checkers[2:end]
    return out_checkers, indices_checkers
end

function __get_custom_arg_chekers(p::Index, checker::Nothing, indices_checkers::Dict)
    return [], indices_checkers
end

function __get_custom_arg_chekers(p::Index, checker, indices_checkers::Dict)
    if haskey(indices_checkers, p.n)
        if indices_checkers[p.n] == checker
            return [], indices_checkers
        else
            combined = (args...) -> indices_checkers[p.n](args...) && checker(args...)
            indices_checkers[p.n] = combined
            return [], indices_checkers
        end
    else
        indices_checkers[p.n] = checker
        return [], indices_checkers
    end
end

function __get_custom_arg_chekers(p::Abstraction, checker::Nothing, indices_checkers::Dict)
    chekers, indices_checkers = __get_custom_arg_chekers(p.b, checker, Dict(i + 1 => c for (i, c) in indices_checkers))
    if haskey(indices_checkers, 0)
        out_checkers = vcat([indices_checkers[0]], chekers)
    elseif !isempty(chekers)
        out_checkers = vcat([nothing], chekers)
    else
        out_checkers = []
    end
    return out_checkers, Dict(i - 1 => c for (i, c) in indices_checkers if i > 0)
end

function _is_reversible(p::Primitive)
    if haskey(all_abstractors, p)
        all_abstractors[p][1]
    else
        nothing
    end
end

function _is_reversible(p::Apply)
    rev_f = _is_reversible(p.f)
    if !isnothing(rev_f)
        if isempty(rev_f)
            if isa(p.x, Hole)
                if !isarrow(p.x.t)
                    return rev_f
                else
                    return nothing
                end
            end
            if isa(p.x, Index) || isa(p.x, FreeVar)
                return rev_f
            end
            if isa(p.x, Abstraction) || isa(p.x, Apply)
                return _is_reversible(p.x)
            end
        else
            checker = rev_f[1][1]
            if checker(p.x)
                return view(rev_f, 2:length(rev_f))
            else
                return nothing
            end
        end
    end
    nothing
end

_is_reversible(p::Invented) = _is_reversible(p.b)
_is_reversible(p::Abstraction) = _is_reversible(p.b)

_is_reversible(p::Program) = nothing

is_reversible(p::Program)::Bool = !isnothing(_is_reversible(p))

struct SkipArg end

mutable struct ReverseRunContext
    arguments::Vector{Any}
    predicted_arguments::Vector{Any}
    calculated_arguments::Vector{Any}
    filled_indices::Dict{Int64,Any}
    filled_vars::Dict{UInt64,Any}
end

ReverseRunContext() = ReverseRunContext([], [], [], Dict(), Dict())

function _merge_options_paths(path1, path2)
    i = 1
    j = 1
    result = []
    while i <= length(path1) || j <= length(path2)
        if i > length(path1)
            push!(result, path2[j])
            j += 1
        elseif j > length(path2)
            push!(result, path1[i])
            i += 1
        elseif path1[i] == path2[j]
            push!(result, path1[i])
            i += 1
            j += 1
        else
            push!(result, path1[i])
            i += 1
        end
    end
    return result
end

function _intersect_values(
    old_v,
    v,
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    if old_v != v
        error("Can't intersect values $old_v and $v")
    end
    return v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    old_v::Union{AbductibleValue,AnyObject},
    v,
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    return v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    old_v,
    v::Union{AbductibleValue,AnyObject},
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    return old_v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    old_v::AbductibleValue,
    v::Union{AbductibleValue,AnyObject},
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    return old_v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    old_v::Union{AbductibleValue,AnyObject},
    v::AbductibleValue,
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    return v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    old_v::Union{AbductibleValue,AnyObject},
    v::EitherOptions,
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    return v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    old_v::EitherOptions,
    v::Union{AbductibleValue,AnyObject},
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    return old_v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

_unify_values(v1, v2::AnyObject) = v1
_unify_values(v1::AnyObject, v2) = v2
_unify_values(v1::AnyObject, v2::AnyObject) = v2

function _unify_values(v1::EitherOptions, v2::EitherOptions)
    options = Dict()
    for (h, v) in v1.options
        if haskey(v2.options, h)
            options[h] = _unify_values(v, v2.options[h])
        end
    end
    return EitherOptions(options)
end

function _unify_values(v1, v2)
    if v1 == v2
        return v1
    end
    error("Incompatible values")
end

function _intersect_values(
    old_v::EitherOptions,
    v::EitherOptions,
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    if old_v == v
        return predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
    end
    # @info old_v
    # @info v
    old_options = Set(_const_options(old_v))
    new_options = Set(_const_options(v))
    common_options = intersect(old_options, new_options)
    paths = Set()
    # @info common_options
    for op in common_options
        # @info op
        old_op_fixed_hashes = Set()
        new_op_fixed_hashes = Set()
        try
            while true
                old_op_fixed_hashes_ = get_intersecting_hashes(old_v, op, new_op_fixed_hashes)

                new_op_fixed_hashes_ = get_intersecting_hashes(v, op, old_op_fixed_hashes_)
                if old_op_fixed_hashes_ == old_op_fixed_hashes && new_op_fixed_hashes_ == new_op_fixed_hashes
                    break
                end
                old_op_fixed_hashes = old_op_fixed_hashes_
                new_op_fixed_hashes = new_op_fixed_hashes_
            end
            # @info old_op_fixed_hashes
            # @info new_op_fixed_hashes
            old_op_hashes_paths = get_hashes_paths(old_v, op, new_op_fixed_hashes)
            # @info old_op_hashes_paths

            for old_path in old_op_hashes_paths
                # @info old_path
                new_op_hashes_paths = get_hashes_paths(v, op, old_path)
                # @info new_op_hashes_paths
                for new_path in new_op_hashes_paths
                    push!(paths, _merge_options_paths(old_path, new_path))
                end
            end
        catch e
            if isa(e, InterruptException)
                rethrow()
            end
        end
    end
    if isempty(common_options) || isempty(paths)
        error("No common options")
    end
    # @info paths
    # @info predicted_arguments
    predicted_arguments = [remap_options_hashes(paths, arg) for arg in predicted_arguments]
    filled_indices = Dict{Int64,Any}(i => remap_options_hashes(paths, v) for (i, v) in filled_indices)
    filled_vars = Dict{UInt64,Any}(k => remap_options_hashes(paths, v) for (k, v) in filled_vars)

    new_args = [remap_options_hashes(paths, arg) for arg in new_args]
    new_filled_indices = Dict{Int64,Any}(i => remap_options_hashes(paths, v) for (i, v) in new_filled_indices)
    new_filled_vars = Dict{UInt64,Any}(k => remap_options_hashes(paths, v) for (k, v) in new_filled_vars)

    r1 = remap_options_hashes(paths, v)
    r2 = remap_options_hashes(paths, old_v)
    # @info r1
    # @info r2
    # @info _unify_values(r1, r2)

    return _unify_values(r1, r2),
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars
end

function _intersect_values(
    old_v::EitherOptions,
    v,
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    fixed_hashes = get_fixed_hashes(old_v, v)

    predicted_arguments = [fix_option_hashes(fixed_hashes, arg) for arg in predicted_arguments]
    filled_indices = Dict{Int64,Any}(i => fix_option_hashes(fixed_hashes, v) for (i, v) in filled_indices)
    filled_vars = Dict{UInt64,Any}(k => fix_option_hashes(fixed_hashes, v) for (k, v) in filled_vars)
    new_args = [fix_option_hashes(fixed_hashes, arg) for arg in new_args]
    new_filled_indices = Dict{Int64,Any}(i => fix_option_hashes(fixed_hashes, v) for (i, v) in new_filled_indices)
    new_filled_vars = Dict{UInt64,Any}(k => fix_option_hashes(fixed_hashes, v) for (k, v) in new_filled_vars)
    return v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    old_v,
    v::EitherOptions,
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    new_v, new_args, new_filled_indices, new_filled_vars, predicted_arguments, filled_indices, filled_vars =
        _intersect_values(
            v,
            old_v,
            new_args,
            new_filled_indices,
            new_filled_vars,
            predicted_arguments,
            filled_indices,
            filled_vars,
        )
    return new_v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _intersect_values(
    predicted_arguments,
    filled_indices,
    filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars,
)
    for (i, v) in new_filled_indices
        if haskey(filled_indices, i) && filled_indices[i] != v
            new_v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars =
                _intersect_values(
                    filled_indices[i],
                    v,
                    predicted_arguments,
                    filled_indices,
                    filled_vars,
                    new_args,
                    new_filled_indices,
                    new_filled_vars,
                )
            filled_indices[i] = new_v
            new_filled_indices[i] = new_v
        end
    end
    for (k, v) in new_filled_vars
        if haskey(filled_vars, k) && filled_vars[k] != v
            new_v, predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars =
                _intersect_values(
                    filled_vars[k],
                    v,
                    predicted_arguments,
                    filled_indices,
                    filled_vars,
                    new_args,
                    new_filled_indices,
                    new_filled_vars,
                )
            filled_vars[k] = new_v
            new_filled_vars[k] = new_v
        end
    end
    return predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars
end

function _run_in_reverse(p::Primitive, output, context)
    # @info "Running in reverse $p $output $context"
    calculated_output, new_context = all_abstractors[p][2](output, context)
    context.predicted_arguments,
    context.filled_indices,
    context.filled_vars,
    new_args,
    new_filled_indices,
    new_filled_vars = _intersect_values(
        context.predicted_arguments,
        context.filled_indices,
        context.filled_vars,
        new_context.predicted_arguments,
        new_context.filled_indices,
        new_context.filled_vars,
    )
    if !isempty(new_filled_indices)
        context.filled_indices = merge(context.filled_indices, new_filled_indices)
    end
    if !isempty(new_filled_vars)
        context.filled_vars = merge(context.filled_vars, new_filled_vars)
    end
    context.predicted_arguments = vcat(context.predicted_arguments, reverse(new_args))

    return calculated_output, context
end

function _run_in_reverse(p::Primitive, output::AbductibleValue, context)
    # @info "Running in reverse $p $output $context"
    for _ in 1:length(arguments_of_type(p.t))
        push!(context.predicted_arguments, output)
    end
    return output, context
end

function _preprocess_options(args_options, output)
    if any(isa(out, AbductibleValue) for out in values(args_options))
        abd = first(out for out in values(args_options) if isa(out, AbductibleValue))
        for (h, val) in args_options
            if !isa(val, AbductibleValue) && abd.value == val
                args_options[h] = abd
            end
        end
    end
    if any(out == output for out in values(args_options))
        return output
    else
        return EitherOptions(args_options)
    end
end

function _run_in_reverse(p::Primitive, output::EitherOptions, context)
    # @info "Running in reverse $p $output $context"
    output_options = Dict()
    arguments_options = Dict[]
    filled_indices_options = DefaultDict(() -> Dict())
    filled_vars_options = DefaultDict(() -> Dict())
    for (h, val) in output.options
        fixed_hashes = Set([h])
        op_calculated_arguments = [fix_option_hashes(fixed_hashes, v) for v in context.calculated_arguments]
        op_predicted_arguments = [fix_option_hashes(fixed_hashes, v) for v in context.predicted_arguments]
        op_filled_indices = Dict(i => fix_option_hashes(fixed_hashes, v) for (i, v) in context.filled_indices)
        op_filled_vars = Dict(k => fix_option_hashes(fixed_hashes, v) for (k, v) in context.filled_vars)

        calculated_output, new_context = _run_in_reverse(
            p,
            val,
            ReverseRunContext(
                context.arguments,
                op_predicted_arguments,
                op_calculated_arguments,
                op_filled_indices,
                op_filled_vars,
            ),
        )

        predicted_arguments_op, filled_indices_op, filled_vars_op, new_args, new_filled_indices, new_filled_vars =
            _intersect_values(
                op_predicted_arguments,
                op_filled_indices,
                op_filled_vars,
                new_context.predicted_arguments,
                new_context.filled_indices,
                new_context.filled_vars,
            )

        if isempty(arguments_options)
            for _ in 1:(length(new_args))
                push!(arguments_options, Dict())
            end
        end
        output_options[h] = calculated_output

        for i in 1:length(new_args)
            arguments_options[i][h] = new_args[i]
        end
        for (i, v) in filled_indices_op
            filled_indices_options[i][h] = v
        end
        for (k, v) in filled_vars_op
            filled_vars_options[k][h] = v
        end
        for (i, v) in new_filled_indices
            filled_indices_options[i][h] = v
        end
        for (k, v) in new_filled_vars
            filled_vars_options[k][h] = v
        end
    end

    out_args = []
    out_filled_indices = Dict()
    out_filled_vars = Dict()

    # @info arguments_options
    for args_options in arguments_options
        push!(out_args, _preprocess_options(args_options, output))
    end
    for (i, v) in filled_indices_options
        out_filled_indices[i] = _preprocess_options(v, output)
    end
    for (k, v) in filled_vars_options
        out_filled_vars[k] = _preprocess_options(v, output)
    end
    out_context = ReverseRunContext(
        context.arguments,
        out_args,
        context.calculated_arguments,
        out_filled_indices,
        out_filled_vars,
    )
    # @info "Output options $output_options"
    # @info "Output context $out_context"
    return EitherOptions(output_options), out_context
end

function _run_in_reverse(p::Primitive, output::PatternWrapper, context)
    # @info "Running in reverse $p $output $context"
    calculated_output, new_context = _run_in_reverse(p, output.value, context)

    predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars = _intersect_values(
        context.predicted_arguments,
        context.filled_indices,
        context.filled_vars,
        new_context.predicted_arguments,
        new_context.filled_indices,
        new_context.filled_vars,
    )
    if !isempty(new_filled_indices)
        context.filled_indices = merge(filled_indices, new_filled_indices)
    end
    if !isempty(new_filled_vars)
        context.filled_vars = merge(filled_vars, new_filled_vars)
    end

    context.predicted_arguments = [_wrap_wildcard(arg) for arg in new_args]

    return _wrap_wildcard(calculated_output), context
end

function _run_in_reverse(p::Primitive, output::Union{Nothing,AnyObject}, context)
    # @info "Running in reverse $p $output $context"
    try
        calculated_output, new_context = all_abstractors[p][2](output, context)
        predicted_arguments, filled_indices, filled_vars, new_args, new_filled_indices, new_filled_vars =
            _intersect_values(
                context.predicted_arguments,
                context.filled_indices,
                context.filled_vars,
                new_context.predicted_arguments,
                new_context.filled_indices,
                new_context.filled_vars,
            )
        if !isempty(new_filled_indices)
            context.filled_indices = merge(filled_indices, filled_indices)
        end
        if !isempty(new_filled_vars)
            context.filled_vars = merge(filled_vars, filled_vars)
        end
        context.predicted_arguments = vcat(predicted_arguments, reverse(new_args))
        return calculated_output, context
    catch e
        # @info e
        # bt = catch_backtrace()
        # @error e exception = (e, bt)
        if isa(e, MethodError)
            context.predicted_arguments =
                vcat(context.predicted_arguments, [output for _ in 1:length(arguments_of_type(p.t))])
            return output, context
        else
            rethrow()
        end
    end
end

function _run_in_reverse(p::Apply, output::AbductibleValue, context)
    # @info "Running in reverse $p $output $context"
    env = Any[nothing for _ in 1:maximum(keys(context.filled_indices); init = 0)]
    for (i, v) in context.filled_indices
        env[end-i] = v
    end
    try
        calculated_output = p(env, context.filled_vars)
        # @info calculated_output
        if calculated_output isa Function
            error("Function output")
        end
        return calculated_output, context
    catch e
        if e isa InterruptException
            rethrow()
        end
        return @invoke _run_in_reverse(p::Apply, output::Any, context)
    end
end

function _run_in_reverse(p::Apply, output, context)
    # @info "Running in reverse $p $output $context"
    push!(context.arguments, p.x)
    push!(context.calculated_arguments, missing)
    original_predicted_arguments = copy(context.predicted_arguments)
    calculated_output, context = _run_in_reverse(p.f, output, context)
    pop!(context.arguments)
    pop!(context.calculated_arguments)
    arg_target = pop!(context.predicted_arguments)
    if arg_target isa SkipArg
        return calculated_output, context
    end
    arg_calculated_output, context = _run_in_reverse(p.x, arg_target, context)
    # while arg_calculated_output != arg_target
    if arg_target isa AbductibleValue && arg_calculated_output != arg_target
        # @info "arg_target $arg_target"
        # @info "arg_calculated_output $arg_calculated_output"
        push!(context.arguments, p.x)
        push!(context.calculated_arguments, arg_calculated_output)
        context.predicted_arguments = original_predicted_arguments
        calculated_output, context = _run_in_reverse(p.f, output, context)
        pop!(context.arguments)
        pop!(context.calculated_arguments)
        arg_target = pop!(context.predicted_arguments)
        if arg_target isa SkipArg
            return calculated_output, context
        end
        arg_calculated_output, context = _run_in_reverse(p.x, arg_target, context)
        # @info "arg_target2 $arg_target"
        # @info "arg_calculated_output2 $arg_calculated_output"
    end
    return calculated_output, context
end

function _run_in_reverse(p::FreeVar, output, context)
    # @info "Running in reverse $p $output $context"
    if haskey(context.filled_vars, p.var_id)
        context.predicted_arguments,
        context.filled_indices,
        filled_vars,
        new_args,
        new_filled_indices,
        new_filled_vars = _intersect_values(
            context.predicted_arguments,
            context.filled_indices,
            context.filled_vars,
            [],
            Dict(),
            Dict{UInt64,Any}(p.var_id => output),
        )
        context.filled_vars = merge(filled_vars, new_filled_vars)
    else
        context.filled_vars[p.var_id] = output
    end
    # @info context
    return context.filled_vars[p.var_id], context
end

function _run_in_reverse(p::Index, output, context)
    # @info "Running in reverse $p $output $context"
    if haskey(context.filled_indices, p.n)
        context.predicted_arguments,
        filled_indices,
        context.filled_vars,
        new_args,
        new_filled_indices,
        new_filled_vars = _intersect_values(
            context.predicted_arguments,
            context.filled_indices,
            context.filled_vars,
            [],
            Dict{UInt64,Any}(p.n => output),
            Dict(),
        )
        context.filled_indices = merge(filled_indices, new_filled_indices)
    else
        context.filled_indices[p.n] = output
    end
    # @info context
    return context.filled_indices[p.n], context
end

function _run_in_reverse(p::Invented, output, context)
    return _run_in_reverse(p.b, output, context)
end

function _run_in_reverse(p::Abstraction, output, context::ReverseRunContext)
    # @info "Running in reverse $p $output $context"
    context.filled_indices = Dict{Int64,Any}(i + 1 => v for (i, v) in context.filled_indices)
    if !ismissing(context.calculated_arguments[end])
        context.filled_indices[0] = context.calculated_arguments[end]
    end
    pop!(context.calculated_arguments)
    calculated_output, context = _run_in_reverse(p.b, output, context)
    push!(context.predicted_arguments, context.filled_indices[0])
    push!(context.calculated_arguments, calculated_output)

    context.filled_indices = Dict{Int64,Any}(i - 1 => v for (i, v) in context.filled_indices if i > 0)
    return output, context
end

function _run_in_reverse(p::Program, output)
    return _run_in_reverse(p, output, ReverseRunContext())
end

function run_in_reverse(p::Program, output)
    # @info p
    return _run_in_reverse(p, output, ReverseRunContext())[2].filled_vars
end

_has_wildcard(v::PatternWrapper) = true
_has_wildcard(v) = false
_has_wildcard(v::AnyObject) = true
_has_wildcard(v::Vector) = any(_has_wildcard, v)
_has_wildcard(v::Tuple) = any(_has_wildcard, v)
_has_wildcard(v::Set) = any(_has_wildcard, v)

_wrap_wildcard(p::PatternWrapper) = p

function _wrap_wildcard(v)
    if _has_wildcard(v)
        return PatternWrapper(v)
    else
        return v
    end
end

function _wrap_wildcard(v::EitherOptions)
    options = Dict()
    for (h, op) in v.options
        options[h] = _wrap_wildcard(op)
    end
    return EitherOptions(options)
end

macro define_reverse_primitive(name, t, x, reverse_function)
    return quote
        local n = $(esc(name))
        @define_primitive n $t $x
        local prim = every_primitive[n]
        all_abstractors[prim] = [],
        (
            (v, ctx) -> (
                v,
                ReverseRunContext(ctx.arguments, $(esc(reverse_function))(v), ctx.calculated_arguments, Dict(), Dict()),
            )
        )
    end
end

function _generic_abductible_reverse(f, n, value, calculated_arguments, i, calculated_arg)
    if i == n
        return f(value, calculated_arguments)
    else
        return _generic_abductible_reverse(f, n, value, calculated_arguments, i + 1, calculated_arguments[end-i])
    end
end

function _generic_abductible_reverse(f, n, value, calculated_arguments, i, calculated_arg::EitherOptions)
    outputs = Dict()
    for (h, v) in calculated_arg.options
        new_args = [fix_option_hashes(Set([h]), v) for v in calculated_arguments]
        outputs[h] = _generic_abductible_reverse(f, n, value, new_args, 1, new_args[end])
    end
    results = [EitherOptions(Dict(h => v[j] for (h, v) in outputs)) for j in 1:n]
    # @info results
    return results
end

function _generic_abductible_reverse(f, n, value, calculated_arguments, i, calculated_arg::AnyObject)
    try
        if i == n
            return f(value, calculated_arguments)
        else
            return _generic_abductible_reverse(f, n, value, calculated_arguments, i + 1, calculated_arguments[end-i])
        end
    catch e
        if isa(e, InterruptException)
            rethrow()
        end
        # @info e
        new_args = [
            j == (length(calculated_arguments) - i + 1) ? missing : calculated_arguments[j] for
            j in 1:length(calculated_arguments)
        ]
        if i == n
            return f(value, new_args)
        else
            return _generic_abductible_reverse(f, n, value, new_args, i + 1, new_args[end-i])
        end
    end
end

function _generic_abductible_reverse(f, n, value, calculated_arguments)
    # @info "Running in reverse $f $n $value $calculated_arguments"
    result = _generic_abductible_reverse(f, n, value, calculated_arguments, 1, calculated_arguments[end])
    # @info "Reverse result $result"
    return result
end

macro define_abductible_reverse_primitive(name, t, x, reverse_function)
    return quote
        local n = $(esc(name))
        @define_primitive n $t $x
        local prim = every_primitive[n]
        all_abstractors[prim] = [],
        (
            (v, ctx) -> (
                v,
                ReverseRunContext(
                    ctx.arguments,
                    _generic_abductible_reverse(
                        $(esc(reverse_function)),
                        length(arguments_of_type($(esc(t)))),
                        v,
                        ctx.calculated_arguments,
                    ),
                    ctx.calculated_arguments,
                    Dict(),
                    Dict(),
                ),
            )
        )
    end
end

macro define_custom_reverse_primitive(name, t, x, reverse_function)
    return quote
        local n = $(esc(name))
        @define_primitive n $t $x
        local prim = every_primitive[n]
        all_abstractors[prim] = $(esc(reverse_function))
    end
end

_has_no_holes(p::Hole) = false
_has_no_holes(p::Apply) = _has_no_holes(p.f) && _has_no_holes(p.x)
_has_no_holes(p::Abstraction) = _has_no_holes(p.b)
_has_no_holes(p::Program) = true

_is_reversible_subfunction(p) = is_reversible(p) && _has_no_holes(p)

_is_possible_subfunction(p::Index, from_input, skeleton, path) = p.n != 0 || !isa(path[end], ArgTurn)
_is_possible_subfunction(p::Primitive, from_input, skeleton, path) = !from_input || haskey(all_abstractors, p)
_is_possible_subfunction(p::Invented, from_input, skeleton, path) = !from_input || is_reversible(p)
_is_possible_subfunction(p::FreeVar, from_input, skeleton, path) = true

_get_var_indices(p::Index) = [p.n]
_get_var_indices(p::FreeVar) = [-Int64(p.var_id)]
_get_var_indices(p::Primitive) = []
_get_var_indices(p::Invented) = []
_get_var_indices(p::Apply) = vcat(_get_var_indices(p.f), _get_var_indices(p.x))
_get_var_indices(p::Abstraction) = [((i > 0) ? (i - 1) : i) for i in _get_var_indices(p.b) if i != 0]

function _has_external_vars(f)
    return !isempty(_get_var_indices(f))
end

function calculate_dependent_vars(p, inputs, output)
    context = ReverseRunContext([], [], [], Dict(), copy(inputs))
    updated_inputs = _run_in_reverse(p, output, context)[2].filled_vars
    return Dict(
        k => v for (k, v) in updated_inputs if (!haskey(inputs, k) || inputs[k] != v) && !isa(v, AbductibleValue)
    )
end

include("repeat.jl")
include("cons.jl")
include("map.jl")
include("concat.jl")
include("range.jl")
include("rows.jl")
include("select.jl")
include("elements.jl")
include("zip.jl")
include("reverse.jl")
include("fold.jl")
include("tuple.jl")
include("adjoin.jl")
include("groupby.jl")
include("cluster.jl")
include("bool.jl")
include("int.jl")
