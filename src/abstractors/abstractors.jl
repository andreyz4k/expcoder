
all_abstractors = Dict{Program,Tuple{Vector,Any}}()

abstract type ArgChecker end

struct CombinedArgChecker
    should_be_reversible::Union{Bool,Nothing}
    max_index::Union{Int64,Nothing}
    can_have_free_vars::Union{Bool,Nothing}
    can_only_have_free_vars::Union{Bool,Nothing}
    inner_checkers::Vector
end

custom_arg_checkers = Dict{UInt64,Vector{Any}}()

function CombinedArgChecker(checkers::Vector)
    should_be_reversible = nothing
    max_index = nothing
    can_have_free_vars = nothing
    can_only_have_free_vars = nothing
    for checker in checkers
        if !isnothing(checker.should_be_reversible)
            should_be_reversible = checker.should_be_reversible
        end
        if !isnothing(checker.max_index)
            if isnothing(max_index)
                max_index = checker.max_index
            else
                max_index = min(max_index, checker.max_index)
            end
        end
        if !isnothing(checker.can_have_free_vars)
            can_have_free_vars = checker.can_have_free_vars
        end
        if !isnothing(checker.can_only_have_free_vars)
            can_only_have_free_vars = checker.can_only_have_free_vars
        end
    end
    return CombinedArgChecker(should_be_reversible, max_index, can_have_free_vars, can_only_have_free_vars, checkers)
end

Base.:(==)(c1::CombinedArgChecker, c2::CombinedArgChecker) =
    c1.should_be_reversible == c2.should_be_reversible &&
    c1.max_index == c2.max_index &&
    c1.can_have_free_vars == c2.can_have_free_vars &&
    c1.can_only_have_free_vars == c2.can_only_have_free_vars &&
    c1.inner_checkers == c2.inner_checkers

Base.hash(c::CombinedArgChecker, h::UInt64) = hash(
    c.should_be_reversible,
    hash(c.max_index, hash(c.can_have_free_vars, hash(c.can_only_have_free_vars, hash(c.inner_checkers, h)))),
)

function (c::CombinedArgChecker)(p::Index, skeleton, path)
    if c.can_only_have_free_vars == true || (!isnothing(c.max_index) && (p.n) > c.max_index)
        return false
    end
    return all(checker(p, skeleton, path) for checker in c.inner_checkers)
end

function (c::CombinedArgChecker)(p::Union{Primitive,Invented}, skeleton, path)
    if c.can_only_have_free_vars == true || (c.should_be_reversible == true && !is_reversible(p))
        return false
    end
    return all(checker(p, skeleton, path) for checker in c.inner_checkers)
end

function (c::CombinedArgChecker)(p::SetConst, skeleton, path)
    if c.can_only_have_free_vars == true
        return false
    end
    return all(checker(p, skeleton, path) for checker in c.inner_checkers)
end

function (c::CombinedArgChecker)(p::FreeVar, skeleton, path)
    if c.can_have_free_vars == false
        return false
    end
    return all(checker(p, skeleton, path) for checker in c.inner_checkers)
end

function step_arg_checker(c::CombinedArgChecker, arg)
    new_checkers = [step_arg_checker(checker, arg) for checker in c.inner_checkers]
    filter!(c -> !isnothing(c), new_checkers)
    if isempty(new_checkers)
        return nothing
    end
    return CombinedArgChecker(new_checkers)
end

function combine_arg_checkers(old::CombinedArgChecker, new::ArgChecker)
    if new == old.inner_checkers[end]
        return old
    end
    should_be_reversible = if isnothing(new.should_be_reversible)
        old.should_be_reversible
    else
        new.should_be_reversible
    end
    max_index = if isnothing(new.max_index)
        old.max_index
    elseif isnothing(old.max_index)
        new.max_index
    else
        min(old.max_index, new.max_index)
    end
    can_have_free_vars = if isnothing(new.can_have_free_vars)
        old.can_have_free_vars
    else
        new.can_have_free_vars
    end
    can_only_have_free_vars = if isnothing(new.can_only_have_free_vars)
        old.can_only_have_free_vars
    else
        new.can_only_have_free_vars
    end
    new_checkers = vcat(old.inner_checkers, [new])
    return CombinedArgChecker(
        should_be_reversible,
        max_index,
        can_have_free_vars,
        can_only_have_free_vars,
        new_checkers,
    )
end

function combine_arg_checkers(old::CombinedArgChecker, new::CombinedArgChecker)
    for c in new.inner_checkers
        old = combine_arg_checkers(old, c)
    end
    return old
end

struct SimpleArgChecker <: ArgChecker
    should_be_reversible::Union{Bool,Nothing}
    max_index::Union{Int64,Nothing}
    can_have_free_vars::Union{Bool,Nothing}
    can_only_have_free_vars::Union{Bool,Nothing}
end

Base.:(==)(c1::SimpleArgChecker, c2::SimpleArgChecker) =
    c1.should_be_reversible == c2.should_be_reversible &&
    c1.max_index == c2.max_index &&
    c1.can_have_free_vars == c2.can_have_free_vars &&
    c1.can_only_have_free_vars == c2.can_only_have_free_vars

Base.hash(c::SimpleArgChecker, h::UInt64) =
    hash(c.should_be_reversible, hash(c.max_index, hash(c.can_have_free_vars, hash(c.can_only_have_free_vars, h))))

(c::SimpleArgChecker)(p, skeleton, path) = true

function step_arg_checker(c::SimpleArgChecker, arg::ArgTurn)
    return SimpleArgChecker(
        c.should_be_reversible,
        isnothing(c.max_index) ? c.max_index : c.max_index + 1,
        c.can_have_free_vars,
        c.can_only_have_free_vars,
    )
end

function step_arg_checker(c::SimpleArgChecker, arg)
    return c
end

function _get_custom_arg_checkers(p::Primitive)
    if !haskey(custom_arg_checkers, p.hash_value)
        if haskey(all_abstractors, p)
            custom_arg_checkers[p.hash_value] = [c[2] for c in all_abstractors[p][1]]
        else
            custom_arg_checkers[p.hash_value] = []
        end
    end
    return custom_arg_checkers[p.hash_value]
end

_get_custom_arg_checkers(p::Index) = []
_get_custom_arg_checkers(p::FreeVar) = []

function _get_custom_arg_checkers(p::Invented)
    if !haskey(custom_arg_checkers, p.hash_value)
        checkers, indices_checkers = __get_custom_arg_checkers(p, nothing, Dict())
        @assert isempty(indices_checkers)
        custom_arg_checkers[p.hash_value] = checkers
    end
    return custom_arg_checkers[p.hash_value]
end

function __get_custom_arg_checkers(p::Primitive, checker::Nothing, indices_checkers::Dict)
    if haskey(all_abstractors, p)
        [CombinedArgChecker([c[2]]) for c in all_abstractors[p][1]], indices_checkers
    else
        [], indices_checkers
    end
end

function __get_custom_arg_checkers(p::Primitive, checker, indices_checkers::Dict)
    arg_count = length(arguments_of_type(p.t))
    custom_checkers = _get_custom_arg_checkers(p)
    out_checkers = []
    for i in 1:arg_count
        current_checker = step_arg_checker(checker, (p, i))
        if i > length(custom_checkers)
            push!(out_checkers, current_checker)
        elseif isnothing(custom_checkers[i])
            push!(out_checkers, current_checker)
        elseif isnothing(current_checker)
            push!(out_checkers, custom_checkers[i])
        else
            combined = combine_arg_checkers(current_checker, custom_checkers[i])
            push!(out_checkers, combined)
        end
    end
    out_checkers, indices_checkers
end

function __get_custom_arg_checkers(p::SetConst, checker, indices_checkers::Dict)
    [], indices_checkers
end

function __get_custom_arg_checkers(p::Invented, checker, indices_checkers::Dict)
    return __get_custom_arg_checkers(p.b, checker, indices_checkers)
end

function __get_custom_arg_checkers(p::Apply, checker, indices_checkers::Dict)
    checkers, indices_checkers = __get_custom_arg_checkers(p.f, checker, indices_checkers)
    if !isempty(checkers)
        _, indices_checkers = __get_custom_arg_checkers(p.x, checkers[1], indices_checkers)
    else
        _, indices_checkers = __get_custom_arg_checkers(p.x, nothing, indices_checkers)
    end
    return checkers[2:end], indices_checkers
end

function __get_custom_arg_checkers(p::Index, checker::Nothing, indices_checkers::Dict)
    return [], indices_checkers
end

function __get_custom_arg_checkers(p::Index, checker, indices_checkers::Dict)
    current_checker = step_arg_checker(checker, p)
    if !isnothing(current_checker)
        if haskey(indices_checkers, p.n)
            combined = combine_arg_checkers(current_checker, indices_checkers[p.n])
            indices_checkers[p.n] = combined
        else
            indices_checkers[p.n] = current_checker
        end
    end
    return [], indices_checkers
end

function __get_custom_arg_checkers(p::Abstraction, checker, indices_checkers::Dict)
    chekers, indices_checkers = __get_custom_arg_checkers(
        p.b,
        isnothing(checker) ? checker : step_arg_checker(checker, ArgTurn(t0, t0)),
        Dict(i + 1 => c for (i, c) in indices_checkers),
    )
    if haskey(indices_checkers, 0)
        out_checkers = vcat([indices_checkers[0]], chekers)
    elseif !isempty(chekers)
        out_checkers = vcat([nothing], chekers)
    else
        out_checkers = []
    end
    return out_checkers, Dict(i - 1 => c for (i, c) in indices_checkers if i > 0)
end

_fill_args(p::Program, environment) = p
_fill_args(p::Invented, environment) = _fill_args(p.b, environment)
_fill_args(p::Apply, environment) = Apply(_fill_args(p.f, environment), _fill_args(p.x, environment))
_fill_args(p::Abstraction, environment) = Abstraction(_fill_args(p.b, Dict(i + 1 => c for (i, c) in environment)))

function _fill_args(p::Index, environment)
    if haskey(environment, p.n) && !isa(environment[p.n], Hole)
        return environment[p.n]
    else
        return p
    end
end

reversible_cache = Dict{Tuple{Program,Dict{Int64,Any},Vector{Any},Bool},Any}()

function _is_reversible(p::Primitive, environment, args, in_lambda)
    # @info "Checking $(p) $environment $args $in_lambda"
    key = (p, environment, args, in_lambda)
    if !haskey(reversible_cache, key)
        if haskey(all_abstractors, p)
            reversible_cache[key] = [c[1] for c in all_abstractors[p][1]]
        else
            reversible_cache[key] = nothing
        end
    end
    return reversible_cache[key]
end

function _is_reversible(p::Apply, environment, args, in_lambda)
    # @info "Checking $(p) $environment $args $in_lambda"
    key = (p, environment, args, in_lambda)
    if !haskey(reversible_cache, key)
        filled_x = _fill_args(p.x, environment)
        checkers = _is_reversible(p.f, environment, vcat(args, [filled_x]), in_lambda)
        if isnothing(checkers)
            # @info "Returned nothing for $(p.f) $environment $args $filled_x"
            reversible_cache[key] = nothing
        else
            checker = nothing
            if isempty(checkers)
                reversible_cache[key] = if isa(filled_x, Hole)
                    if !in_lambda && !isarrow(filled_x.t)
                        checkers
                    else
                        nothing
                    end
                elseif isa(filled_x, Index) || isa(filled_x, FreeVar)
                    checkers
                elseif isa(filled_x, Abstraction)
                    checkers
                else
                    checker = x -> !isnothing(_is_reversible(x, Dict(), [], in_lambda))
                end
            else
                checker = checkers[1]
                if isnothing(checker)
                    if isa(filled_x, Abstraction)
                        reversible_cache[key] = view(checkers, 2:length(checkers))
                    else
                        checker = x -> !isnothing(_is_reversible(x, Dict(), [], in_lambda))
                    end
                end
            end
            if !isnothing(checker)
                # @info "Running checker $checker $(p) $(filled_x)"
                if !checker(filled_x)
                    # @info "Checker failed for $checker $(p) $(filled_x) "
                    reversible_cache[key] = nothing
                else
                    reversible_cache[key] = view(checkers, 2:length(checkers))
                end
            end
        end
    end
    return reversible_cache[key]
end

_is_reversible(p::Invented, environment, args, in_lambda) = _is_reversible(p.b, environment, args, in_lambda)

function _is_reversible(p::Abstraction, environment, args, in_lambda)
    # @info "Checking $(p) $environment $args $in_lambda"
    key = (p, environment, args, in_lambda)
    if !haskey(reversible_cache, key)
        environment = Dict{Int64,Any}(i + 1 => c for (i, c) in environment)
        if !isempty(args)
            environment[0] = args[end]
        end
        reversible_cache[key] = _is_reversible(p.b, environment, view(args, 1:length(args)-1), true)
    end
    return reversible_cache[key]
end

_is_reversible(p::SetConst, environment, args, in_lambda) = []

function _is_reversible(p::Index, environment, args, in_lambda)
    # @info "Checking $(p) $environment $args $in_lambda"
    key = (p, environment, args, in_lambda)
    if !haskey(reversible_cache, key)
        filled_p = _fill_args(p, environment)
        if isa(filled_p, Index)
            return []
        else
            reversible_cache[key] = _is_reversible(filled_p, Dict(), [], in_lambda)
        end
    end
    return reversible_cache[key]
end

_is_reversible(p::Program, environment, args, in_lambda) = nothing

is_reversible(p::Program)::Bool = !isnothing(_is_reversible(p, Dict{Int64,Any}(), [], false))
is_reversible(p::Invented)::Bool = p.is_reversible

struct SkipArg end

mutable struct ReverseRunContext
    block_id::UInt64
    arguments::Vector{Any}
    predicted_arguments::Vector{Any}
    calculated_arguments::Vector{Any}
    filled_indices::Dict{Int64,Any}
    filled_vars::Dict{UInt64,Any}
end

ReverseRunContext(block_id::UInt64) = ReverseRunContext(block_id, [], [], [], Dict(), Dict())

function _preprocess_options(args_options, output)
    if any(isa(out, AbductibleValue) for out in values(args_options))
        abd = first(out for out in values(args_options) if isa(out, AbductibleValue))
        for (h, val) in args_options
            if !isa(val, AbductibleValue) && abd.value == val
                args_options[h] = abd
            end
        end
    end
    return EitherOptions(args_options)
end

abstract type ProgramInfo end

struct PrimitiveInfo <: ProgramInfo
    p::Primitive
    indices::Vector{Int64}
    var_ids::Vector{UInt64}
end

struct ApplyInfo <: ProgramInfo
    p::Apply
    f_info::ProgramInfo
    x_info::ProgramInfo
    indices::Vector{Int64}
    var_ids::Vector{UInt64}
end

struct AbstractionInfo <: ProgramInfo
    p::Abstraction
    b_info::ProgramInfo
    indices::Vector{Int64}
    var_ids::Vector{UInt64}
end

struct SetConstInfo <: ProgramInfo
    p::SetConst
    indices::Vector{Int64}
    var_ids::Vector{UInt64}
end

struct IndexInfo <: ProgramInfo
    p::Index
    indices::Vector{Int64}
    var_ids::Vector{UInt64}
end

struct FreeVarInfo <: ProgramInfo
    p::FreeVar
    indices::Vector{Int64}
    var_ids::Vector{UInt64}
end

_gather_info(p::Primitive, fill_indices, args) = PrimitiveInfo(p, [], [])

_gather_info(p::Invented, fill_indices, args) = _gather_info(p.b, fill_indices, args)

function _gather_info(p::Apply, fill_indices, args)
    x_info = _gather_info(p.x, fill_indices, [])
    f_info = _gather_info(p.f, fill_indices, vcat(args, [(0, x_info.p)]))
    indices = vcat(f_info.indices, x_info.indices)
    var_ids = vcat(f_info.var_ids, x_info.var_ids)
    return ApplyInfo(Apply(f_info.p, x_info.p), f_info, x_info, indices, var_ids)
end

function _gather_info(p::Abstraction, fill_indices, args)
    new_fill_indices = Dict(i + 1 => (k + 1, c) for (i, (k, c)) in fill_indices)
    if !isempty(args) && isa(args[end][2], Abstraction)
        new_fill_indices[0] = (args[end][1] + 1, args[end][2])
    end
    # @info p
    new_args = [(i + 1, a) for (i, a) in view(args, 1:length(args)-1)]
    # @info "New args $new_args"
    # @info "New fill indices $new_fill_indices"
    b_info = _gather_info(p.b, new_fill_indices, new_args)
    return AbstractionInfo(Abstraction(b_info.p), b_info, [i - 1 for i in b_info.indices if i > 0], b_info.var_ids)
end

_gather_info(p::SetConst, fill_indices, args) = SetConstInfo(p, [], [])

shift_indices(p::Abstraction, shift, threshold) = Abstraction(shift_indices(p.b, shift, threshold + 1))
shift_indices(p::Apply, shift, threshold) =
    Apply(shift_indices(p.f, shift, threshold), shift_indices(p.x, shift, threshold))
shift_indices(p::Index, shift, threshold) =
    if p.n < threshold
        p
    else
        Index(p.n + shift)
    end
shift_indices(p, shift, threshold) = p

function _gather_info(p::Index, fill_indices, args)
    if haskey(fill_indices, p.n)
        fill_shift, filler = fill_indices[p.n]
        shifted_p = shift_indices(filler, fill_shift, 0)
        # @info "Shifted $(fill_indices[p.n]) $(p.n) to $shifted_p"
        return _gather_info(shifted_p, fill_indices, args)
    else
        return IndexInfo(p, [p.n], [])
    end
end

_gather_info(p::FreeVar, fill_indices, args) = FreeVarInfo(p, [], [p.var_id])

gather_info(p) = _gather_info(p, Dict(), [])

function gather_info(p::BoundAbstraction)
    filled_indices = Dict()
    for i in 0:length(p.arguments)-1
        arg = p.arguments[end-i]
        if isa(arg, BoundAbstraction)
            arg_info = gather_info(arg)
            filled_indices[i] = (0, arg_info.p)
        end
    end
    _gather_info(p.p_base, filled_indices, [])
end

function _run_in_reverse(p_info, output, context, splitter::EitherOptions)
    # @info "Running in reverse $(p_info.p) $output $context"
    output_options = Dict()
    arguments_options = Dict[]
    arguments_options_counts = Int[]
    filled_indices_options = DefaultDict(() -> Dict())
    filled_indices_options_counts = DefaultDict(() -> 0)
    filled_vars_options = DefaultDict(() -> Dict())
    filled_vars_options_counts = DefaultDict(() -> 0)
    for (h, _) in splitter.options
        fixed_hashes = Set([h])
        op_calculated_arguments = [fix_option_hashes(fixed_hashes, v) for v in context.calculated_arguments]
        op_predicted_arguments = [fix_option_hashes(fixed_hashes, v) for v in context.predicted_arguments]
        op_filled_indices = Dict(i => fix_option_hashes(fixed_hashes, v) for (i, v) in context.filled_indices)
        op_filled_vars = Dict(k => fix_option_hashes(fixed_hashes, v) for (k, v) in context.filled_vars)

        success, calculated_output, new_context = _run_in_reverse(
            p_info,
            fix_option_hashes(fixed_hashes, output),
            ReverseRunContext(
                context.block_id,
                context.arguments,
                op_predicted_arguments,
                op_calculated_arguments,
                op_filled_indices,
                op_filled_vars,
            ),
        )

        if !success
            continue
        end
        if isempty(arguments_options)
            for _ in 1:(length(new_context.predicted_arguments))
                push!(arguments_options, Dict())
                push!(arguments_options_counts, 0)
            end
        end
        output_options[h] = calculated_output

        for i in 1:length(new_context.predicted_arguments)
            arguments_options[i][h] = new_context.predicted_arguments[i]
            arguments_options_counts[i] += get_options_count(new_context.predicted_arguments[i])
            if arguments_options_counts[i] > 100
                return false, output, context
            end
        end
        for (i, v) in new_context.filled_indices
            filled_indices_options[i][h] = v
            filled_indices_options_counts[i] += get_options_count(v)
            if filled_indices_options_counts[i] > 100
                return false, output, context
            end
        end
        for (k, v) in new_context.filled_vars
            filled_vars_options[k][h] = v
            filled_vars_options_counts[k] += get_options_count(v)
            if filled_vars_options_counts[k] > 100
                return false, output, context
            end
        end
    end

    out_args = []
    out_filled_indices = Dict()
    out_filled_vars = Dict()

    # @info "Arguments options $arguments_options"
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
        context.block_id,
        context.arguments,
        out_args,
        context.calculated_arguments,
        out_filled_indices,
        out_filled_vars,
    )
    if isempty(output_options) ||
       length(output_options) > 100 ||
       sum((get_options_count(v) for v in values(output_options))) > 100
        # @info "Bad options count $output_options"
        return false, output, out_context
    end
    # @info "Results for reverse $(p_info.p) $output $context"
    # @info "Output options $output_options"
    # @info "Output context $out_context"
    return true, EitherOptions(output_options), out_context
end

function _run_in_reverse(p_info, output::EitherOptions, context)
    return _run_in_reverse(p_info, output, context, output)
end

function _run_in_reverse(p_info, output, context)
    for (i, v) in context.filled_indices
        if isa(v, EitherOptions)
            return _run_in_reverse(p_info, output, context, v)
        end
    end
    for (k, v) in context.filled_vars
        if isa(v, EitherOptions)
            return _run_in_reverse(p_info, output, context, v)
        end
    end
    return __run_in_reverse(p_info, output, context)
end

function __run_in_reverse(p_info::PrimitiveInfo, @nospecialize(output::Any), context)
    # @info "Running in reverse $(p_info.p) $output $context"
    try
        results = all_abstractors[p_info.p][2](output, context)
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    catch e
        # bt = catch_backtrace()
        # @error "Error while running $(p_info.p) $output $context" exception = (e, bt)
        if isa(e, InterruptException)
            rethrow()
        end
        # @info "Failed to run in reverse $(p_info.p) $output $context"
        return false, output, context
    end
end

function __run_in_reverse(p_info::PrimitiveInfo, output::AbductibleValue, context)
    # @info "Running in reverse $(p_info.p) $output $context"
    success, calculated_output, new_context = try
        all_abstractors[p_info.p][2](output, context)
    catch e
        # bt = catch_backtrace()
        # @error e exception = (e, bt)
        if isa(e, InterruptException)
            rethrow()
        elseif isa(e, MethodError) && any(isa(arg, AbductibleValue) for arg in e.args)
            false, output, context
        else
            # @info "Failed to run in reverse $(p_info.p) $output $context"
            return false, output, context
        end
    end
    if success
        new_context.predicted_arguments = [_wrap_abductible(arg) for arg in new_context.predicted_arguments]
        new_context.filled_indices = Dict(i => _wrap_abductible(v) for (i, v) in new_context.filled_indices)
        new_context.filled_vars = Dict(k => _wrap_abductible(v) for (k, v) in new_context.filled_vars)
        results = success, _wrap_abductible(calculated_output), new_context
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    else
        results = []
        arg_types = reverse(arguments_of_type(p_info.p.t))
        for (i, t) in enumerate(arg_types)
            if ismissing(context.calculated_arguments[end-length(arg_types)+i])
                if isarrow(t)
                    push!(results, SkipArg())
                    for index in context.arguments[i].indices
                        if !haskey(context.filled_indices, index)
                            context.filled_indices[index] = AbductibleValue(any_object)
                        end
                    end
                    for var_id in context.arguments[i].var_ids
                        if !haskey(context.filled_vars, var_id)
                            context.filled_vars[var_id] = AbductibleValue(any_object)
                        end
                    end
                else
                    push!(results, AbductibleValue(any_object))
                end
            else
                push!(results, context.calculated_arguments[end-length(arg_types)+i])
            end
        end
        results = true,
        output,
        ReverseRunContext(
            context.block_id,
            context.arguments,
            vcat(context.predicted_arguments, results),
            context.calculated_arguments,
            context.filled_indices,
            context.filled_vars,
        )
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    end
end

function __run_in_reverse(p_info::PrimitiveInfo, output::PatternWrapper, context)
    # @info "Running in reverse $(p_info.p) $output $context"
    success, calculated_output, new_context = __run_in_reverse(p_info, output.value, context)
    if !success
        # @info "Failed to run in reverse $(p_info.p) $output $context"
        return false, output, context
    end

    new_context.predicted_arguments = [_wrap_wildcard(arg) for arg in new_context.predicted_arguments]
    new_context.filled_indices = Dict(i => _wrap_wildcard(v) for (i, v) in new_context.filled_indices)
    new_context.filled_vars = Dict(k => _wrap_wildcard(v) for (k, v) in new_context.filled_vars)

    results = success, _wrap_wildcard(calculated_output), new_context
    # @info "Results for reverse $(p_info.p) $output $context are $results"
    return results
end

function __run_in_reverse(p_info::PrimitiveInfo, output::Union{Nothing,AnyObject}, context)
    # @info "Running in reverse $(p_info.p) $output $context"
    success, calculated_output, new_context = try
        all_abstractors[p_info.p][2](output, context)
    catch e
        # bt = catch_backtrace()
        # @error e exception = (e, bt)
        if isa(e, InterruptException)
            rethrow()
        elseif isa(e, MethodError)
            false, output, context
        else
            # @info "Failed to run in reverse $(p_info.p) $output $context"
            return false, output, context
        end
    end
    if success
        results = success, calculated_output, new_context
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    else
        new_predicted_arguments = []
        for (i, t) in enumerate(reverse(arguments_of_type(p_info.p.t)))
            if isarrow(t)
                push!(new_predicted_arguments, SkipArg())
                for index in context.arguments[i].indices
                    if !haskey(context.filled_indices, index)
                        context.filled_indices[index] = output
                    end
                end
                for var_id in context.arguments[i].var_ids
                    if !haskey(context.filled_vars, var_id)
                        context.filled_vars[var_id] = output
                    end
                end
            else
                push!(new_predicted_arguments, output)
            end
        end
        results = true,
        output,
        ReverseRunContext(
            context.block_id,
            context.arguments,
            vcat(context.predicted_arguments, new_predicted_arguments),
            context.calculated_arguments,
            context.filled_indices,
            context.filled_vars,
        )
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    end
end

function __run_in_reverse(p_info::ApplyInfo, output::AbductibleValue, context)
    # @info "Running in reverse $(p_info.p) $output $context"
    env = Any[nothing for _ in 1:maximum(keys(context.filled_indices); init = -1)+1]
    for (i, v) in context.filled_indices
        env[end-i] = v
    end
    try
        calculated_output = p_info.p(env, context.filled_vars)
        # @info calculated_output
        if calculated_output isa Function
            error("Function output")
        end
        results = true, calculated_output, context
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    catch e
        if e isa InterruptException
            rethrow()
        end
        results = @invoke __run_in_reverse(p_info::ApplyInfo, output::Any, context)
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    end
end

function _precalculate_arg(p_info, context)
    # @info "Precalculating $(p_info.p) $(p_info.indices) $(p_info.var_ids) $(context.filled_indices) $(context.filled_vars) $(context.calculated_arguments)"
    for i in p_info.indices
        if !haskey(context.filled_indices, i)
            return missing
        end
    end
    for i in p_info.var_ids
        if !haskey(context.filled_vars, i)
            return missing
        end
    end
    env = Any[missing for _ in 1:maximum(keys(context.filled_indices); init = -1)+1]
    for (i, v) in context.filled_indices
        env[end-i] = v
    end
    try
        # @info "Precalculating $(p_info.p) with $env and $(context.filled_vars)"
        calculated_output = __run_with_arguments(_build_typed_expression(p_info.p), env, context.filled_vars)
        # @info calculated_output
        if isa(calculated_output, Function) ||
           isa(calculated_output, AbductibleValue) ||
           isa(calculated_output, PatternWrapper)
            return missing
        end
        return calculated_output
    catch e
        if e isa InterruptException
            rethrow()
        end
        return missing
    end
end

function __run_in_reverse(p_info::ApplyInfo, output, context)
    # @info "Running in reverse $(p_info.p) $output $context"
    precalculated_arg = _precalculate_arg(p_info.x_info, context)
    # @info "Precalculated arg for $(p_info.x_info.p) is $precalculated_arg"
    success, calculated_output, arg_context = _run_in_reverse(
        p_info.f_info,
        output,
        ReverseRunContext(
            context.block_id,
            vcat(context.arguments, [p_info.x_info]),
            context.predicted_arguments,
            vcat(context.calculated_arguments, [precalculated_arg]),
            context.filled_indices,
            context.filled_vars,
        ),
    )
    # @info success, calculated_output, arg_context
    if !success
        # @info "Failed to run in reverse $(p_info.p) $output $context"
        return false, output, context
    end
    # @info "Arg context for $(p_info.p) $arg_context"
    pop!(arg_context.arguments)
    pop!(arg_context.calculated_arguments)
    arg_target = pop!(arg_context.predicted_arguments)
    if arg_target isa SkipArg
        results = true, calculated_output, arg_context
        # @info "Results for reverse $(p_info.p) $output $context are $results"
        return results
    end
    success, arg_calculated_output, out_context = _run_in_reverse(p_info.x_info, arg_target, arg_context)
    if !success
        # @info "Failed to run arg in reverse $(p_info.p) $(p_info.x_info.p) $arg_target $context $arg_context"
        return false, output, context
    end
    # @info "arg_target $arg_target"
    # @info "arg_calculated_output $arg_calculated_output"
    if arg_calculated_output != arg_target
        # if arg_target isa AbductibleValue && arg_calculated_output != arg_target
        success, calculated_output, arg_context = _run_in_reverse(
            p_info.f_info,
            calculated_output,
            ReverseRunContext(
                context.block_id,
                vcat(context.arguments, [p_info.x_info]),
                context.predicted_arguments,
                vcat(context.calculated_arguments, [arg_calculated_output]),
                out_context.filled_indices,
                out_context.filled_vars,
            ),
        )
        if !success
            # @info "Failed to run in reverse $(p_info.p) $output $context"
            return false, output, context
        end
        pop!(arg_context.arguments)
        pop!(arg_context.calculated_arguments)
        arg_target = pop!(arg_context.predicted_arguments)
        if arg_target isa SkipArg
            results = true, calculated_output, arg_context
            # @info "Results for reverse $(p_info.p) $output $context are $results"
            return results
        end
        success, arg_calculated_output, out_context = _run_in_reverse(p_info.x_info, arg_target, arg_context)
        if !success
            # @info "Failed to run in reverse $(p_info.p) $output $context"
            return false, output, context
        end
        # @info "arg_target2 $arg_target"
        # @info "arg_calculated_output2 $arg_calculated_output"
    end
    # @info "Calculated output for $(p_info.p) $calculated_output"
    # @info "Out context for $(p_info.p) $out_context"
    results = true, calculated_output, out_context
    # @info "Results for reverse $(p_info.p) $output $context are $results"
    return results
end

function __run_in_reverse(p_info::FreeVarInfo, output, context)
    # @info "Running in reverse $(p_info.p) $output $context"
    if haskey(context.filled_vars, p_info.p.var_id)
        found, unified_v = _try_unify_values(context.filled_vars[p_info.p.var_id], output, false, context.block_id)
        if !found
            # @info "Failed to run in reverse $(p_info.p) $output $context"
            return false, output, context
        end
        context.filled_vars[p_info.p.var_id] = unified_v
    else
        context.filled_vars[p_info.p.var_id] = output
    end
    # @info context
    results = true, context.filled_vars[p_info.p.var_id], context
    # @info "Results for reverse $(p_info.p) $output $context are $results"
    return results
end

function __run_in_reverse(p_info::IndexInfo, output, context)
    # @info "Running in reverse $(p_info.p) $output $context"
    if haskey(context.filled_indices, p_info.p.n)
        found, unified_v = _try_unify_values(context.filled_indices[p_info.p.n], output, false, context.block_id)
        if !found
            # @info "Failed to run in reverse $(p_info.p) $output $context"
            return false, output, context
        end
        context.filled_indices[p_info.p.n] = unified_v
    else
        context.filled_indices[p_info.p.n] = output
    end
    # @info context
    results = true, context.filled_indices[p_info.p.n], context
    # @info "Results for reverse $(p_info.p) $output $context are $results"
    return results
end

function __run_in_reverse(p_info::AbstractionInfo, output, context::ReverseRunContext)
    # @info "Running in reverse $(p_info.p) $output $context"
    in_filled_indices = Dict{Int64,Any}(i + 1 => v for (i, v) in context.filled_indices)
    if !ismissing(context.calculated_arguments[end])
        in_filled_indices[0] = context.calculated_arguments[end]
    end
    success, calculated_output, out_context = _run_in_reverse(
        p_info.b_info,
        output,
        ReverseRunContext(
            context.block_id,
            context.arguments[1:end-1],
            context.predicted_arguments,
            context.calculated_arguments[1:end-1],
            in_filled_indices,
            context.filled_vars,
        ),
    )
    if !success
        # @info "Failed to run in reverse $(p_info.p) $output $context"
        return false, output, context
    end
    if !haskey(out_context.filled_indices, 0)
        push!(out_context.predicted_arguments, SkipArg())
    else
        push!(out_context.predicted_arguments, out_context.filled_indices[0])
    end
    push!(out_context.calculated_arguments, calculated_output)
    if !isempty(context.arguments)
        push!(out_context.arguments, context.arguments[end])
    end

    out_context.filled_indices = Dict{Int64,Any}(i - 1 => v for (i, v) in out_context.filled_indices if i > 0)
    results = true, output, out_context
    # @info "Results for reverse $(p_info.p) $output $context are $results"
    return results
end

function __run_in_reverse(p_info::SetConstInfo, output, context)
    results = output == p_info.p.value, output, context
    # @info "Results for reverse $(p_info.p) $output $context are $results"
    return results
end

function run_in_reverse(p::Program, output, block_id::UInt64)
    # @info p
    # start_time = time()
    # @info "Running in reverse $p $output"
    p_info = gather_info(p)
    success, computed_output, context = _run_in_reverse(p_info, output, ReverseRunContext(block_id))
    # @info success, computed_output, context
    if !success
        error("Failed to run in reverse $p $output")
    end
    # elapsed = time() - start_time
    # if elapsed > 2
    #     @info "Reverse run took $elapsed seconds"
    #     @info p
    #     @info output
    # end
    # @info context.predicted_arguments
    # @info context.filled_indices
    if computed_output != output && !isempty(context.filled_vars)
        error("Output mismatch $computed_output != $output")
    end
    return context.filled_vars
end

_has_wildcard(v::PatternWrapper) = true
_has_wildcard(v) = false
_has_wildcard(v::AnyObject) = true
_has_wildcard(v::Array) = any(_has_wildcard, v)
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

_unwrap_abductible(v::AbductibleValue) = _unwrap_abductible(v.value)
_unwrap_abductible(v::PatternWrapper) = _unwrap_abductible(v.value)
function _unwrap_abductible(v::Array)
    res = [_unwrap_abductible(v) for v in v]
    return reshape(res, size(v))
end
_unwrap_abductible(v::Tuple) = tuple((_unwrap_abductible(v) for v in v)...)
_unwrap_abductible(v::Set) = Set([_unwrap_abductible(v) for v in v])
_unwrap_abductible(v) = v

_wrap_abductible(v::AbductibleValue) = v

function _wrap_abductible(v)
    if _has_wildcard(v)
        return AbductibleValue(_unwrap_abductible(v))
    else
        return v
    end
end

function _wrap_abductible(v::EitherOptions)
    options = Dict()
    for (h, op) in v.options
        options[h] = _wrap_abductible(op)
    end
    return EitherOptions(options)
end

function _generic_reverse(f, val, ctx)
    predicted_args = f(ctx.block_id, val)
    for i in 1:length(predicted_args)
        if !ismissing(ctx.calculated_arguments[end-i+1])
            arg = predicted_args[i]
            found, fixed_hashes = _get_fixed_hashes(arg, ctx.calculated_arguments[end-i+1])
            if !found
                #     @info "Failed to fix hashes"
                #     @info arg
                #     @info ctx.calculated_arguments[end-i+1]
                return false, val, ctx
            end
            predicted_args = [fix_option_hashes(fixed_hashes, v) for v in predicted_args]
        end
    end
    (
        true,
        val,
        ReverseRunContext(
            ctx.block_id,
            ctx.arguments,
            vcat(ctx.predicted_arguments, reverse(predicted_args)),
            ctx.calculated_arguments,
            ctx.filled_indices,
            ctx.filled_vars,
        ),
    )
end

macro define_reverse_primitive(name, t, x, reverse_function)
    return quote
        local n = $(esc(name))
        @define_primitive n $(esc(t)) $(esc(x))
        local prim = every_primitive[n]
        all_abstractors[prim] = [], (v, ctx) -> _generic_reverse($(esc(reverse_function)), v, ctx)
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

function _generic_abductible_reverse(f, n, value, calculated_arguments, i, calculated_arg::PatternWrapper)
    new_args =
        [j == length(calculated_arguments) - i + 1 ? arg.value : arg for (j, arg) in enumerate(calculated_arguments)]
    results = _generic_abductible_reverse(f, n, value, new_args, i, calculated_arg.value)
    return [_wrap_wildcard(r) for r in results]
end

function _generic_abductible_reverse(f, n, value, calculated_arguments, i, calculated_arg::AbductibleValue)
    new_args =
        [j == length(calculated_arguments) - i + 1 ? arg.value : arg for (j, arg) in enumerate(calculated_arguments)]
    results = _generic_abductible_reverse(f, n, value, new_args, i, calculated_arg.value)
    return [_wrap_abductible(r) for r in results]
end

function _generic_abductible_reverse(f, n, value, calculated_arguments, i, calculated_arg::Union{AnyObject,Nothing})
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
        # @info calculated_arguments
        # @info new_args
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
                true,
                v,
                ReverseRunContext(
                    ctx.block_id,
                    ctx.arguments,
                    vcat(
                        ctx.predicted_arguments,
                        reverse(
                            _generic_abductible_reverse(
                                $(esc(reverse_function)),
                                length(arguments_of_type($(esc(t)))),
                                v,
                                ctx.calculated_arguments,
                            ),
                        ),
                    ),
                    ctx.calculated_arguments,
                    ctx.filled_indices,
                    ctx.filled_vars,
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

struct IsPossibleSubfunction <: ArgChecker
    should_be_reversible::Nothing
    max_index::Nothing
    can_have_free_vars::Nothing
    can_only_have_free_vars::Nothing
    IsPossibleSubfunction() = new(nothing, nothing, nothing, nothing)
end

Base.:(==)(c1::IsPossibleSubfunction, c2::IsPossibleSubfunction) = true

Base.hash(c::IsPossibleSubfunction, h::UInt64) =
    hash(c.should_be_reversible, hash(c.max_index, hash(c.can_have_free_vars, hash(c.can_only_have_free_vars, h))))

function (c::IsPossibleSubfunction)(p::Index, skeleton, path)
    return p.n != 0
end

(c::IsPossibleSubfunction)(p, skeleton, path) = true

step_arg_checker(c::IsPossibleSubfunction, arg::ArgTurn) = c
step_arg_checker(::IsPossibleSubfunction, arg) = nothing

function calculate_dependent_vars(p, inputs, output, block_id::UInt64)
    context = ReverseRunContext(block_id, [], [], [], Dict(), copy(inputs))
    p_info = gather_info(p)
    success, computed_output, context = _run_in_reverse(p_info, output, context)
    if !success
        error("Failed to run in reverse $p $output")
    end
    updated_inputs = context.filled_vars
    return Dict(
        k => v for (k, v) in updated_inputs if (!haskey(inputs, k) || inputs[k] != v) # && !isa(v, AbductibleValue)
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
include("rev_fix_param.jl")
