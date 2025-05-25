
struct IsPossibleReversibleSubfunction <: ArgChecker
    should_be_reversible::Bool
    max_index::Nothing
    can_have_free_vars::Nothing
    can_only_have_free_vars::Nothing
    IsPossibleReversibleSubfunction() = new(true, nothing, nothing, nothing)
end

Base.:(==)(c1::IsPossibleReversibleSubfunction, c2::IsPossibleReversibleSubfunction) = true

Base.hash(c::IsPossibleReversibleSubfunction, h::UInt64) =
    hash(c.should_be_reversible, hash(c.max_index, hash(c.can_have_free_vars, hash(c.can_only_have_free_vars, h))))

(c::IsPossibleReversibleSubfunction)(p, skeleton, path) = true

function step_arg_checker(c::IsPossibleReversibleSubfunction, arg::Index)
    return nothing
end

function step_arg_checker(c::IsPossibleReversibleSubfunction, arg)
    return c
end

# _is_fixable_param(p::Index) = true
# _is_fixable_param(p::FreeVar) = true
_is_fixable_param(p) = true

struct IsPossibleFixableParam <: ArgChecker
    should_be_reversible::Nothing
    max_index::Nothing
    can_have_free_vars::Nothing
    can_only_have_free_vars::Nothing
    IsPossibleFixableParam() = new(nothing, nothing, nothing, nothing)
end

Base.:(==)(c1::IsPossibleFixableParam, c2::IsPossibleFixableParam) = true

Base.hash(c::IsPossibleFixableParam, h::UInt64) =
    hash(c.should_be_reversible, hash(c.max_index, hash(c.can_have_free_vars, hash(c.can_only_have_free_vars, h))))

function (c::IsPossibleFixableParam)(p::Index, skeleton, path)
    return has_index(follow_path(skeleton, vcat(path[begin:end-1], [LeftTurn(), RightTurn()])), p.n)
end
(c::IsPossibleFixableParam)(p, skeleton, path) = false

function (c::IsPossibleFixableParam)(p::FreeVar, skeleton, path)
    body_free_vars = _get_free_vars(follow_path(skeleton, path[begin:end-1]))
    return haskey(body_free_vars, p.var_id)
end

step_arg_checker(::IsPossibleFixableParam, arg) = nothing

function reverse_fix_param()
    function _reverse_fix_param(value, context)
        # @info "Running reverse fix param for $value in context $context"
        body = context.arguments[end]
        param = context.arguments[end-1].p
        fixer = context.arguments[end-2]

        env = Any[missing for _ in 1:maximum(keys(context.filled_indices); init = -1)+1]
        for (i, v) in context.filled_indices
            env[end-i] = v
        end
        fixer_func = __run_with_arguments(_build_typed_expression(fixer.p), env, context.filled_vars)

        # fixer_value = try_evaluate_program(fixer.p, [value], Dict())
        fixer_value = try_run_function(fixer_func, [value])

        if isa(fixer_value, EitherOptions) || isa(fixer_value, PatternWrapper) || isa(fixer_value, AbductibleValue)
            return false, value, context
            # error("Fixer value cannot be wildcard")
        end
        if isa(param, Index)
            if haskey(context.filled_indices, param.n) && context.filled_indices[param.n] !== fixer_value
                return false, value, context
                # error("Index $(param.n) is already filled with $(context.filled_indices[param.n])")
            end
            filled_indices = copy(context.filled_indices)
            filled_indices[param.n] = fixer_value
            filled_vars = context.filled_vars
        elseif isa(param, FreeVar)
            if haskey(context.filled_vars, param.var_id) && context.filled_vars[param.var_id] !== fixer_value
                return false, value, context
                # error("Variable $(param.var_id) is already filled with $(context.filled_vars[param.var_id])")
            end
            filled_vars = copy(context.filled_vars)
            filled_vars[param.var_id] = fixer_value
            filled_indices = context.filled_indices
        else
            error("Invalid param type $(param)")
            return false, value, context
        end

        success, calculated_output, arg_context = _run_in_reverse(
            body,
            value,
            ReverseRunContext(
                context.block_id,
                context.arguments[begin:end-3],
                context.predicted_arguments,
                context.calculated_arguments[begin:end-3],
                filled_indices,
                filled_vars,
            ),
        )
        if !success
            return false, value, context
        end
        return true,
        calculated_output,
        ReverseRunContext(
            context.block_id,
            context.arguments,
            vcat(arg_context.predicted_arguments, [SkipArg(), SkipArg(), SkipArg()]),
            context.calculated_arguments,
            arg_context.filled_indices,
            arg_context.filled_vars,
        )
    end
    return [
        (_is_reversible_subfunction, IsPossibleReversibleSubfunction()),
        (_is_fixable_param, IsPossibleFixableParam()),
        (_has_no_holes, SimpleArgChecker(false, -1, false, nothing)),
    ],
    _reverse_fix_param
end

@define_custom_reverse_primitive(
    "rev_fix_param",
    arrow(t0, t1, arrow(t0, t1), t0),
    (body -> (param -> (fixer -> body))),
    reverse_fix_param()
)
