
struct Task
    name::String
    task_type::Tp
    log_likelihood_checker::Any
    train_inputs::Any
    train_outputs::Any
    test_inputs::Any
    test_outputs::Any
end

function _test_one_example(p, xs, y)
    try
        run_with_arguments(p, [], Dict{Any,Any}(xs)) == y
    catch e
        if isa(e, UnknownPrimitive)
            error("Unknown primitive: $(e.name)")
        elseif isa(e, InterruptException) || isa(e, AssertionError) || isa(e, MethodError)
            # bt = catch_backtrace()
            # @error "Error while testing example" exception = (e, bt)
            rethrow()
        elseif isa(e, EnumerationException) || isa(e, ErrorException)
            # bt = catch_backtrace()
            # @error "Error while testing example" exception = (e, bt)
            return false
        else
            bt = catch_backtrace()
            @error "Error while testing example" exception = (e, bt)
            @error p
            @error xs
            @error y
            return false
        end
    end
end

function supervised_task_checker(task::Task, p::Program)
    # p_analized = analyze_evaluation(p)
    for i in 1:length(task.train_inputs)
        if !_test_one_example(p, task.train_inputs[i], task.train_outputs[i])
            return log(0)
        end
    end
    for i in 1:length(task.test_inputs)
        if !_test_one_example(p, task.test_inputs[i], task.test_outputs[i])
            return log(0)
        end
    end
    return 0.0
end
