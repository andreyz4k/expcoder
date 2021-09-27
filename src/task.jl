

struct Task
    name::String
    task_type::Tp
    log_likelihood_checker::Any
    train_inputs::Any
    train_outputs::Any
    test_inputs::Any
    test_outputs::Any
end

@enum MatchResult Strict Pattern TypeOnly NoMatch


supervised_task_checker(task::Task, p::Program) =
    if all(
        try
            evaluate_program(p, xs) == y
        catch e
            if isa(e, UnknownPrimitive)
                error("Unknown primitive: $(e.name)")
            elseif isa(e, EnumerationTimeout)
                rethrow()
            else
                false
            end
        end for (xs, y) in zip(vcat(task.train_inputs, task.test_inputs), vcat(task.train_outputs, task.test_outputs))
    )
        0.0
    else
        1.0
    end


function build_task(handler, name, task_type, examples, test_examples)
    Task(
        name,
        task_type,
        handler,
        [ex["inputs"] for ex in examples],
        [ex["output"] for ex in examples],
        [ex["inputs"] for ex in test_examples],
        [ex["output"] for ex in test_examples],
    )
end
