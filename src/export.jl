

function export_frontiers(number_enumerated, task, solutions)
    Dict(
        "number_enumerated" => number_enumerated,
        "request" => task.task_type,
        "solutions" => [
            Dict(
                "program" => s.hit_program,
                "time" => s.hit_time,
                "logLikelihood" => s.hit_likelihood,
                "logPrior" => s.hit_prior,
            ) for s in solutions
        ],
    )

end
