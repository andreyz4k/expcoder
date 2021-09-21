
struct Grammar
    log_variable::Float64
    library::Vector{Tuple{Program,Tp,Float64}}
    continuation_type::Union{Tp,Nothing}
end

struct ContextualGrammar
    no_context::Grammar
    variable_context::Grammar
    contextual_library::Vector{Tuple{Program,Vector{Grammar}}}
end


function deserialize_grammar(payload)
    log_variable = payload["logVariable"]

    productions = map(payload["productions"]) do p
        source = p["expression"]
        expression = parse_program(source)
        program_type = try
            infer_program_type(empty_context, [], expression)[2]
        catch e
            if isa(e, UnificationFailure)
                error("Could not type $source")
            else
                rethrow()
            end
        end
        log_probability = p["logProbability"]
        (expression, program_type, log_probability)
    end

    continuation_type = try
        deserialize_type(payload["continuationType"])
    catch
        nothing
    end

    #  Successfully parsed the grammar
    Grammar(log_variable, productions, continuation_type)
end


function make_dummy_contextual(g::Grammar)
    contextual_library = map(g.library) do (e, t, _)
        (e, [g for _ in arguments_of_type(t)])
    end
    cg = ContextualGrammar(g, g, contextual_library)
    prune_contextual_grammar(cg)
end


function _prune(expression, gs)
    t = closed_inference(expression)
    argument_types = arguments_of_type(t)

    map(zip(argument_types, gs)) do (arg_type, g)
        argument_type = return_of_type(arg_type)
        filtered_library = filter(g.library) do (_, child_type, _)
            child_type = return_of_type(child_type)
            try
                k, child_type = instantiate(child_type, empty_context)
                k, argument_type = instantiate(argument_type, k)
                unify(k, child_type, argument_type)
                return true
            catch e
                if isa(e, UnificationFailure)
                    return false
                else
                    rethrow()
                end
            end
        end
        Grammar(g.log_variable, filtered_library, g.continuation_type)
    end
end


function prune_contextual_grammar(g::ContextualGrammar)
    ContextualGrammar(g.no_context, g.variable_context, map(((e, gs),) -> (e, _prune(e, gs)), g.contextual_library))
end

function deserialize_contextual_grammar(payload)
    no_context = deserialize_grammar(payload["noParent"])
    variable_context = deserialize_grammar(payload["variableParent"])
    contextual_library = map(payload["productions"]) do production
        source = production["program"]
        expression = parse_program(source)
        children = map(deserialize_grammar, production["arguments"])
        (expression, children)
    end
    grammar = ContextualGrammar(no_context, variable_context, contextual_library)
    prune_contextual_grammar(grammar)
end
