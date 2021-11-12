
using Base.Iterators: flatten


function bind_parsers(first_parser, continuation_func)
    function _bind_parse(s::String, n::Int64)
        first_results = first_parser(s, n)
        if isempty(first_results)
            return []
        end
        continuations = map(first_results) do token_pair
            token, new_n = token_pair
            next_parser = continuation_func(token)
            next_parser(s, new_n)
        end
        collect(flatten(continuations))
    end
end

branch_parsers(parsers...) = (s, n) -> collect(flatten([parser(s, n) for parser in parsers]))

return_parse(x) = (_, n) -> [(x, n)]

parse_failure(_, _) = []



constant_parser(k::String) = (s::String, n::Int64) -> begin
    if length(s) >= n + length(k) - 1 && s[n:n+length(k) - 1] == k
        [((), n + length(k))]
    else
        []
    end
end

token_parser(predicate; can_be_empty = false) =
    (s::String, n::Int64) -> begin
        max_passing_i = n - 1
        for i = n:length(s)
            if predicate(s[i])
                max_passing_i = i
            else
                break
            end
        end

        token = s[n:max_passing_i]
        if (!can_be_empty) && length(token) == 0
            []
        else
            [(token, n + length(token))]
        end
    end
