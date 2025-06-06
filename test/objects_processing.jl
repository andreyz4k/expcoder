using solver:
    Apply,
    Abstraction,
    Index,
    Hole,
    FreeVar,
    any_object,
    parse_program,
    is_reversible,
    tgrid,
    EitherOptions,
    PatternWrapper,
    every_primitive,
    t0,
    tcolor,
    run_in_reverse,
    fix_option_hashes,
    run_with_arguments,
    all_abstractors,
    calculate_dependent_vars,
    CombinedArgChecker,
    step_arg_checker,
    ArgTurn

@testset "Objects processing" begin
    function unfold_options(options::Dict)
        if all(x -> !isa(x, EitherOptions), values(options))
            return [options]
        end
        result = []
        for (i, item) in options
            if isa(item, EitherOptions)
                for (h, val) in item.options
                    new_option = Dict(k => fix_option_hashes([h], v) for (k, v) in options)
                    append!(result, unfold_options(new_option))
                end
                break
            end
        end
        return result
    end

    function compare_options(options, expected)
        if Set(unfold_options(options)) != Set(unfold_options(expected))
            @error options
            @error expected
            return false
        end
        return true
    end

    capture_free_vars(p, max_var = UInt64(0)) = p, max_var

    function capture_free_vars(p::Apply, max_var = UInt64(0))
        new_f, max_var = capture_free_vars(p.f, max_var)
        new_x, max_var = capture_free_vars(p.x, max_var)
        Apply(new_f, new_x), max_var
    end

    function capture_free_vars(p::Abstraction, max_var = UInt64(0))
        new_b, max_var = capture_free_vars(p.b, max_var)
        Abstraction(new_b), max_var
    end

    function capture_free_vars(p::Hole, max_var = UInt64(0))
        var_id = max_var + 1
        FreeVar(t0, t0, var_id, nothing), max_var + 1
    end

    function capture_free_vars(p::FreeVar, max_var = UInt64(0))
        if isnothing(p.var_id)
            var_id = max_var + 1
            FreeVar(t0, t0, var_id, p.location), max_var + 1
        else
            p, max_var
        end
    end

    @testcase_log "Select background" begin
        grid = [
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 9 9 9 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        ]
        select_background = Apply(
            Apply(
                Apply(
                    every_primitive["rev_select_grid"],
                    Abstraction(
                        Apply(
                            Apply(every_primitive["eq?"], Index(0)),
                            Hole(
                                t0,
                                t0,
                                [],
                                step_arg_checker(
                                    step_arg_checker(
                                        CombinedArgChecker([
                                            SimpleArgChecker(false, -1, true, nothing),
                                            all_abstractors[every_primitive["rev_select_grid"]][1][1][2],
                                        ]),
                                        ArgTurn(tcolor, tcolor),
                                    ),
                                    (every_primitive["eq?"], 2),
                                ),
                                nothing,
                            ),
                        ),
                    ),
                ),
                Hole(tgrid(tcolor), tgrid(tcolor), [], nothing, nothing),
            ),
            Hole(tgrid(tcolor), tgrid(tcolor), [], nothing, nothing),
        )
        @test is_reversible(select_background)

        select_background, _ = capture_free_vars(select_background)
        @test compare_options(
            run_in_reverse(select_background, grid, rand(UInt64)),
            Dict(
                0x0000000000000001 => EitherOptions(
                    Dict{UInt64,Any}(
                        0xfd29da2cf6a4bc92 => 7,
                        0x30dff9ab7c5f54e6 => 0,
                        0x919fc667709f16b6 => 9,
                        0x7888f4371e0a1750 => 2,
                    ),
                ),
                0x0000000000000002 => EitherOptions(
                    Dict{UInt64,Any}(
                        0xfd29da2cf6a4bc92 => PatternWrapper(
                            [
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object 7 7 7 any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object 7 any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object 7 7 7 any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                            ],
                        ),
                        0x30dff9ab7c5f54e6 => PatternWrapper(
                            [
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 any_object any_object any_object 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 any_object 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 any_object any_object any_object 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 any_object any_object any_object 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 any_object 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 any_object any_object any_object 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 any_object any_object 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 any_object any_object any_object 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 any_object any_object 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            ],
                        ),
                        0x919fc667709f16b6 => PatternWrapper(
                            [
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object 9 9 any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object 9 9 9 any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object 9 9 any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                            ],
                        ),
                        0x7888f4371e0a1750 => PatternWrapper(
                            [
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object 2 2 2 any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object 2 any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object 2 2 2 any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                                any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object any_object
                            ],
                        ),
                    ),
                ),
                0x0000000000000003 => EitherOptions(
                    Dict{UInt64,Any}(
                        0xfd29da2cf6a4bc92 => [
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 nothing nothing nothing 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 nothing 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 nothing nothing nothing 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 9 9 9 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        ],
                        0x30dff9ab7c5f54e6 => [
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
                            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
                        ],
                        0x919fc667709f16b6 => [
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 2 2 2 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 nothing nothing 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 nothing nothing nothing 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 nothing nothing 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        ],
                        0x7888f4371e0a1750 => [
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 7 7 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 nothing nothing nothing 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 nothing 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 nothing nothing nothing 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 9 9 9 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 9 9 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        ],
                    ),
                ),
            ),
        )
    end

    @testcase_log "Extract background" begin
        bgr_grid = [
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 any_object any_object any_object 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 any_object 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 any_object any_object any_object 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 any_object any_object any_object 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 any_object 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 any_object any_object any_object 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 any_object any_object 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 any_object any_object any_object 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 any_object any_object 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        ]
        extract_bgr = parse_program("(repeat_grid ??(color) ??(int) ??(int))")
        @test is_reversible(extract_bgr)
        extract_bgr, _ = capture_free_vars(extract_bgr)
        @test run_in_reverse(extract_bgr, bgr_grid, rand(UInt64)) ==
              Dict(UInt64(1) => 0, UInt64(2) => 17, UInt64(3) => 20)
        @test run_with_arguments(extract_bgr, [], Dict(UInt64(1) => 0, UInt64(2) => 17, UInt64(3) => 20)) == [
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        ]
    end

    @testcase_log "Non-background cells" begin
        grid = [
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing 7 7 7 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing 2 2 2 nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing 9 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing 9 9 nothing nothing nothing nothing nothing nothing nothing nothing nothing
            nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing nothing
        ]

        fetch_elements = parse_program("(rev_grid_elements ??(set(tuple2(tuple2(int, int), color))) ??(int) ??(int))")
        @test is_reversible(fetch_elements)
        fetch_elements, _ = capture_free_vars(fetch_elements)
        @test run_in_reverse(fetch_elements, grid, rand(UInt64)) == Dict(
            UInt64(1) => Set([
                ((19, 11), 9),
                ((5, 3), 7),
                ((18, 10), 9),
                ((5, 4), 7),
                ((11, 11), 2),
                ((9, 11), 2),
                ((10, 12), 2),
                ((5, 5), 7),
                ((17, 10), 9),
                ((19, 10), 9),
                ((18, 9), 9),
                ((3, 3), 7),
                ((3, 4), 7),
                ((18, 11), 9),
                ((11, 12), 2),
                ((9, 12), 2),
                ((11, 13), 2),
                ((17, 9), 9),
                ((3, 5), 7),
                ((4, 4), 7),
                ((9, 13), 2),
            ]),
            UInt64(2) => 20,
            UInt64(3) => 20,
        )
    end

    @testcase_log "Cluster nearby cells" begin
        cells = Set(
            Any[
                ((19, 11), 9),
                ((5, 3), 7),
                ((18, 10), 9),
                ((5, 4), 7),
                ((11, 11), 2),
                ((9, 11), 2),
                ((10, 12), 2),
                ((5, 5), 7),
                ((17, 10), 9),
                ((19, 10), 9),
                ((18, 9), 9),
                ((3, 3), 7),
                ((3, 4), 7),
                ((18, 11), 9),
                ((11, 12), 2),
                ((9, 12), 2),
                ((11, 13), 2),
                ((17, 9), 9),
                ((3, 5), 7),
                ((4, 4), 7),
                ((9, 13), 2),
            ],
        )
        group_cells = parse_program(
            "(rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (tuple2_first (tuple2_first \$0)) (tuple2_first (tuple2_first \$2)))) 1)) (not (gt? (abs (- (tuple2_second (tuple2_first \$0)) (tuple2_second (tuple2_first \$2)))) 1)))) \$0))) \$1 \$0))) empty_set ??(set(set(tuple2(tuple2(int, int), color)))))",
        )
        @test is_reversible(group_cells)
        group_cells, _ = capture_free_vars(group_cells)
        @test run_in_reverse(group_cells, cells, rand(UInt64)) == Dict(
            0x0000000000000001 => Set([
                Set([
                    ((18, 9), 9),
                    ((19, 11), 9),
                    ((17, 9), 9),
                    ((18, 10), 9),
                    ((18, 11), 9),
                    ((17, 10), 9),
                    ((19, 10), 9),
                ]),
                Set([
                    ((11, 12), 2),
                    ((10, 12), 2),
                    ((9, 12), 2),
                    ((11, 13), 2),
                    ((9, 13), 2),
                    ((11, 11), 2),
                    ((9, 11), 2),
                ]),
                Set([((3, 3), 7), ((5, 3), 7), ((3, 4), 7), ((5, 4), 7), ((4, 4), 7), ((3, 5), 7), ((5, 5), 7)]),
            ]),
        )
    end

    @testcase_log "Separate colors" begin
        groups = Set([
            Set([
                ((18, 9), 9),
                ((19, 11), 9),
                ((17, 9), 9),
                ((18, 10), 9),
                ((18, 11), 9),
                ((17, 10), 9),
                ((19, 10), 9),
            ]),
            Set([((11, 12), 2), ((10, 12), 2), ((9, 12), 2), ((11, 13), 2), ((9, 13), 2), ((11, 11), 2), ((9, 11), 2)]),
            Set([((3, 3), 7), ((5, 3), 7), ((3, 4), 7), ((5, 4), 7), ((4, 4), 7), ((3, 5), 7), ((5, 5), 7)]),
        ])
        repeat_colors = parse_program(
            "(map_set (lambda (map_set (lambda (tuple2 \$0 (tuple2_second \$1))) (tuple2_first \$0))) ??(set(tuple2(set(tuple2(int, int)), color))))",
        )
        @test is_reversible(repeat_colors)
        repeat_colors, _ = capture_free_vars(repeat_colors)
        @test run_in_reverse(repeat_colors, groups, rand(UInt64)) == Dict(
            0x0000000000000001 => Set(
                Tuple{Set{Tuple{Int64,Int64}},Int64}[
                    (Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]), 9),
                    (Set([(5, 5), (3, 3), (5, 3), (3, 4), (5, 4), (4, 4), (3, 5)]), 7),
                    (Set([(11, 13), (9, 13), (11, 11), (9, 11), (11, 12), (10, 12), (9, 12)]), 2),
                ],
            ),
        )
    end

    @testcase_log "Single object coordinates extraction" begin
        cells = Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)])
        extract_coordinates = parse_program(
            "(rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$v2)) (+ (tuple2_second \$0) (tuple2_second \$v2)))) \$v1) \$v2 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))",
        )
        @test is_reversible(extract_coordinates)
        extract_coordinates, _ = capture_free_vars(extract_coordinates)
        @test run_in_reverse(extract_coordinates, cells, rand(UInt64)) == Dict(
            0x0000000000000001 => Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)]),
            0x0000000000000002 => (17, 9),
        )
    end

    @testcase_log "Single object coordinates extraction 2" begin
        cells = Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)])
        extract_coordinates = parse_program(
            "((lambda (lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$2)) (+ (tuple2_second \$0) (tuple2_second \$2)))) \$0) \$1 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int)))))) (tuple2_first \$v1) (tuple2_second \$v1))",
        )
        @test is_reversible(extract_coordinates)
        extract_coordinates, _ = capture_free_vars(extract_coordinates)
        @test run_in_reverse(extract_coordinates, cells, rand(UInt64)) ==
              Dict(0x0000000000000001 => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])))
    end

    @testcase_log "Single object coordinates extraction 3" begin
        cells = Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)])
        extract_coordinates = parse_program(
            "(#(lambda (lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$2)) (+ (tuple2_second \$0) (tuple2_second \$2)))) \$0) \$1 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int)))))) (tuple2_first \$v1) (tuple2_second \$v1))",
        )
        @test is_reversible(extract_coordinates)
        extract_coordinates, _ = capture_free_vars(extract_coordinates)
        @test run_in_reverse(extract_coordinates, cells, rand(UInt64)) ==
              Dict(0x0000000000000001 => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])))
    end

    @testcase_log "Single object coordinates extraction 4" begin
        cells = Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)])
        extract_coordinates = parse_program(
            "((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first \$v1))) (tuple2_second \$v1))",
        )
        @test is_reversible(extract_coordinates)
        extract_coordinates, _ = capture_free_vars(extract_coordinates)
        @test run_in_reverse(extract_coordinates, cells, rand(UInt64)) ==
              Dict(0x0000000000000001 => ((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])))
    end

    @testcase_log "Get object coordinates" begin
        objects = Set(
            Tuple{Set{Tuple{Int64,Int64}},Int64}[
                (Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]), 9),
                (Set([(5, 5), (3, 3), (5, 3), (3, 4), (5, 4), (4, 4), (3, 5)]), 7),
                (Set([(11, 13), (9, 13), (11, 11), (9, 11), (11, 12), (10, 12), (9, 12)]), 2),
            ],
        )
        extract_coordinates = parse_program(
            "(map_set (lambda (tuple2 (#(lambda (lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$2)) (+ (tuple2_second \$0) (tuple2_second \$2)))) \$0) \$1 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int)))))) (tuple2_first (tuple2_first \$0)) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) ??(set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))))",
        )
        @test is_reversible(extract_coordinates)
        extract_coordinates, _ = capture_free_vars(extract_coordinates)
        @test run_in_reverse(extract_coordinates, objects, rand(UInt64)) == Dict(
            0x0000000000000001 => Set([
                (((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])), 9),
                (((3, 3), Set([(2, 2), (0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (0, 2)])), 7),
                (((9, 11), Set([(2, 2), (0, 2), (2, 0), (0, 0), (2, 1), (1, 1), (0, 1)])), 2),
            ]),
        )
    end

    @testcase_log "Get object coordinates 2" begin
        objects = Set(
            Tuple{Set{Tuple{Int64,Int64}},Int64}[
                (Set([(19, 10), (18, 9), (19, 11), (17, 9), (18, 10), (18, 11), (17, 10)]), 9),
                (Set([(5, 5), (3, 3), (5, 3), (3, 4), (5, 4), (4, 4), (3, 5)]), 7),
                (Set([(11, 13), (9, 13), (11, 11), (9, 11), (11, 12), (10, 12), (9, 12)]), 2),
            ],
        )
        extract_coordinates = parse_program(
            "(map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first \$0) (tuple2_first \$1)) (+ (tuple2_second \$0) (tuple2_second \$1)))) \$1) \$0 (lambda (tuple2 (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_first \$0)) (collect \$0)) max_int) (fold (lambda (lambda (if (gt? \$0 \$1) \$1 \$0))) (map (lambda (tuple2_second \$0)) (collect \$0)) max_int))))) (tuple2_first (tuple2_first \$1)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) ??(set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))))",
        )
        @test is_reversible(extract_coordinates)
        extract_coordinates, _ = capture_free_vars(extract_coordinates)
        @test run_in_reverse(extract_coordinates, objects, rand(UInt64)) == Dict(
            0x0000000000000001 => Set([
                (((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])), 9),
                (((3, 3), Set([(2, 2), (0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (0, 2)])), 7),
                (((9, 11), Set([(2, 2), (0, 2), (2, 0), (0, 0), (2, 1), (1, 1), (0, 1)])), 2),
            ]),
        )
    end

    @testcase_log "Select similar shape objects" begin
        objects = Set([
            (((17, 9), Set([(2, 1), (1, 0), (2, 2), (0, 0), (1, 1), (1, 2), (0, 1)])), 9),
            (((3, 3), Set([(2, 2), (0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (0, 2)])), 7),
            (((9, 11), Set([(2, 2), (0, 2), (2, 0), (0, 0), (2, 1), (1, 1), (0, 1)])), 2),
        ])
        select_objects = parse_program(
            "(rev_select_set (lambda (eq? (tuple2_second (tuple2_first \$0)) ??(set(tuple2(int, int))))) ??(set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))) ??(set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))))",
        )
        @test is_reversible(select_objects)
        select_objects, _ = capture_free_vars(select_objects)
        @test compare_options(
            run_in_reverse(select_objects, objects, rand(UInt64)),
            Dict(
                0x0000000000000001 => EitherOptions(
                    Dict{UInt64,Any}(
                        0x414a5726bfff0864 => Set([(0, 0), (1, 2), (1, 1), (0, 1), (2, 2), (2, 1), (1, 0)]),
                        0xe03e2a628b9e5b77 => Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)]),
                    ),
                ),
                0x0000000000000002 => EitherOptions(
                    Dict{UInt64,Any}(
                        0x414a5726bfff0864 =>
                            Set(Any[(((17, 9), Set([(0, 0), (1, 2), (1, 1), (0, 1), (2, 2), (2, 1), (1, 0)])), 9)]),
                        0xe03e2a628b9e5b77 => Set(
                            Any[
                                (((9, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                                (((3, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                            ],
                        ),
                    ),
                ),
                0x0000000000000003 => EitherOptions(
                    Dict{UInt64,Any}(
                        0x414a5726bfff0864 => Set(
                            Any[
                                (((9, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                                (((3, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                            ],
                        ),
                        0xe03e2a628b9e5b77 =>
                            Set(Any[(((17, 9), Set([(0, 0), (1, 2), (1, 1), (0, 1), (2, 2), (2, 1), (1, 0)])), 9)]),
                    ),
                ),
            ),
        )
    end

    @testcase_log "Move objects" begin
        objects = Set([
            (((9, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
            (((3, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
        ])
        move_objects = parse_program(
            "(map_set (lambda (tuple2 (tuple2 (tuple2 (+ (tuple2_first (tuple2_first (tuple2_first \$0))) \$v2) (tuple2_second (tuple2_first (tuple2_first \$0)))) (tuple2_second (tuple2_first \$0))) (tuple2_second \$0))) ??(set(tuple2(tuple2(tuple2(int, int), set(tuple2(int, int))), color))))",
        )
        @test is_reversible(move_objects)
        move_objects, _ = capture_free_vars(move_objects)
        @test calculate_dependent_vars(move_objects, Dict(0x0000000000000002 => 1), objects, rand(UInt64)) == Dict(
            0x0000000000000001 => Set([
                (((8, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                (((2, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
            ]),
        )

        @test calculate_dependent_vars(
            move_objects,
            Dict(
                0x0000000000000001 => Set([
                    (((8, 11), Set([(0, 0), (0, 2), (2, 0), (1, 1), (0, 1), (2, 2), (2, 1)])), 2),
                    (((2, 3), Set([(0, 0), (2, 0), (1, 1), (0, 1), (0, 2), (2, 2), (2, 1)])), 7),
                ]),
            ),
            objects,
            rand(UInt64),
        ) == Dict(0x0000000000000002 => 1)
    end
end
