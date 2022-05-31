
using Test

using solver:
    every_primitive,
    Apply,
    Hole,
    tint,
    FreeVar,
    Abstraction,
    tlist,
    ttuple2,
    Index,
    get_reversed_filled_program,
    is_reversible
using DataStructures: OrderedDict, Accumulator
import Redis

@testset "Abstractors" begin
    @testset "Check reversible simple" begin
        @test is_reversible(Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing)))
    end

    @testset "Check reverrsible map" begin
        @test is_reversible(
            Apply(
                Apply(
                    every_primitive["map"],
                    Abstraction(Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing))),
                ),
                Hole(tlist(ttuple2(tint, tint)), nothing),
            ),
        )
    end

    @testset "Check reversible nested map" begin
        @test is_reversible(
            Apply(
                Apply(
                    every_primitive["map"],
                    Abstraction(
                        Apply(
                            Apply(
                                every_primitive["map"],
                                Abstraction(
                                    Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing)),
                                ),
                            ),
                            Hole(tlist(tlist(tint)), nothing),
                        ),
                    ),
                ),
                Hole(tlist(ttuple2(tlist(tint), tlist(tint))), nothing),
            ),
        )
    end

    @testset "Reverse repeat" begin
        skeleton = Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing))
        filled_p, rev_p = get_reversed_filled_program(skeleton)
        @test filled_p == Apply(Apply(every_primitive["repeat"], FreeVar(tint, nothing)), FreeVar(tint, nothing))
        @test rev_p([[1, 2, 3], [1, 2, 3]]) == ([1, 2, 3], 2)
        @test rev_p([1, 1, 1]) == (1, 3)
    end

    @testset "Reverse cons" begin
        skeleton = Apply(Apply(every_primitive["cons"], Hole(tint, nothing)), Hole(tint, nothing))
        filled_p, rev_p = get_reversed_filled_program(skeleton)
        @test filled_p == Apply(Apply(every_primitive["cons"], FreeVar(tint, nothing)), FreeVar(tint, nothing))
        @test rev_p([1, 2, 3]) == (1, [2, 3])
    end

    @testset "Reverse combined abstractors" begin
        skeleton = Apply(
            Apply(every_primitive["cons"], Hole(tint, nothing)),
            Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing)),
        )
        filled_p, rev_p = get_reversed_filled_program(skeleton)
        @test filled_p == Apply(
            Apply(every_primitive["cons"], FreeVar(tint, nothing)),
            Apply(Apply(every_primitive["repeat"], FreeVar(tint, nothing)), FreeVar(tint, nothing)),
        )
        @test rev_p([1, 2, 2, 2]) == (1, 2, 3)
    end

    @testset "Reverse map" begin
        skeleton = Apply(
            Apply(
                every_primitive["map"],
                Abstraction(Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing))),
            ),
            Hole(tlist(ttuple2(tint, tint)), nothing),
        )
        filled_p, rev_p = get_reversed_filled_program(skeleton)
        @test filled_p == Apply(
            Apply(
                every_primitive["map"],
                Abstraction(
                    Apply(
                        Apply(every_primitive["repeat"], Apply(every_primitive["tuple2_first"], Index(0))),
                        Apply(every_primitive["tuple2_second"], Index(0)),
                    ),
                ),
            ),
            Apply(Apply(every_primitive["zip2"], FreeVar(tlist(tint), nothing)), FreeVar(tlist(tint), nothing)),
        )
        @test rev_p([[1, 1, 1], [2, 2], [4]]) == ([1, 2, 4], [3, 2, 1])
    end

    @testset "Reverse nested map" begin
        skeleton = Apply(
            Apply(
                every_primitive["map"],
                Abstraction(
                    Apply(
                        Apply(
                            every_primitive["map"],
                            Abstraction(
                                Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing)),
                            ),
                        ),
                        Hole(tlist(tlist(tint)), nothing),
                    ),
                ),
            ),
            Hole(tlist(ttuple2(tlist(tint), tlist(tint))), nothing),
        )
        filled_p, rev_p = get_reversed_filled_program(skeleton)
        @test filled_p == Apply(
            Apply(
                every_primitive["map"],
                Abstraction(
                    Apply(
                        Apply(
                            every_primitive["map"],
                            Abstraction(
                                Apply(
                                    Apply(every_primitive["repeat"], Apply(every_primitive["tuple2_first"], Index(0))),
                                    Apply(every_primitive["tuple2_second"], Index(0)),
                                ),
                            ),
                        ),
                        Apply(
                            Apply(every_primitive["zip2"], Apply(every_primitive["tuple2_first"], Index(0))),
                            Apply(every_primitive["tuple2_second"], Index(0)),
                        ),
                    ),
                ),
            ),
            Apply(
                Apply(every_primitive["zip2"], FreeVar(tlist(tlist(tint)), nothing)),
                FreeVar(tlist(tlist(tint)), nothing),
            ),
        )
        @test rev_p([[[1, 1, 1], [2, 2], [4]], [[3, 3, 3, 3], [2, 2, 2], [8, 8, 8]]]) ==
              ([[1, 2, 4], [3, 2, 8]], [[3, 2, 1], [4, 3, 3]])
    end
end
