
using Test

using solver:
    every_primitive,
    Apply,
    Hole,
    tint,
    fill_free_holes,
    FreeVar,
    Abstraction,
    tlist,
    ttuple2,
    Index,
    get_reversed_program,
    EntriesBranch,
    EntryBranchItem,
    ValueEntry,
    ProgramBlock,
    is_reversible
using DataStructures: OrderedDict
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

    @testset "Fill simple holes" begin
        skeleton = Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing))
        @test fill_free_holes(skeleton) ==
              Apply(Apply(every_primitive["repeat"], FreeVar(tint, nothing)), FreeVar(tint, nothing))
    end

    @testset "Fill map holes" begin
        skeleton = Apply(
            Apply(
                every_primitive["map"],
                Abstraction(Apply(Apply(every_primitive["repeat"], Hole(tint, nothing)), Hole(tint, nothing))),
            ),
            Hole(tlist(ttuple2(tint, tint)), nothing),
        )
        @test fill_free_holes(skeleton) == Apply(
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
    end

    @testset "Fill nested map holes" begin
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
        @test fill_free_holes(skeleton) == Apply(
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
    end

    @testset "Reverse simple abstractor" begin
        forward = Apply(Apply(every_primitive["cons"], FreeVar(tint, nothing)), FreeVar(tint, nothing))
        entry = ValueEntry(tlist(tint), [], 0.0)
        var = (
            "key",
            EntriesBranch(
                Dict(
                    "key" => EntryBranchItem(
                        entry,
                        [OrderedDict{String,ProgramBlock}()],
                        Set(),
                        true,
                        true,
                        0.0,
                        entry.complexity,
                    ),
                ),
                nothing,
                Set(),
            ),
        )

        @test get_reversed_program(forward, var) == [
            Apply(every_primitive["car"], FreeVar(tlist(tint), "key")),
            Apply(every_primitive["cdr"], FreeVar(tlist(tint), "key")),
        ]
    end

    @testset "Reverse map abstractor" begin
        forward = Apply(
            Apply(
                every_primitive["map"],
                Abstraction(
                    Apply(
                        Apply(every_primitive["cons"], Apply(every_primitive["tuple2_first"], Index(0))),
                        Apply(every_primitive["tuple2_second"], Index(0)),
                    ),
                ),
            ),
            Apply(Apply(every_primitive["zip2"], FreeVar(tlist(tint), nothing)), FreeVar(tlist(tint), nothing)),
        )
        entry = ValueEntry(tlist(tlist(tint)), [], 0.0)
        var = (
            "key",
            EntriesBranch(
                Dict(
                    "key" => EntryBranchItem(
                        entry,
                        [OrderedDict{String,ProgramBlock}()],
                        Set(),
                        true,
                        true,
                        0.0,
                        entry.complexity,
                    ),
                ),
                nothing,
                Set(),
            ),
        )

        @test get_reversed_program(forward, var) == [
            Apply(
                Apply(every_primitive["map"], Abstraction(Apply(every_primitive["car"], Index(0)))),
                FreeVar(tlist(tlist(tint)), "key"),
            ),
            Apply(
                Apply(every_primitive["map"], Abstraction(Apply(every_primitive["cdr"], Index(0)))),
                FreeVar(tlist(tlist(tint)), "key"),
            ),
        ]
    end

    @testset "Reverse nested map abstractor" begin
        forward = Apply(
            Apply(
                every_primitive["map"],
                Abstraction(
                    Apply(
                        Apply(
                            every_primitive["map"],
                            Abstraction(
                                Apply(
                                    Apply(every_primitive["cons"], Apply(every_primitive["tuple2_first"], Index(0))),
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
        entry = ValueEntry(tlist(tlist(tlist(tint))), [], 0.0)
        var = (
            "key",
            EntriesBranch(
                Dict(
                    "key" => EntryBranchItem(
                        entry,
                        [OrderedDict{String,ProgramBlock}()],
                        Set(),
                        true,
                        true,
                        0.0,
                        entry.complexity,
                    ),
                ),
                nothing,
                Set(),
            ),
        )
        @test get_reversed_program(forward, var) == [
            Apply(
                Apply(
                    every_primitive["map"],
                    Abstraction(
                        Apply(
                            Apply(every_primitive["map"], Abstraction(Apply(every_primitive["car"], Index(0)))),
                            Index(0),
                        ),
                    ),
                ),
                FreeVar(tlist(tlist(tlist(tint))), "key"),
            ),
            Apply(
                Apply(
                    every_primitive["map"],
                    Abstraction(
                        Apply(
                            Apply(every_primitive["map"], Abstraction(Apply(every_primitive["cdr"], Index(0)))),
                            Index(0),
                        ),
                    ),
                ),
                FreeVar(tlist(tlist(tlist(tint))), "key"),
            ),
        ]
    end
end
