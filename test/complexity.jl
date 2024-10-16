
using DataStructures

using solver: get_complexity_summary, tlist, tint, tgrid, tcolor

@testset "Test complexity" begin
    @testcase_log "list complexity" begin
        l = [1, 2, 3]
        t = tlist(tint)
        s, m, c = get_complexity_summary([l], t)
        @test s == Accumulator("list" => 1, "int" => 3)
        @test m == Accumulator("list" => 1, "int" => 3)
        @test c == 1

        s, m, c = get_complexity_summary([l, l], t)
        @test s == Accumulator("list" => 2, "int" => 6)
        @test m == Accumulator("list" => 1, "int" => 3)
        @test c == 2

        ll = [[1, 2, 3], [1, 2, 3]]
        tt = tlist(tlist(tint))
        ss, mm, cc = get_complexity_summary([ll], tt)
        @test ss == Accumulator("list" => 3, "int" => 6)
        @test mm == Accumulator("list" => 3, "int" => 6)
        @test cc == 1
    end

    @testcase_log "grid complexity" begin
        g = [1 2 3; 4 5 6]
        t = tgrid(tcolor)
        s, m, c = get_complexity_summary([g], t)
        @test s == Accumulator("grid" => 1, "color" => 6)
        @test m == Accumulator("grid" => 1, "color" => 6)
        @test c == 1
    end
end
