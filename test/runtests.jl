
using Test
include("../src/solver.jl")
using TestSetExtensions

@testset ExtendedTestSet "all" begin
    @includetests ARGS
end
