
using Distributed
if myid() != 1
    # cd("test")
else
    cd("..")
    addprocs(Threads.nthreads())
    @everywhere using XUnit
end

runtests("test/all_tests.jl", ["all/" * a for a in ARGS]...)
