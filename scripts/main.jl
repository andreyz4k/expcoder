
using solver

if abspath(PROGRAM_FILE) == @__FILE__
    ccall(:jl_exit_on_sigint, Cvoid, (Cint,), 0)
    solver.main()
end
