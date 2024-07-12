using CryptoMiniSat
using Test

#using Aqua
#Aqua.test_all(CryptoMiniSat, deps_compat = true)

@testset "Low-level CryptoMiniSat" begin
    p = CryptoMiniSat.cmsat_new()
    CryptoMiniSat.cmsat_new_vars(p, 3)
    @test CryptoMiniSat.cmsat_nvars(p) == 3

    CryptoMiniSat.cmsat_add_clause(p, [CMSLit(0,false)])
    CryptoMiniSat.cmsat_add_clause(p, [CMSLit(1,true)])
    CryptoMiniSat.cmsat_add_clause(p, [CMSLit(0,true),CMSLit(1,false),CMSLit(2,false)])

    @test CryptoMiniSat.cmsat_solve(p) == CryptoMiniSat.L_TRUE

    @test CryptoMiniSat.cmsat_get_model(p) == [0x00,0x01,0x00]

    @test CryptoMiniSat.cmsat_solve_with_assumptions(p, [CMSLit(2,true)]) == CryptoMiniSat.L_FALSE
    @test CryptoMiniSat.cmsat_solve(p) == CryptoMiniSat.L_TRUE

    CryptoMiniSat.cmsat_add_clause(p, [CMSLit(2,true)])
    @test CryptoMiniSat.cmsat_solve(p) == CryptoMiniSat.L_FALSE

    CryptoMiniSat.cmsat_free(p)
end

@testset "Top-level PicoSAT-like interface" begin
    cnf = [[1, -5, 4], [-1, 5, 3, 4], [-3, -4]]
    @test CryptoMiniSat.solve(cnf) == [-1, -2, -3, -4, -5]
    @test sort(collect(CryptoMiniSat.itersolve(cnf))) == Any[[-1, -2, -3, -4, -5], [-1, -2, -3, 4, -5], [-1, -2, -3, 4, 5], [-1, -2, 3, -4, -5], [-1, 2, -3, -4, -5], [-1, 2, -3, 4, -5], [-1, 2, -3, 4, 5], [-1, 2, 3, -4, -5], [1, -2, -3, -4, 5], [1, -2, -3, 4, -5], [1, -2, -3, 4, 5], [1, -2, 3, -4, -5], [1, -2, 3, -4, 5], [1, 2, -3, -4, 5], [1, 2, -3, 4, -5], [1, 2, -3, 4, 5], [1, 2, 3, -4, -5], [1, 2, 3, -4, 5]]
end

@testset "Top-level interface with symbols" begin
    cnf = [[XorLit(:coffee),XorLit(:tea)],[NotLit(:coffee),Lit(:cream)],[NotLit(:tea),Lit(:milk)]]
    @test Set(collect(itersolve(cnf))) == Set([Dict{Symbol, Bool}(:cream => 0, :milk => 1, :tea => 1, :coffee => 0),Dict{Symbol, Bool}(:cream => 1, :milk => 1, :tea => 1, :coffee => 0),Dict{Symbol, Bool}(:cream => 1, :milk => 1, :tea => 0, :coffee => 1),Dict{Symbol, Bool}(:cream => 1, :milk => 0, :tea => 0, :coffee => 1)])
end
