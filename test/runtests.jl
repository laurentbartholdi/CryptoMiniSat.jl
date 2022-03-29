using CryptoMiniSat
using Aqua
using Test

Aqua.test_all(CryptoMiniSat, deps_compat = true)

@testset "Low-level CryptoMiniSat" begin
    p = CryptoMiniSat.cms_new()
    CryptoMiniSat.cms_new_vars(p, 3)
    @test CryptoMiniSat.cms_nvars(p) == 3

    CryptoMiniSat.cms_add_clause(p, [Lit(0,false)])
    CryptoMiniSat.cms_add_clause(p, [Lit(1,true)])
    CryptoMiniSat.cms_add_clause(p, [Lit(0,true),Lit(1,false),Lit(2,false)])

    @test CryptoMiniSat.cms_solve(p) == CryptoMiniSat.L_TRUE

    @test CryptoMiniSat.cms_get_model(p) == [0x00,0x01,0x00]

    @test CryptoMiniSat.cms_solve_with_assumptions(p, [Lit(2,true)]) == CryptoMiniSat.L_FALSE
    @test CryptoMiniSat.cms_solve(p) == CryptoMiniSat.L_TRUE

    CryptoMiniSat.cms_add_clause(p, [Lit(2,true)])
    @test CryptoMiniSat.cms_solve(p) == CryptoMiniSat.L_FALSE

    CryptoMiniSat.cms_free(p)
end

@testset "Top-level PicoSAT-like interface" begin
    cnf = Any[[1, -5, 4], [-1, 5, 3, 4], [-3, -4]]
    @test CryptoMiniSat.solve(cnf) == [-1, -2, -3, -4, -5]
    @test sort(collect(CryptoMiniSat.itersolve(cnf))) == Any[[-1, -2, -3, -4, -5], [-1, -2, -3, 4, -5], [-1, -2, -3, 4, 5], [-1, -2, 3, -4, -5], [-1, 2, -3, -4, -5], [-1, 2, -3, 4, -5], [-1, 2, -3, 4, 5], [-1, 2, 3, -4, -5], [1, -2, -3, -4, 5], [1, -2, -3, 4, -5], [1, -2, -3, 4, 5], [1, -2, 3, -4, -5], [1, -2, 3, -4, 5], [1, 2, -3, -4, 5], [1, 2, -3, 4, -5], [1, 2, -3, 4, 5], [1, 2, 3, -4, -5], [1, 2, 3, -4, 5]]
end
