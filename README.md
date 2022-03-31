# CryptoMiniSat

This is a user interface, in Julia, to the [CryptoMiniSat](https://github.com/msoos/cryptominisat) SAT solver.

It exposes all the functions of the C interface, in the same syntax (cmsat_new, etc.), and provides higher-level interfaces:
- the same functions as in the C interface, without `cmsat_`, accept 1-based variables of any integer type (rather than the 0-based UInt32)
- a high-level `solve(clauses; ...)` function that accepts a vector of vectors of clauses, represented as integers (negative for negated terms) for one-go solving, as well as an iterator `itersolve(clauses; ...)`
- a higher-level `solve(clauses; ...)` in which the terms of the clauses are `Lit(x)`, `NotLit(x)` or generally `Lit(x,negated::Bool)` for usual clauses, and `x` may be of any type; or the terms are of the form `XorLit(x)` and `XNorLit(x)` for XOR-clauses, in which the number of non-satisfied terms should have the same parity as the number of XNorLit terms.

```julia
julia> using CryptoMiniSat
julia> # simple clauses
julia> cnf = [[1, -5, 4], [-1, 5, 3, 4], [-3, -4]];
julia> solve(cnf)
5-element Array{Int64,1}:
 -1
 -2
 -3
 -4
 -5
julia> # coffee with cream, tea with milk
julia> cnf = [[XorLit(:coffee),XorLit(:tea)],[NotLit(:coffee),Lit(:cream)],[NotLit(:tea),Lit(:milk)]]
julia> collect(itersolve(cnf))
4-element Vector{Any}:
 Dict{Symbol, Bool}(:cream => 0, :milk => 1, :tea => 1, :coffee => 0)
 Dict{Symbol, Bool}(:cream => 1, :milk => 1, :tea => 1, :coffee => 0)
 Dict{Symbol, Bool}(:cream => 1, :milk => 1, :tea => 0, :coffee => 1)
 Dict{Symbol, Bool}(:cream => 1, :milk => 0, :tea => 0, :coffee => 1)
```


