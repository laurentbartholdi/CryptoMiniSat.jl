module CryptoMiniSat

import CryptoMiniSat_jll

export CMSLit, CMS, new_vars, nvars, add_clause, add_xor_clause, solve, get_model, get_conflict, itersolve, Lit, NotLit, XorLit, XNorLit

import Base: show, convert, iterate, IteratorSize

const libcms = CryptoMiniSat_jll.libcryptominisat5

const L_TRUE = 0x00
const L_FALSE = 0x01
const L_UNDEF = 0x02

################################################################
# low-level interface, CMSLit or 0-based

# the main structure
mutable struct CMS
    ptr::Ptr{Cvoid}
end
convert(::Type{Ptr{Cvoid}}, p::CMS) = p.ptr
"""`CMS(variables = 0; num_threads = Sys.CPU_THREADS)`

creates a new CryptoMiniSat problem, with optional number of variables and threas."""
function CMS(nvars::Int = 0; num_threads::Int = Sys.CPU_THREADS)
    p = cmsat_new()
    num_threads > 1 && cmsat_set_num_threads(p, num_threads)
    nvars > 0 && cmsat_new_vars(p, nvars)
    finalizer(cmsat_free, p)
    p
end
    
function Base.show(io::IO, p::CMS)
    if p.ptr == C_NULL
        print(io, "Unallocated CMS problem")
    else
        print(io, cmsat_nvars(p), "-variable CMS problem")
    end
end

# literals
struct CMSLit
    x::UInt32
end
CMSLit(v::Int) = CMSLit(v > 0 ? UInt32(2v-2) : v < 0 ? UInt32(-2v-1) : error("0 is not a valid literal"))
CMSLit(v::Int, invert::Bool) = CMSLit(UInt32(2v + (invert ? 1 : 0)))
Base.convert(::Type{CMSLit}, x::Int) = CMSLit(x)
Base.convert(::Type{Int}, x::CMSLit) = sign(x) ? -1-var(x) : 1+var(x)
Base.convert(::Type{Int32}, x::CMSLit) = Int32(convert(Int, x))
var(l::CMSLit) = Int(l.x >> 1)
sign(l::CMSLit) = Bool(l.x & 0x01)

function Base.show(io::IO, l::CMSLit)
    print(io, "CMSLit(",var(l),",",sign(l),")")
end
    
# constructor, destructor
cmsat_new() = ccall((:cmsat_new, libcms), CMS, ())
cmsat_free(p::CMS) = (ccall((:cmsat_free, libcms), Cvoid, (CMS,), p); p.ptr = C_NULL; nothing)

# add variables, clauses
cmsat_nvars(p::CMS) = ccall((:cmsat_nvars, libcms), Cint, (CMS,), p)
cmsat_add_clause(p::CMS, clause::Vector{CMSLit}) = Bool(ccall((:cmsat_add_clause, libcms), UInt8, (CMS,Ptr{CMSLit},Csize_t), p, clause, length(clause)))
cmsat_add_xor_clause(p::CMS, vars::Vector{Cuint}, rhs::Bool) = Bool(ccall((:cmsat_add_xor_clause, libcms), UInt8, (CMS,Ptr{Cuint},Csize_t,Cuint), p, vars, length(vars), rhs))
cmsat_new_vars(p::CMS, n::Int) = ccall((:cmsat_new_vars, libcms), Cvoid, (CMS,Csize_t), p, n)

# solve
cmsat_solve(p::CMS) = ccall((:cmsat_solve, libcms), UInt8, (CMS,), p)
cmsat_solve_with_assumptions(p::CMS, assumptions::Vector{CMSLit}) = ccall((:cmsat_solve_with_assumptions, libcms), UInt8, (CMS,Ptr{CMSLit},Csize_t), p, assumptions, length(assumptions))
cmsat_get_model(p::CMS) = unsafe_wrap(Array, ccall((:cmsat_get_model, libcms), Tuple{Ptr{UInt8},Csize_t}, (CMS,), p)...)
cmsat_get_conflict(p::CMS) = unsafe_wrap(Array, ccall((:cmsat_get_conflict, libcms), Tuple{Ptr{CMSLit},Csize_t}, (CMS,), p)...)

cmsat_print_stats(p::CMS) = ccall((:cmsat_print_stats, libcms), Cvoid, (CMS,), p)
cmsat_set_num_threads(p::CMS, n::Int) = ccall((:cmsat_set_num_threads, libcms), Cvoid, (CMS,Cuint), p, n)
cmsat_set_verbosity(p::CMS, n::Int) = ccall((:cmsat_set_verbosity, libcms), Cvoid, (CMS,Cuint), p, n)
cmsat_set_default_polarity(p::CMS, polarity::Int) = ccall((:cmsat_set_default_polarity, libcms), Cvoid, (CMS,Cint), p, polarity)
cmsat_set_polarity_auto(p::CMS) = ccall((:cmsat_set_polarity_auto, libcms), Cvoid, (CMS,), p)
cmsat_set_no_simplify(p::CMS) = ccall((:cmsat_set_no_simplify, libcms), Cvoid, (CMS,), p)
cmsat_set_no_simplify_at_startup(p::CMS) = ccall((:cmsat_set_no_simplify_at_startup, libcms), Cvoid, (CMS,), p)
cmsat_set_no_equivalent_lit_replacement(p::CMS) = ccall((:cmsat_set_no_equivalent_lit_replacement, libcms), Cvoid, (CMS,), p)
cmsat_set_no_bva(p::CMS) = ccall((:cmsat_set_no_bva, libcms), Cvoid, (CMS,), p)
cmsat_set_no_bve(p::CMS) = ccall((:cmsat_set_no_bve, libcms), Cvoid, (CMS,), p)
cmsat_set_up_for_scalmc(p::CMS) = ccall((:cmsat_set_up_for_scalmc, libcms), Cvoid, (CMS,), p)
cmsat_set_yes_comphandler(p::CMS) = ccall((:cmsat_set_yes_comphandler, libcms), Cvoid, (CMS,), p)
cmsat_simplify(p::CMS, assumptions::Vector{CMSLit}) = Bool(ccall((:cmsat_simplify, libcms), UInt8, (CMS,Ptr{CMSLit},Csize_t), p, clause, length(clause)))
cmsat_set_max_time(p::CMS, max_time::Float64) = ccall((:cmsat_set_max_time, libcms), Cvoid, (CMS,Float64), p, max_time)

################################################################
# higher-level interface, 1-based

"""`new_vars(p::CMS, n::Int)`

Add `n` new variables to the system `p`"""
new_vars(p::CMS, n::Int) = cmsat_new_vars(p, n)

"""`nvars(p::CMS)::Int`

Return the number of variables in the system `p`"""
nvars(p::CMS) = cmsat_nvars(p)

"""`add_clause(p::CMS, clause::Vector{Union{CMSLit,Integer}})::Bool`

Add a clause to the system, namely the disjunction of the entries in `clause`.
Direct terms are integers are numbered from 1, inverted terms are negative numbered from -1. They may also be specified as `CMSLit(variable,invert)`."""
add_clause(p::CMS, clause::Vector{CMSLit}) = cmsat_add_clause(p,clause)
function add_clause(p::CMS, clause::Vector{T}) where T <: Integer
    c = convert(Vector{CMSLit},clause)
    m = -1
    for l in c
        m = max(m,var(l))
    end
    if m ≥ nvars(p)
        new_vars(p, m+1-nvars(p))
    end
    cmsat_add_clause(p,c)
end

"""`add_clauses(p::CMS, clauses::Vector)`

Adds all `clauses` to `p`."""
function add_clauses(p::CMS, clauses)
    for item in clauses
        add_clause(p, item)
    end
end

"""`add_xor_clause(p::CMS, clause::Vector{Union{CMSLit,Int}}, rhs::Bool)::Bool`

Adds an XOR clause to `p`. This is a clause of the form `x_1 ⊻ x_2 ⊻ ... ⊻ x_n = rhs`."""
add_xor_clause(p::CMS, clause::Vector{UInt32}, rhs::Bool = true) = cmsat_add_xor_clause(p, clause, rhs)
function add_xor_clause(p::CMS, clause::Union{Vector{CMSLit},Vector{T}}, rhs = true) where T <: Integer
    cc = UInt32[]
    m = -1
    for c in clause
        if isa(c, CMSLit)
            x = var(c)
            rhs ⊻= sign(c)
        elseif c>0
            x = c-1
        elseif c<0
            x = -c-1
            rhs = !rhs
        else
            error("0 is not a valid literal")
        end
        m = max(m,x)
        push!(cc,x)
    end
    if m ≥ nvars(p)
        new_vars(p, m+1-nvars(p))
    end    
    cmsat_add_xor_clause(p, cc, rhs)
end

"""`add_xor_clauses(p::CMS, clauses::Vector)`

Adds all XOR `clauses` to `p`."""
function add_xor_clauses(p::CMS, clauses)
    for item in clauses
        add_xor_clause(p, item)
    end
end

Cbool2Bool(v) = (v == 0x02 ? :undefined : v == 0x01 ? false : true)
"""`solve(p::CMS, assumptions=[])`

returns whether `p` is solvable; possibly returns :undefined."""
solve(p::CMS) = Cbool2Bool(cmsat_solve(p))
function solve(p::CMS, assumptions::Vector{Union{CMSLit,Integer}})
    c = convert(Vector{CMSLit},assumptions)
    m = -1
    for l in c
        m = max(m,var(l))
    end
    if m ≥ nvars(p)
        new_vars(p, m+1-nvars(p))
    end
    Cbool2Bool(cmsat_solve_with_assumptions(p,c))
end

"""`get_model(p::CMS)::Vector{Bool}`

returns the variables in the current solution to `p`. This assumes that `solve(p)` was called and returned `true`."""
function get_model(p::CMS)
    map(Cbool2Bool,cmsat_get_model(p))
end

"""`get_conflict(p::CMS)::Vector{CMSLit}`

returns the conflicting variables in the current solution to `p`. This assumes that `solve(p)` was called and returned `false`"""
function get_conflict(p::CMS)
    cmsat_get_conflict(p)
end

################################################################
# top-level interface, creating / destructing CMS object in one go.
# the syntax is compatible with e.g. PicoSAT

function create_problem(clauses, vars, verbose, num_threads)
    numvars = -1
    for c=clauses, l=c
        numvars = max(numvars,abs(l))
    end
    if vars == -1
        vars = numvars
    end
    vars < numvars && error("There are more variables than specified")

    p = CMS(vars; num_threads = num_threads)
    cmsat_set_verbosity(p, verbose)
    add_clauses(p, clauses)
    p
end

"""
`solve(clauses; vars::Integer=-1, verbose::Integer=0, proplimit::Integer=0, num_threads::Int = Sys.CPU_THREADS)`
   - `vars` - the number of variables (will be inferred if not specified)
   - `verbose` - verbosity
   - `proplimit` - ignored
   - `num_threads` - number of CPU threads to use
Returns a solution if the problem is satisfiable.
Satisfiable solutions are represented as a vector of signed integers.
If the problem is not satisfiable the method returns an `:unsatisfiable` symbol.
```julia
julia> import CryptoMiniSat
julia> cnf = [[1, -5, 4], [-1, 5, 3, 4], [-3, -4]];
julia> CryptoMiniSat.solve(cnf)
5-element Array{Int64,1}:
 -1
 -2
 -3
 -4
 -5
```
"""
function solve(clauses::Vector{Vector{T}};
               vars::Integer=-1,
               verbose::Integer=0,
               proplimit::Integer=0,
               num_threads::Integer=Sys.CPU_THREADS) where T <: Integer
    p = create_problem(clauses, vars, verbose, num_threads)
    if solve(p)
        sol = get_model(p)
        return [sol[i] ? i : -i for i=1:length(sol)]
    else
        return :unsatisfiable
    end
end

struct CMSIterator
    p::CMS
end
"""
`itersolve(clauses; vars::Integer=-1, verbose::Integer=0, proplimit::Integer=0, num_threads::Integer=Sys.CPU_THREADS)`
   - `vars` - the number of variables
   - `verbose` - verbosity
   - `proplimit` - ignored
   - `num_threads` - number of CPU threads to use

Returns an iterable object over all solutions.

```julia
julia> import CryptoMiniSat
julia> cnf = [[1, -5, 4], [-1, 5, 3, 4], [-3, -4]];
julia> collect(CryptoMiniSat.itersolve(cnf))
18-element Array{Any,1}:
 [-1, -2, -3, -4, -5]
 [-1, 2, -3, -4, -5]
 [-1, 2, 3, -4, -5]
 [1, 2, 3, -4, 5]
 [-1, -2, -3, 4, -5]
 [1, -2, 3, -4, 5]
 [-1, -2, -3, 4, 5]
 [-1, 2, -3, 4, -5]
 [1, -2, -3, 4, 5]
 [1, 2, -3, 4, 5]
 [1, 2, -3, 4, -5]
 [-1, 2, -3, 4, 5]
 [1, -2, -3, 4, -5]
 [1, -2, 3, -4, -5]
 [-1, -2, 3, -4, -5]
 [1, 2, -3, -4, 5]
 [1, -2, -3, -4, 5]
 [1, 2, 3, -4, -5]
```
"""
function itersolve(clauses::Vector{Vector{T}};
                   vars::Integer=-1,
                   verbose::Integer=0,
                   proplimit::Integer=0,
                   num_threads::Integer=Sys.CPU_THREADS) where T <: Integer
    p = create_problem(clauses, vars, verbose, num_threads)
    return CMSIterator(p)
end

function Base.iterate(it::CMSIterator, state=nothing)
    if solve(it.p)
        v = get_model(it.p)
        sol = [v[i] ? i : -i for i=1:length(v)]

        # add inverse sol for next iter
        add_clause(it.p, -sol)
        return (sol, nothing)
    else
        return nothing
    end
end

IteratorSize(it::CMSIterator) = Base.SizeUnknown()

################################################################
# super-top level interface, in which the terms are arbitrary, and
# coded into integers by a Dictionary

struct Lit{T}
    x::T
    sign::Int
end

"""
`Lit(x,inverted::Bool = false)`
Creates a literal `x`
"""
Lit(x::T,inverted::Bool = false) where T = Lit{T}(x,inverted)

"""
`NotLit(x)`
Creates a negated literal `x`; this is equivalent to `Lit(x,true)`
"""
NotLit(x::T) where T = Lit{T}(x,true)

"""
`XorLit(x)`
Creates a literal `x`, to be used in an XOR clause
"""
XorLit(x::T) where T = Lit{T}(x,-2)

"""
`XNorLit(x)`
Creates a negated literal `x`, to be used in an XOR clause
"""
XNorLit(x::T) where T = Lit{T}(x,-1)

function Base.show(io::IO,x::Lit{T}) where T
    isodd(x.sign) && print(io,"¬")
    x.sign<0 && print(io,"⊻")
    show(io,x.x)
end

function create_problem(clauses::Vector{Vector{Lit{T}}}, verbose, num_threads) where T
    vardict = Dict{T,Int32}()
    varlist = T[]

    for c=clauses, l=c
        haskey(vardict,l.x) && continue
        push!(varlist,l.x)
        vardict[l.x] = length(varlist)
    end

    p = CMS(length(varlist); num_threads = num_threads)
    cmsat_set_verbosity(p, verbose)
    
    for c=clauses
        is_xor = any(l->l.sign<0,c)
        is_xor == all(l->l.sign<0,c) || error("Clause $c contains a mix of Xor and usual terms")
        if is_xor
            rhs = true
            newc = UInt32[]
            for l=c
                push!(newc, vardict[l.x]-1)
                rhs ⊻= Bool(l.sign&1)
            end
            add_xor_clause(p, newc, rhs)
        else
            newc = CMSLit[]
            for l=c
                push!(newc, CMSLit(vardict[l.x]-1,Bool(l.sign)))
            end
            add_clause(p, newc)
        end
    end
    (p, vardict, varlist)
end

"""
`solve(clauses; verbose::Integer=0, num_threads::Int = Sys.CPU_THREADS)`
   - `verbose` - verbosity
   - `num_threads` - number of CPU threads to use
Returns a solution if the problem is satisfiable.
Satisfiable solutions are represented as a dictionary.

The first argument is a vector of clauses. Each clause is a vector of
literals of, each encapsulated in `Lit(T)`, `NotLit(T)`, `XorLit(T)`
or `XNorLit(T)` for some type `T`. Each clause containing XorLit and
XNotLit terms is an XOR clause, and the number of satisfied clauses
must have the same parity as the number of NotLit and XNorLit for the
clause to be satified. Clauses containing Lit and NotLit terms are
usual disjunctive clauses.

If the problem is not satisfiable the method returns an `:unsatisfiable` symbol.
```julia
julia> import CryptoMiniSat
julia> # coffee with cream, tea with milk
julia> cnf = [[XorLit(:coffee),XorLit(:tea)],[NotLit(:coffee),Lit(:cream)],[NotLit(:tea),Lit(:milk)]];
julia> CryptoMiniSat.solve(cnf)
Dict{Symbol, Bool} with 3 entries:
  :cream  => 0
  :milk   => 1
  :tea    => 1
  :coffee => 0
```
"""
function solve(clauses::Vector{Vector{Lit{T}}};
               verbose::Integer=0,
               num_threads::Integer=Sys.CPU_THREADS) where T
    (p, vardict, varlist) = create_problem(clauses, verbose, num_threads)
    if solve(p)
        sol = get_model(p)
        return Dict(varlist[i] => sol[i] for i=1:length(sol))
    else
        return :unsatisfiable
    end
end

struct CMSDIterator{T}
    p::CMS
    d::Dict{T,UInt32}
    l::Vector{T}
end

"""
`itersolve(clauses; verbose::Integer=0, num_threads::Integer=Sys.CPU_THREADS)`
   - `verbose` - verbosity
   - `num_threads` - number of CPU threads to use

The first argument is a vector of clauses. Each clause is a vector of
literals of, each encapsulated in `Lit(T)`, `NotLit(T)`, `XorLit(T)`
or `XNorLit(T)` for some type `T`. Each clause containing XorLit and
XNotLit terms is an XOR clause, and the number of satisfied clauses
must have the same parity as the number of NotLit and XNorLit for the
clause to be satified. Clauses containing Lit and NotLit terms are
usual disjunctive clauses.

Returns an iterable object over all solutions.
```julia
julia> import CryptoMiniSat
julia> # coffee with cream, tea with milk
julia> cnf = [[XorLit(:coffee),XorLit(:tea)],[NotLit(:coffee),Lit(:cream)],[NotLit(:tea),Lit(:milk)]];
julia> collect(CryptoMiniSat.itersolve(cnf))
4-element Vector{Any}:
 Dict{Symbol, Bool}(:cream => 0, :milk => 1, :tea => 1, :coffee => 0)
 Dict{Symbol, Bool}(:cream => 1, :milk => 1, :tea => 1, :coffee => 0)
 Dict{Symbol, Bool}(:cream => 1, :milk => 1, :tea => 0, :coffee => 1)
 Dict{Symbol, Bool}(:cream => 1, :milk => 0, :tea => 0, :coffee => 1)
```
"""
function itersolve(clauses::Vector{Vector{Lit{T}}};
                   verbose::Integer=0,
                   num_threads::Integer=Sys.CPU_THREADS) where T
    (p, vardict, varlist) = create_problem(clauses, verbose, num_threads)
    return CMSDIterator{T}(p, vardict, varlist)
end

function Base.iterate(it::CMSDIterator, state=nothing)
    if solve(it.p)
        v = get_model(it.p)

        # add inverse sol for next iter
        add_clause(it.p, [v[i] ? -i : i for i=1:length(v)])
        return (Dict(it.l[i] => v[i] for i=1:length(v)), nothing)
    else
        return nothing
    end
end

IteratorSize(it::CMSDIterator) = Base.SizeUnknown()

end
