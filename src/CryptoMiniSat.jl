module CryptoMiniSat

import CryptoMiniSat_jll

using Aqua

export Lit, CMS, new_vars, nvars, add_clause, add_xor_clause, solve, get_model, get_conflict, itersolve

import Base: show, convert, iterate, IteratorSize

const libcms = CryptoMiniSat_jll.libcryptominisat5

const L_TRUE = 0x00
const L_FALSE = 0x01
const L_UNDEF = 0x02

# the main structure
mutable struct CMS
    ptr::Ptr{Cvoid}
end
convert(::Type{Ptr{Cvoid}}, p::CMS) = p.ptr
"""`CMS(variables = 0; num_threads = Sys.CPU_THREADS)`

creates a new CryptoMiniSat problem, with optional number of variables and threas."""
function CMS(nvars::Int = 0; num_threads::Int = Sys.CPU_THREADS)
    p = cms_new()
    num_threads > 1 && cms_set_num_threads(p, num_threads)
    nvars > 0 && cms_new_vars(p, nvars)
    finalizer(cms_free, p)
    p
end
    
function Base.show(io::IO, p::CMS)
    if p.ptr == C_NULL
        print(io, "Unallocated CMS problem")
    else
        print(io, cms_nvars(p), "-variable CMS problem")
    end
end

# literals
struct Lit
    x::UInt32
end
Lit(v::Int) = Lit(v > 0 ? UInt32(2v-2) : v < 0 ? UInt32(-2v-1) : error("0 is not a valid literal"))
Lit(v::Int, invert::Bool) = Lit(UInt32(2v + (invert ? 1 : 0)))
Base.convert(::Type{Lit}, x::Int) = Lit(x)
Base.convert(::Type{Int}, x::Lit) = sign(x) ? -1-var(x) : 1+var(x)
Base.convert(::Type{Int32}, x::Lit) = Int32(convert(Int, x))
var(l::Lit) = Int(l.x >> 1)
sign(l::Lit) = Bool(l.x & 0x01)

function Base.show(io::IO, l::Lit)
    print(io, "Lit(",var(l),",",sign(l),")")
end
    
# constructor, destructor
cms_new() = ccall((:cmsat_new, libcms), CMS, ())
cms_free(p::CMS) = (ccall((:cmsat_free, libcms), Cvoid, (CMS,), p); p.ptr = C_NULL; nothing)

# add variables, clauses
cms_nvars(p::CMS) = ccall((:cmsat_nvars, libcms), Cint, (CMS,), p)
cms_add_clause(p::CMS, clause::Vector{Lit}) = Bool(ccall((:cmsat_add_clause, libcms), UInt8, (CMS,Ptr{Lit},Csize_t), p, clause, length(clause)))
cms_add_xor_clause(p::CMS, vars::Vector{Cuint}, rhs::Bool) = Bool(ccall((:cmsat_add_xor_clause, libcms), UInt8, (CMS,Ptr{Cuint},Csize_t,Cuint), p, vars, length(vars), rhs))
cms_new_vars(p::CMS, n::Int) = ccall((:cmsat_new_vars, libcms), Cvoid, (CMS,Csize_t), p, n)

# solve
cms_solve(p::CMS) = ccall((:cmsat_solve, libcms), UInt8, (CMS,), p)
cms_solve_with_assumptions(p::CMS, assumptions::Vector{Lit}) = ccall((:cmsat_solve_with_assumptions, libcms), UInt8, (CMS,Ptr{Lit},Csize_t), p, assumptions, length(assumptions))
cms_get_model(p::CMS) = unsafe_wrap(Array, ccall((:cmsat_get_model, libcms), Tuple{Ptr{UInt8},Csize_t}, (CMS,), p)...)
cms_get_conflict(p::CMS) = unsafe_wrap(Array, ccall((:cmsat_get_conflict, libcms), Tuple{Ptr{Lit},Csize_t}, (CMS,), p)...)

cms_set_num_threads(p::CMS, n::Int) = ccall((:cmsat_set_num_threads, libcms), Cvoid, (CMS,Cuint), p, n)

################################################################
# higher-level interface

"""`new_vars(p::CMS, n::Int)`

Add `n` new variables to the system `p`"""
new_vars(p::CMS, n::Int) = cms_new_vars(p, n)

"""`nvars(p::CMS)::Int`

Return the number of variables in the system `p`"""
nvars(p::CMS) = cms_nvars(p)

"""`add_clause(p::CMS, clause::Vector{Union{Lit,Int}})::Bool`

Add a clause to the system, namely the disjunction of the entries in `clause`.
Direct terms are integers are numbered from 1, inverted terms are negative numbered from -1. They may also be specified as `Lit(variable,invert)`."""
add_clause(p::CMS, clause::Vector{Lit}) = cms_add_clause(p,clause)
function add_clause(p::CMS, clause)
    c = convert(Array{Lit},clause)
    m = -1
    for l in c
        m = max(m,var(l))
    end
    if m ≥ nvars(p)
        new_vars(p, m+1-nvars(p))
    end
    cms_add_clause(p,c)
end

"""`add_clauses(p::CMS, clauses::Vector)`

Adds all `clauses` to `p`."""
function add_clauses(p::CMS, clauses)
    for item in clauses
        add_clause(p, item)
    end
end

"""`add_xor_clause(p::CMS, clause::Vector{Union{Lit,Int}}, rhs::Bool)::Bool`

Adds an XOR clause to `p`. This is a clause of the form `x_1 ⊻ x_2 ⊻ ... ⊻ x_n = rhs`."""
add_xor_clause(p::CMS, clause::Vector{UInt32}, rhs::Bool = true) = cms_add_xor_clause(p, clause, rhs)
function add_xor_clause(p::CMS, clause, rhs = true)
    cc = UInt32[]
    m = -1
    for c in clause
        if isa(c, Lit)
            x = var(c)
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
    cms_add_xor_clause(p, cc, rhs)
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
solve(p::CMS) = Cbool2Bool(cms_solve(p))
function solve(p::CMS, assumptions)
    c = convert(Array{Lit},assumptions)
    m = -1
    for l in c
        m = max(m,var(l))
    end
    if m ≥ nvars(p)
        new_vars(p, m+1-nvars(p))
    end
    Cbool2Bool(cms_solve_with_assumptions(p,c))
end

"""`get_model(p::CMS)::Vector{Bool}`

returns the variables in the current solution to `p`. This assumes that `solve(p)` was called and returned `true`."""
function get_model(p::CMS)
    map(Cbool2Bool,cms_get_model(p))
end

"""`get_conflict(p::CMS)::Vector{Lit}`

returns the conflicting variables in the current solution to `p`. This assumes that `solve(p)` was called and returned `false`"""
function get_conflict(p::CMS)
    cms_get_conflict(p)
end

################################################################
# top-level interface, creating / destructing CMS object in one go.
# the syntax is compatible with e.g. PicoSAT

function create_problem(clauses, vars, num_threads)
    numvars = -1
    for c=clauses, l=c
        numvars = max(numvars,abs(l))
    end
    if vars == -1
        vars = numvars
    end
    vars < numvars && error("There are more variables than specified")

    p = CMS(vars; num_threads = num_threads)
    add_clauses(p, clauses)
    p
end

"""
`solve(clauses; vars::Integer=-1, verbose::Integer=0, proplimit::Integer=0, num_threads::Int = Sys.CPU_THREADS)`
   - `vars` - the number of variables (will be inferred if not specified)
   - `verbose` - ignored
   - `proplimit` - ignored
   - `num_threads` - number of CPU threads to use
Returns a solution if the problem is satisfiable.
Satisfiable solutions are represented as a vector of signed integers.
If the problem is not satisfiable the method returns an `:unsatisfiable` symbol.
```julia
julia> import CryptoMiniSat
julia> cnf = Any[[1, -5, 4], [-1, 5, 3, 4], [-3, -4]];
julia> CryptoMiniSat.solve(cnf)
5-element Array{Int64,1}:
 -1
 -2
 -3
 -4
 -5
```
"""
function solve(clauses;
               vars::Integer=-1,
               verbose::Integer=0,
               proplimit::Integer=0,
               num_threads::Integer=Sys.CPU_THREADS)
    p = create_problem(clauses, vars, num_threads)
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
   - `verbose` - ignored
   - `proplimit` - ignored
   - `num_threads` - number of CPU threads to use

Returns an iterable object over all solutions.
When a user-defined propagation limit is specified, the iterator may not produce all feasible solutions.

```julia
julia> import CryptoMiniSat
julia> cnf = Any[[1, -5, 4], [-1, 5, 3, 4], [-3, -4]];
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
function itersolve(clauses;
                   vars::Integer=-1,
                   verbose::Integer=0,
                   proplimit::Integer=0,
                   num_threads::Integer=Sys.CPU_THREADS)
    p = create_problem(clauses, vars, num_threads)
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
end
