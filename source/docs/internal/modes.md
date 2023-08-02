# Three kinds of code ... specification, proof, and executable

As stated in the project [goals](https://github.com/verus-lang/verus/wiki/Goals),
we want to provide a language that expresses specifications, proofs, and executable code.
These three kinds of code differ in significant ways.
For example, executable code is compiled, while proofs and specifications are erased.
In addition, to enable efficient SMT solving,
we [aim](https://github.com/verus-lang/verus/wiki/Goals) to keep the specification language close to the SMT solving language,
whereas executable code and proofs are more similar to programming languages
than to SMT formulas.

We describe these three kinds of code with three different "modes", `spec`, `proof`, and `exec`.
This is a slight extension to the concept of "ghost" and "non-ghost" code
in other verification frameworks like Dafny, in which `exec` corresponds to "non-ghost"
and `spec` and `proof` are two different kinds of "ghost".

Here is an example:
```
#[verifier(opaque)]
#[spec]
fn f(n: int) -> int { n + 1 }

#[proof]
fn lemma_f(n: int) {
    ensures(f(n) > n);

    reveal(f);
}

#[exec]
fn main() {
    #[spec] let x = 7;
    lemma_f(x);
    assert(f(7) > 7);
}
```

or, with a hypothetical future nice syntax:

```
#[verifier(opaque)]
spec fn f(n: int) -> int { n + 1 }

proof fn lemma_f(n: int)
    ensures
        f(n) > n
{
    reveal(f);
}

exec fn main() {
    spec let x = 7;
    lemma_f(x);
    assert(f(7) > 7);
}
```

In this example, `f` is a `spec` function, `lemma_f` is a `proof` function,
`main` is an `exec` function, `n` is a `spec` parameter, `x` is a `spec` variable,
and `f(n) > n` is a `spec` expression.
By default, `exec` function parameters are `exec` and `proof`/`spec` function parameters are `spec`,
so the function declarations above are equivalent to:

```
...
#[spec]
fn f(#[spec] n: int) -> int { n + 1 }

#[proof]
fn lemma_f(#[spec] n: int) {
...
```

There are no `proof` variables or parameters in this example --
we expect `proof` variables to be useful for some special kinds of proof,
but `spec` variables will be more common in standard Hoare-logic style proofs.

## `spec` and `proof` are different

As in Dafny, non-ghost (`exec`) code is compiled,
while ghost (`spec` and `proof`) code is erased before compilation.
However, `spec` and `proof` are treated differently in several ways.
First, `proof` is checked by the Rust lifetime checker,
while `spec` code is not:

```
spec  ---> type checker ---> SMT verifier
proof ---> type checker ---> SMT verifier ---> lifetime checker
exec  ---> type checker ---> SMT verifier ---> lifetime checker ---> compiler
```

Checking proofs for lifetimes enables styles of proof based on linearity,
where a linear `proof` value can represent evidence of the availability of some resource,
as in linear logic and separation logic.
By contrast, `spec` values are free from lifetime constraints:
programs can freely duplicate values within a specification.
More generally, even non-linear `proof` values may be considered evidence that something
has been proven (analogous to how values are used as proofs in constructive logics like Coq),
whereas `spec` values are not by themselves evidence of anything.

Second, proofs may have preconditions and postconditions (requires/ensures),
while specifications do not.
In fact, preconditions and postconditions are the whole point of proofs --
a proof's requires and ensures clause describe what a proof is proving --
but requires and ensures clauses are specifications, not proofs,
and do not carry their own additional requirements or provide
their own additional proofs.
This hard separation between proof and specification is similar to Boogie and Z3,
but differs from Dafny, F*, and Coq, where specifications are themselves verified.
For example, in Dafny, it is an error for a specification like `requires x / y <= 100` to divide by zero,
so that the program has to prove that `y != 0` to even state this specification.
By contrast, Boogie and Z3 treat division by zero in a specification as uninterpreted
rather than errant, and an assertion like `assert(1 / 0 == 1 / 0)` is perfectly valid.

Third, specifications treat all types as inhabited, while proofs (and executable code) do not.
Specifically, for uninhabited types like Rust's `never` type
(written `!` in nightly experimental Rust),
specifications allow for an additional special value called "bottom".
For example, the bottom value can be used to represent results returned by partial functions
that are applied to arguments outside the partial function's domain.
Executable code might create an empty vector `v` of type `vec<!>`.
Subscripting v, as in `v[5]`, would be an error in executable code.
However, specifications can freely refer to `v[5]`,
and the specification expression `v[5]` simply equals bottom.

On the other hand, `spec` and `proof` are similar in one important respect:
both proof functions (lemmas) and specification functions are checked for termination
when they use recursion.
To ensure termination, both `spec` and `proof` functions specify `decreases` clauses
that are checked by the SMT solver.
Proof functions must be checked for termination to avoid circular reasoning --
a proof can't prove itself by simply calling itself recursively infinitely many times.
Specification functions are checked for termination to make sure that they
define meaningful values (a non-terminating function like
`fn f(i: nat) -> nat {f(i) + 1}`
does not actually define a value f(7) such that f(7) = f(7) + 1,
as this is impossible to satisfy.)

## Some language design pitfalls to avoid

The distinction between `spec` and `proof` means that some care must
be taken along the boundary between the two.
In particular, since `spec` includes the bottom value and `proof` does not,
we have to make sure that bottom cannot accidentally flow from `spec` to `proof`
or otherwise malevolently influence proofs.
As described in the section below on mode checking,
it is illegal to directly assign a `spec` value to a `proof` or `exec` variable,
so bottom cannot directly flow into proof variables.
However, there are some more subtle issues.

First, `proof` expressions can pattern match on `spec` values using Rust's `match` expression.
When matching on an enumeration,
this is only sound if the enumeration is non-empty (contains at least one variant).
An empty enumeration is an uninhabited type,
which may be bottom in a specification value.
Allowing a proof match on bottom could generate a proof value of an uninhabited type.
Therefore, for soundness, the mode checking rules described below contain a side condition
that prohibits out this case.

Second, the SMT encoding of non-empty enumerations can assume that each
enumeration value belongs to one of the enumeration's variants.
The SMT encoding cannot make this assumption for empty enumerations,
though, since an empty enumeration contains no variants and may
be represented by bottom in specifications.

Third, refinement types (types whose values satisfy some user-defined predicate)
must be inhabited -- there must be a value of the type for which the predicate holds.
Otherwise, the predicate could simply be `false`,
and the SMT encoding of the predicate would assume `false` whenever a value
of the refinement type appears (in particular, when the bottom value appears in a specification).
Currently, the only refinement types are the built-in numeric types like `u8`, `u16`, etc.,
and these are all inhabited, since there exist integers in the range 0..255, 0..65535, etc.
(As an alternative, instead of requiring refinement types to be inhabited,
we could simply not make SMT assumptions about refinement types for `spec` values.
However, the lack of such assumptions might surprise programmers.
If a `spec` variable `x` has type `u8`, programmers might reasonably expect
that `assert(x < 256)` is automatically valid
without requiring any manual proof work by the programmer.)

Fourth, the Rust compiler can optimize code under the assumption that
no variables can possibly contain a value of the never (`!`) type.
Because `spec` variables can contain values of the never type,
we *must* erase `spec` code before running Rust's compiler.
(It's supposed to be erased anyway; we just have to make sure we really do it.) 

Lastly, consider a value `v` that is a first-class function or a value implementing a trait.
If the function type can have postconditions or the trait members can have postconditions,
then those postconditions are only valid if `v` is an `exec` or `proof` value,
not if `v` is a `spec` value.
In other words, the SMT encoding can assume that postconditions are true
for calls to first-functions and trait members,
but only when calling non-`spec` function and trait values.
This reflects the fact that some function types and trait types might be uninhabited,
a `spec` value of these types might be the bottom value rather than a real function or trait value.
See, for example, [Dafny issue 851](https://github.com/dafny-lang/dafny/issues/851),
where ghost Dafny code could create a ghost value of an uninhabited trait type and
then deduce false from a trait member's postcondition.
Note, though, that unlike Dafny's "ghost" expressions,
`spec` expressions by design ignore preconditions and postconditions
(SMT assertions and assumptions about requires/ensures are only introduced in `exec` and `proof` code).
In other words, making the distinction between `spec` and `proof` allows us to avoid the issue
that arose with Dafny's "ghost".
Nevertheless, it's worth remembering this issue as the language evolves
or we consider alternative designs.

## Mode checking

Each function, local variable, function parameter, function return value, and struct/enum field has a mode.
By default:
- functions are `exec`
- struct/enum fields are `exec`
- for `exec` functions:  variables, parameters, and return values are `exec`
- for `proof` and `spec` functions:  variables, parameters, and return values are `spec`

To override the defaults, programmers can annotate functions, variables, parameters,
return values, and fields with the #[exec], #[proof], or #[spec] attributes.

The formal rules below check the modes of expressions for a simplified model of the language.
The rules include named structs `S`, named enumerations `U`, and named functions `F`.
Both struct and enumeration fields are annotated with modes `m`.
The subsumption rule allows coercions from `exec` to `proof`/`spec` and from `proof` to `spec`,
but not the other way around
(`spec` values cannot flow into `proof`/`exec` variables,
and `proof` values cannot flow into `exec` variables).

Expressions are checked in an environment `m ; G`.
In this environment, `G` describes the modes and types of parameters and local variables.
`m` describes the mode of the code in which the expression lives.
For example, in a precondition or postcondition, `m` will be `spec` -- this ensures
that specifications cannot contain proofs or executable code.
In the body of a function, `m` will be equal to the mode of the function
(e.g. a `spec` function has a `spec` body and an `exec` function has an `exec` body).
This ensures, for example, that proofs (lemmas) cannot contain executable code.

```
Modes, mode ordering, least upper bounds
  m = exec | proof | spec
  exec <= proof <= spec
  LUB(m, m) = m
  LUB(m, spec) = LUB(spec, m) = spec
  LUB(m, exec) = LUB(exec, m) = m

Types, patterns, and expressions
  t = int | S | U
  p = x1 … xj
  e = x | n | e1 + e2 | let x: m t = e1 in e2
    | F(e1, …, ej)
    | S(e1, …, ej) | e.i
    | U.i(e1, …, ej)| match e {p1 => e1, …, pk => ek}

Function types
  f = mf (m1 t1, …, mj tj) -> m0 t0
    where mf <= m0 and … and mf <= mj

Assume a mapping from function names F to modes and types
  F1 -> f1, …, Fn -> fn

Struct/enumeration types:
  s = (m1 t1, …, mj tj)
  u = (s1, …, sk)

Assume a mapping from struct/enumeration names S/U to definitions s/u:
  S1 -> s1, …, Sm -> sm
  U1 -> u1, …, Un -> un

Typing environment m ; G
where G = x1: m1 t1, ..., xn: mn tn

Typing rules m ; G |- e : m' t

m ; G |- e : m1 t
m1 <= m2
----------------- ("subsumption rule")
m ; G |- e : m2 t

m ; G, x : mx tx |- x : LUB(m, mx) tx

m ; G |- n : m int

m ; G |- e1 : m1 int
m ; G |- e2 : m2 int
----------------------------------
m ; G |- e1 + e2 : LUB(m1, m2) int

m <= mx
m ; G |- ex : mx tx
m ; G, x : mx tx |- eb : mb tb
----------------------------------------
m ; G |- let x: mx tx = ex in eb : mb tb

F -> f
f = mf (m1 t1, …, mj tj) -> m0 t0
m <= mf
m ; G |- e1 : m1 t1
…
m ; G |- ej : mj tj
---------------------------------
m ; G |- F(e1, …, ej) : m0 t0

S -> (m1 t1, …, mj tj)
m ; G |- e1 : m1 t1
…
m ; G |- ej : mj tj
------------------------------
m ; G |- S(e1, …, en) : m S

m ; G |- e : me S
S -> (m1 t1, …, mj tj)
-----------------------------
m ; G |- e.i : LUB(me, mi) ti

U -> (s1, …, sk)
si = (m1 t1, …, mj tj)
m ; G |- e1 : m1 t1
…
m ; G |- ej : mj tj
-----------------------------
m ; G |- U.i(e1, …, ej) : m U

m ; G |- e : me U
U -> (s1, …, sk)
me = spec ==> k > 0
for each 1 <= i <= k:
  si = (m1 t1, …, mj tj)
  pi = x1, …, xj
  m' = (if m = exec and me != exec then proof else m)
  G' = G, x1: LUB(me, m1) t1, …, xj: LUB(me, mj) tj
  m' ; G' |- ei : mb t
-----------------------------------------------------
m ; G |- match e {p1 => e1, …, pk => ek} : mb t
```

The pattern match rule (`match e {…}`) contains some subtleties.
First, the  `me = spec ==> k > 0` condition disallows matching on an empty `spec` enumeration. 
This guards against the pitfall of matching with `e` equal to the "bottom" value
(see the previous section on pitfalls).

Second, the definition of `m'` allows the case `ei` to be executable
only if the matched expression `e` is executable.
Otherwise, the match would not be compilable -- you wouldn't be able to decide at run-time
which `ei` to execute if `e` were erased (as would happen if `e` were `proof` or `spec`).
Based on this requirement, you might expect the rule to say `m' = LUB(m, me)` or even just `m' = me`.
However, this would be stricter than necessary.
We can allow `m' = proof` even if `me = spec`.
This allows proofs to inspect `spec` values, which is both useful and safe.
For example, a proof by induction on a `spec` variable `n` might inspect `n` to see whether it is zero or non-zero,
and the proof can recursively call itself in non-zero case.

Note that we perform lifetime checking on `proof` code but not on `spec` code.
In other words, `spec` code is erased before we run Rust's lifetime checker on the `proof` code.
If the `proof` code matches on an expression `e` with mode `spec`,
then we will erase the `e` in the match before running the lifetime checker,
which would naively result in ill-formed Rust code.
To prevent this ill-formed code, such a match is instead erased into an if-else-if…-else expression,
where the condition of each `if` is a non-deterministic bool.

## Erasure

After mode checking, type checking, and SMT verification, we erase `spec` code.
After lifetime checking, we also erase `proof` code.
This way, only `exec` expressions remain for the Rust compiler to compile.
Note that expressions can contain mixtures of `spec`, `proof`, and `exec` code.
For example, if `e` is an argument to a function that expects a `spec` parameter,
`e` might contain some `exec` code that must be compiled for its side effects,
even though the ultimate result of evaluating `e` is an erased `spec` value.
(Note that the mode checker already prohibits `exec` subexpressions from
appearing inside `spec`/`proof` function bodies and `requires/ensures/invariant`,
so these can be always be entirely erased before compilation.
We might consider making the mode checker even more strict,
so that, for example, a `spec` argument could not contain `exec` code inside it.)

Let `ERASE(m_keep, m_expect, e)` be the result of performing erasure on `e`.
More specifically:
- `ERASE(exec, m_expect, e)` is the result of erasing all `spec` and `proof` code from `e`, keeping only the `exec` code
- `ERASE(proof, m_expect, e)` is the result of erasing all `spec` code from `e`, keeping only the `exec` and `proof` code
- `ERASE(spec, m_expect, e)` erases nothing, and just returns `e`

`m_expect` specifies what mode of value we expect `e` to produce.  If `m_expect = exec`, we expect `e` to produce an `exec` value, so we can't erase the generated value.  If `m_expect = proof` or `m_expect = spec`, we may be able to erase the generated value.  For example, `ERASE(_, exec, 99) = 99`, but `ERASE(exec, spec, 99) = ()`.  In the latter case, we erase the value `99` because the value will be used as a `spec` value, and `spec` values are being erased.  This can happen, for example, in the expression `F(99)` if `F` expects an argument of mode `spec`.

Note: `ERASE` may produce expressions like `(); ()` or matches with all cases returning `()`.  These can easily be further simplified.

```
Types, patterns, and expressions
  t = ... | ()
  e = ... | () | e; e | if * then e else e


Erasure in types

If m <= m_keep
  ERASE(m_keep, m t) = m t
Otherwise
  ERASE(m_keep, m t) = ()

Let f = mf (m1 t1, …, mj tj) -> m0 t0
Let f' = mf (ERASE(m_keep, m1 t1), ..., ERASE(m_keep, mj tj)) -> ERASE(m_keep, m0 t0)
If mf <= m_keep
  ERASE(m_keep, F -> f) = F -> f'
Otherwise
  ERASE(m_keep, F -> f) = {}

Let s = (m1 t1, …, mj tj)
Let s' = (ERASE(m_keep, m1 t1), ..., ERASE(m_keep, mj tj))
ERASE(m_keep, s) = s'

Let u = (s1, …, sk)
Let u' = (ERASE(m_keep, s1), …, ERASE(m_keep, sk))
ERASE(m_keep, u) = u'


Erasure in expressions

ERASE(m_keep, m_expect, ()) = ()

If m_expect <= m_keep
  ERASE(m_keep, m_expect, n) = n
Otherwise
  ERASE(m_keep, m_expect, n) = ()

Let e1' = ERASE(m_keep, m_expect, e1)
Let e2' = ERASE(m_keep, m_expect, e2)
If m_expect <= m_keep
  ERASE(m_keep, m_expect, e1 + e2) = e1' + e2'
Otherwise
  ERASE(m_keep, m_expect, e1 + e2) = e1'; e2'

(note: the value of e1 is discarded, so we have minimal expectations of it, so we set m_expect = spec for e1)
Let e1' = ERASE(m_keep, spec, e1)
Let e2' = ERASE(m_keep, m_expect, e2)
ERASE(m_keep, m_expect, e1; e2) = e1'; e2'

Let x: mx tx
If mx <= m_keep and m_expect <= m_keep
  ERASE(m_keep, m_expect, x) = x
Otherwise
  ERASE(m_keep, m_expect, x) = ()

Let ex' = ERASE(m_keep, mx, ex)
Let eb' = ERASE(m_keep, m_expect, eb)
If mx <= m_keep then
  ERASE(m_keep, m_expect, let x: mx tx = ex in eb) = let x: mx tx = ex' in eb'
Otherwise
  ERASE(m_keep, m_expect, let x: mx tx = ex in eb) = ex'; eb'

Let F -> f
Let f = mf (m1 t1, …, mj tj) -> m0 t0
Let e1' = ERASE(m_keep, m1, e1), …, ej' = ERASE(m_keep, mj, ej)
If mf <= m_keep
  If m_expect <= m_keep
    ERASE(m_keep, m_expect, F(e1, …, ej)) = F(e1', …, ej')
  Otherwise
    ERASE(m_keep, m_expect, F(e1, …, ej)) = F(e1', …, ej'); ()
Otherwise
  ERASE(m_keep, m_expect, F(e1, …, ej)) = e1'; …; ej'; ()

Let S -> (m1 t1, …, mj tj)
Let e1' = ERASE(m_keep, LUB(m_expect, m1), e1), …, ej' = ERASE(m_keep, LUB(m_expect, mj), ej)
If m_expect <= m_keep
  ERASE(m_keep, m_expect, S(e1, …, ej)) = S(e1', …, ej')
Otherwise
  ERASE(m_keep, m_expect, S(e1, …, ej)) = e1'; …; ej'; ()

Let S -> (m1 t1, …, mj tj)
Let e' = ERASE(m_keep, m_expect, e)
If mf <= m_keep and m_expect <= m_keep
  ERASE(m_keep, m_expect, e.i) = e'.i
Otherwise
  ERASE(m_keep, m_expect, e.i) = e'; ()

Let U -> (s1, …, sk)
Let si = (m1 t1, …, tj tj)
Let e1' = ERASE(m_keep, LUB(m_expect, m1), e1), …, ej' = ERASE(m_keep, LUB(m_expect, mj), ej)
If m_expect <= m_keep
  ERASE(m_keep, m_expect, U.i(e1, …, ej)) = U.i(e1', …, ej')
Otherwise
  ERASE(m_keep, m_expect, U.i(e1, …, ej)) = e1'; …; ej'; ()

Let e : me U
Let e' = ERASE(m_keep, me, e')
Let e1' = ERASE(m_keep, m_expect, e1), …, ek' = ERASE(m_keep, m_expect, ek)
If me = exec
  ERASE(m_keep, m_expect, match e {p1 => e1, …, pk => ek}) = match e' {p1 => e1', …, pk => ek'}
Otherwise
  If m_expect = exec
    This case should not happen; the mode checker should have already disallowed it
  Otherwise
    If m_keep = exec (note: exec code in cases is disallowed when me in {proof, spec}, so there's no exec code to keep in the cases)
      ERASE(m_keep, m_expect, match e {p1 => e1, …, pk => ek}) = e'
    If me = spec and m_keep = proof
      ERASE(m_keep, m_expect, match e {p1 => e1, …, pk => ek}) = e'; if * then e1' else if * then … else ek'
    Otherwise
      ERASE(m_keep, m_expect, match e {p1 => e1, …, pk => ek}) = match e' {p1 => e1', …, pk => ek'}
```

## Possible future extension: multi-mode functions

The rules above prohibit a specification from calling an `exec` function.
However, some `exec` functions could also work as `spec` functions.
The `len` function of Rust's `vec` type, for example, is deterministic and free of side effects,
so it would be safe to use within a `spec`.
We could extend the mode system to allow this.

Note, however, that we don't necessarily have to allow `spec` code to call `len`.
For example, we could define a separate function for getting the length as a `spec` value.
(We might also consider having `vec` auto-derive such separate `spec` functions.)
Or we could define a function that converts the entire `vec` value
into a more abstract sequence type (an abstract, mathematical "view" of the vector),
and this sequence type would then have a `spec` length function or method.
We could even consider some implicit coercions from the `vec` into the abstract view type
in some circumstances, such as when passing the `vec` as an argument to a function that
expects an abstract sequence, or when attempting to call an `exec` method like `len`
from within a specification.

If, however, we do want to allow `spec` code to call the original `exec` length function/method,
we could allow `len` to be annotated as both `spec` and `exec`.
This would be similar to a "function method" in Dafny,
which can be both compiled and used as a specification.
