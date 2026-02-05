/*!
The Verus prophecy library contains two different forms of prophecy variables, each with
different tradeoffs:

 * [`Prophecy`], loosely based on the prophecy variables from [_The Future is Ours: Prophecy Variables in Separation Logic_](https://plv.mpi-sws.org/prophecies/paper.pdf)
 * [`ProphecyGhost`], loosely based on the parametric prophecies developed in [_RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code_](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf), and later used in [_VerusBelt: A Semantic Foundation for Verus’s Proof-Oriented Extensions to the Rust Type System_](https://iris-project.org/pdfs/2026-pldi-verusbelt.pdf).

# Tradeoffs

The two types provide a similar interface, but make different tradeoffs along certain dimensions:

1. [`ProphecyGhost`] can resolve to any ghost-computed value, but [`Prophecy`] is required to resolve to an exec-computed value.
2. [`ProphecyGhost`] allows prophecies to resolve to values dependent on other prophecies, whereas [`Prophecy`] does not allow this.
3. The [`ProphecyGhost::value`] function, which gives the prophesied value, is marked
   [`verifier::prophetic`](https://verus-lang.github.io/verus/guide/reference-attributes.html#verifierrprophetic), which means it is subject to Verus's prophecy-dependence tracking, which entails certain restrictions on how it is used. However, [`Prophecy::view`] is (counterintuitively) NOT marked prophetic, and so it is not subject to the restrictions that Verus usually enforces on prophesied values. (This is presently the only way to get a prophecy value without being subject to prophecy-dependence restrictions.)

|                   | Ghost resolution | Dependent resolution | Prophecy-dependence tracking |
|-------------------|------------------|----------------------|------------------------------|
| [`Prophecy`]      | ✘ Exec only      | ✘ Not allowed        | ✔ No enforcement             |
| [`ProphecyGhost`] | ✔ Allowed        | ✔ Allowed            | ✘ Enforced                   |

Why is prophecy-dependence tracking necessary, and how does `Prophecy` avoid the need for it?
The reason for these tradeoffs have to do with two specific soundness issues which must be avoided.

## Soundness issue 1: Cyclically dependent prophecy variables

We need to make sure a prophecy value cannot resolve to a value dependent on itself, as such a cyclic dependency can easily create an inconsistency.

```rust
use vstd::proph::ProphecyGhost;

proof fn test() {
    let tracked p = ProphecyGhost::<bool>::new();
    p.resolve(!p.value());
    assert(false); // contradiction!
}
```

`ProphecyGhost` avoids this because `p.value()` is considered a prophetic value which is subject to Verus's dependency tracking.

```
error: prophetic value not allowed for argument to proof-mode function with tracked parameters
 --> cyclic.rs:9:15
  |
9 |     p.resolve(!p.value());
  |               ^---------
  |               ||
  |               |the result of this call is prophetic
  |               this argument is expected to be non-prophetic
  |
```

On the other hand, `Prophecy` does not have this problem because its `resolve` function requires its resolved value to be computed in exec code.
By definition, then, the resolution cannot be dependent on prophesied values, which are always ghost.
We can argue for soundness similarly to the [_Future is Ours_ paper]((https://plv.mpi-sws.org/prophecies/paper.pdf)):
for any program trace, we can determine the full sequence of resolved prophecy variables before instantiating
the proof accompanying the program.

## Soundness issue 2: Unbounded prophecies and termination checking

When working with prophecy variables that depend on other prophecy variables, it possible to end up with data
which is not bounded across all possible program traces. Such prophetic information cannot be used for any kind
of termination reasoning.

For example, consider the [`ProphecySeq`] library, which is implemented via prophecy dependent variables from [`ProphecyGhost`].
For a prophetic sequence `s`, we can resolve the first element to `x` and get another prophetic sequence `s'` such that `s == [x] + s'`.
We can do this indefinitely; thus, there may be an infinite program trace, for which any possible value of `s` is contradictory.
This is fine for safety reasoning, where we only need to consider finite program traces, but not for liveness reasoning.

For example, using `ProphecySeq`, we can easily write an infinite loop with a `decreases`-measure that apparently decreases forever:

```
use vstd::proph::ProphecySeq;

fn test() {
    let tracked s = ProphecySeq::<int>::new();
    loop
        decreases s.seq().len()
    {
        // let ghost old_s = s.seq();
        proof { s.resolve_cons(0); }
        // assert(old_s == [0] + s.seq());
    }
}
```

Again, `ProphecyGhost` (and thus `ProphecySeq`) avoid this soundness issue through prophecy-dependence tracking,
which detects that the `decreases` clause is illegal because it depends on a prophetic value:

```
error: prophetic value not allowed for 'decreases' clause
  --> infinite_loop.rs:10:19
   |
10 |         decreases s.seq().len()
   |                   -------^^^^^^
   |                   |
   |                   the result of this call is prophetic
   |                   this decreases-measure is expected to be non-prophetic
```

`Prophecy`, on the other hand, simply does not support prophecy-dependent resolutions, so it does not have this problem.
This is why there is no equivalent of `ProphecySeq` for the `Prophecy`-style of prophecy variable.
(Note that while the _Future is Ours_ paper does support prophetic sequences, they only consider partial correctness,
not termination reasoning, and so they don't have this problem.)

# Relationship to mutable borrows

Verus uses a prophecy-based encoding for mutable borrows, where the "final value" of a mutable
reference `x: &mut T`, denoted `*final(x)` is a prophesied value. Prophecy variables with
mutable borrows behave most similarly to [`ProphecyGhost`]:

1. Mutable borrows allow ghost-dependent resolution, thus supporting `&mut Ghost<T>` and `&mut Tracked<T>`.

2. Mutable borrows allow prophecy-dependent resolution, as demonstrated by reborrowing:

```rust
fn get_mut_fst<A, B>(pair: &mut (A, B)) -> (fst: &mut A)
    ensures
        *fst == old(pair).0,
        *final(pair) == (*final(fst), old(pair).1),
{
    &mut pair.0
}
```

The prophetic value `*final(pair)` is resolved to a value dependent on prophetic value `*final(fst)`.

3. The value `*final(x)` is subject to prophecy-dependence tracking:

```
fn test(x: &mut u64) {
    let xfinal = Ghost(*final(x));
}
```

```
error: prophetic value not allowed for 'Ghost' wrapper
 --> mut_ref_test.rs:6:24
  |
6 |     let xfinal = Ghost(*final(x));
  |                        ^^^^^^^^^
  |                        |
  |                        the `final` builtin is prophetic
  |                        operand of this wrapper is expected to be non-prophetic
```
*/
#![allow(unused_variables)]

use super::modes::*;
use super::prelude::*;

verus! {

/** A general-purpose prophecy variable.

A prophecy variable is allocated via [`Prophecy::new`](Self::new)
and resolved to a definitive value via [`Prophecy::resolve`](Self::resolve).

In contrast to the similar [`ProphecyGhost`], this does not require us to mark the
[`value()`](Self::view) as [`verifier::prophetic`](https://verus-lang.github.io/verus/guide/reference-attributes.html#verifierprophetic), which can make it easier to use.
However, it does not allow dependent resolutions, and it can only resolve to values
which are computed purely in exec-mode (as enforced by the `T: Structural` bound).
See [the module level documentation](self) for a detailed comparison with the rationale
for these trade-offs.
*/
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct Prophecy<T> {
    v: Ghost<T>,
}

impl<T> Prophecy<T> where T: Structural {
    /// The prophecized value.
    pub uninterp spec fn view(self) -> T;

    /// Allocate a new prophecy variable.
    #[inline(always)]
    #[verifier::external_body]
    pub exec fn new() -> (proph_var: Self) {
        Prophecy::<T> { v: Ghost::assume_new() }
    }

    /// Resolve the prophecy variable to a concrete value.
    /// This consumes `self`, so it can only be called once.
    #[inline(always)]
    #[verifier::external_body]
    pub exec fn resolve(self, v: &T)
        ensures
            self@ == v,
    {
    }
}

/** A general-purpose prophecy variable.

A prophecy variable is allocated via [`ProphecyGhost::new`](Self::new)
and resolved to a definitive value via [`ProphecyGhost::resolve`](Self::resolve).

In contrast to the similar [`Prophecy`], this allows resolving on ghost computations
and permits dependent resolutions. However, the [`value()`](Self::value)
is marked [`verifier::prophetic`](https://verus-lang.github.io/verus/guide/reference-attributes.html#verifierrprophetic), which entails certain restrictions in the way it can be used.
See [the module level documentation](self) for a detailed comparison with the rationale
for these trade-offs.

See [`ProphecySeq`] for an example of a library verified using dependent resolutions.
*/

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub tracked struct ProphecyGhost<T> {
    _t: Ghost<T>,
}

impl<T> ProphecyGhost<T> {
    #[verifier::prophetic]
    pub uninterp spec fn value(&self) -> T;

    pub axiom fn new() -> (tracked proph_var: Self);

    pub axiom fn resolve(tracked self, value: T)
        ensures
            self.value() == value,
    ;

    pub proof fn resolve_dependent<U>(
        tracked self,
        tracked u: &ProphecyGhost<U>,
        f: spec_fn(U) -> T,
    )
        ensures
            self.value() == f(u.value()),
    {
        self.resolve_dependent_2(u, &ProphecyGhost::new(), |u: U, v: ()| f(u));
    }

    pub axiom fn resolve_dependent_2<U, V>(
        tracked self,
        tracked u: &ProphecyGhost<U>,
        tracked v: &ProphecyGhost<V>,
        f: spec_fn(U, V) -> T,
    )
        ensures
            self.value() == f(u.value(), v.value()),
    ;

    pub proof fn resolve_dependent_3<U, V, W>(
        tracked self,
        tracked u: &ProphecyGhost<U>,
        tracked v: &ProphecyGhost<V>,
        tracked w: &ProphecyGhost<W>,
        f: spec_fn(U, V, W) -> T,
    )
        ensures
            self.value() == f(u.value(), v.value(), w.value()),
    {
        let tracked vw = ProphecyGhost::<(V, W)>::new();
        self.resolve_dependent_2(u, &vw, |u: U, vw: (V, W)| f(u, vw.0, vw.1));
        vw.resolve_dependent_2(v, w, |v: V, w: W| (v, w));
    }
}

/// A prophetic sequence, which permits prophesying one element at a time.
pub tracked struct ProphecySeq<T> {
    tracked var: ProphecyGhost<Seq<T>>,
}

impl<T> ProphecySeq<T> {
    #[verifier::prophetic]
    pub closed spec fn seq(&self) -> Seq<T> {
        self.var.value()
    }

    pub proof fn new() -> (tracked proph_var: Self) {
        ProphecySeq { var: ProphecyGhost::new() }
    }

    pub proof fn resolve_cons(tracked &mut self, v: T)
        ensures
            old(self).seq() == seq![v] + final(self).seq(),
    {
        let tracked mut var = ProphecyGhost::new();
        tracked_swap(&mut var, &mut self.var);
        var.resolve_dependent(&self.var, |w| seq![v] + w);
    }

    pub proof fn resolve_nil(tracked self)
        ensures
            self.seq() === seq![],
    {
        let tracked ProphecySeq { var } = self;
        var.resolve(seq![]);
    }
}

} // verus!
