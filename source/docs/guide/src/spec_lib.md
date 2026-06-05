# Specification libraries: Seq, Set, ISet, Map, IMap

The Verus libraries contain types `Seq<T>`, `Set<T>`, `ISet<T>`,
`Map<Key, Value>`, and `IMap<Key, Value>`
for representing sequences, finite sets, potentially infinite sets,
finite maps, and potentially infinite maps in specifications.
In contrast to executable Rust collection datatypes in
[std::collections](https://doc.rust-lang.org/std/collections/),
the `Seq`, `Set`, `ISet`, `Map`, and `IMap` types
represent collections of arbitrary size.
For example, while the `len()` method of
[`std::collections::HashSet`](https://doc.rust-lang.org/std/collections/hash_set/struct.HashSet.html)
returns a length of type `usize`,
which is bounded,
the `len()` methods of `Seq`, `Set`, and `ISet` each return
a length of type `nat`, which is unbounded.

`Seq`, `Set`, and `Map` objects are always finite.
`ISet` and `IMap` represent possibly-infinite sets and maps.
This allows specifications to talk about collections that
are larger than could be contained in the physical memory of a computer.

The possibly-infinite versions have one key benefit: You can construct them
without proving they're finite. The finite versions have two key benefits.
First, they can be used in recursive types; e.g., an `enum T` can contain
fields of type `Set<T>` and `Map<T, U>` but not `ISet<T>` or `IMap<T, U>`.
Second, the verifier knows the finiteness property always holds, which can
prevent some SMT-time proof failure surprises. For instance, adding a new
element to a `Set` increases its `len()` by 1, but this doesn't always hold
for an `ISet` since it might have infinite size.

## Constructing and using Seq, Set, ISet, Map, and IMap

The `seq!`, `set!`, and `map!` macros construct values of type `Seq`, `Set`,
and `Map` with particular contents. The `iset!` and `imap!` macros construct
finite values of the possibly-infinite types `ISet` and `IMap`:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:macro}}
```

The macros above can only construct finite (literal) sequences, sets, and maps.
Sequences, potentially-infinite sets, and potentially-infinite maps can also
be constructed with `Seq::new`, `ISet::new`, and `IMap::new`.

A `Set` can only be constructed if it's provably finite. There are several
ways to do this, including the following:
* For numeric types `T` (e.g., `int`, `usize`, `i32`, `u64`, etc.),
  `Set::<T>::range(lo, hi)` produces a set of `i: T` such that `lo <= i <
  hi`. (See the `FiniteRange` trait.)
* For numeric types `T` other than `int` and `nat`,
  `Set::<T>::full().unwrap()` produces a set of all values of type `T`. (See
  the `FiniteFull` trait.)
* You can use one of the above techniques, then modify the `Set` as desired
  using `Set::filter` and/or `Set::map`. But be warned: `Set::filter` is fine,
  but `Set::map` can be problematic. This is because the meaning of `Set::map`
  is defined via the formula
  `self.map(f).contains(b) <==> exists|a: A| self.contains(a) && b == f(a)`.
  This use of `exists` generally makes proofs about the resulting set more
  difficult and less automated. Consider alternatives to `Set::map`, such as
  `Set::map_by` and `set_build!`, when possible.
* You can construct a `Set` using the `set_build!` macro defined
in the contributed library [set_build.rs](https://github.com/verus-lang/verus/tree/main/source/builtin_macros/src/contrib/set_build.rs).

To construct a `Map`, construct its domain as a `Set`, then pass that as
the first parameter to `Map::new`.

```rust
{{#include ../../../../examples/guide/lib_examples.rs:new}}
```

Each `Map<Key, Value>` value has a domain of type `Set<Key>` given by `.dom()`.
Likewise, each `IMap<Key, Value>` has a domain of type `ISet<Key>`.
In the `test_map2` example above, each of `m` and `m_finite` has the finite
domain `{0, 10, 20, 30, 40}`
while `m_infinite`'s domain is the infinite set `{..., -20, 10, 0, 10, 20, ...}`.

Some constructors of `Set<T>` don't necessarily produce a finite set; they
produce an `Option<Set<T>>` that's only `Some` when the set is finite. Thus,
they're only useful if you can prove finiteness (usually by recursion, using
the facts that `ISet::empty()` is finite and that `ISet::insert` preserves
finiteness). If you can't (or don't need to) prove that the set is finite,
just use an `ISet` instead. Examples of functions that produce an
`Option<Set<T>>` are:
* `Set::<T>::new(f)` constructs a set of all members of `T` satisfying
  predicate `f: spec_fn(T) -> bool`.
* `Set::<T>::full()` constructs a set of all members of `T`. If `T` has trait
  `FiniteFull`, an ambient broadcast lemma is sufficient to know it's `Some`.
* `Set::<T>::complement(self)` constructs a set of all members of `T` not in
  `self.`
* `Set::<T>::new_from_iset(s)` constructs a set of all members of `T` in the
  `ISet` s.

For more operations, including sequence contenation (`.add` or `+`),
sequence update,
sequence subrange,
set union (`.union` or `+`),
set intersection (`.intersect`),
etc.,
see:

- [seq.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/seq.rs)
- [seq_lib.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/seq_lib.rs)
- [set.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/set.rs)
- [set_lib.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/set_lib.rs)
- [iset.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/iset.rs)
- [iset_lib.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/iset_lib.rs)
- [map.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/map.rs)
- [map_lib.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/map_lib.rs)
- [imap.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/imap.rs)
- [imap_lib.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/imap_lib.rs)

See also the [API documentation](https://verus-lang.github.io/verus/verusdoc/vstd/index.html).

## Proving properties of Seq, Set, ISet, Map, and IMap

The SMT solver will prove some properties about Seq, Set, ISet, Map, and IMap automatically,
as shown in the examples above.
However, some other properties may require calling lemmas in the library
or may require proofs by induction.

If two collections (`Seq`, `Set`, `ISet`, `Map`, or `IMap`) have the same elements,
Verus considers them to be equal.
This is known as equality via [extensionality](https://en.wikipedia.org/wiki/Extensionality).
However, the SMT solver will in general not automatically recognize that
the two collections are equal
if the collections were constructed in different ways.
For example, the following 3 sequences are equal,
but calling `check_eq` fails:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:test_eq_fail}}
```

To convince the SMT solver that `s1`, `s2`, and `s3` are equal,
we have to explicitly assert the equality via the *extensional* equality operator `=~=`,
rather than just the ordinary equality operator `==`.
Using `=~=` forces the SMT solver
to check that all the elements of the collections are equal,
which it would not ordinarily do, so that the following succeeds:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:test_eq}}
```

We can use `assert(s1 =~= s2)`, for example, to prove that `s1` equals `s2`
before calling the original `check_eq`:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:test_eq2}}
```

(Note that by default, Verus will automatically promote `==` to `=~=`
inside `assert`, `ensures`, and `invariant`,
so that, for example, `assert(s1 == s2)` actually means `assert(s1 =~= s2)`.
See the [Equality via extensionality](extensional_equality.md) section for more details.)

An `ISet` and a `Set` can never be equal because their types disagree;
should you find yourself needing to relate them, consider the `Set::congruent`
predicate, or convert the `Set` to an `ISet` with `to_iset()` before
checking for equality. (In non-library code, it is best practice to use
exclusively the finite or infinite variant, if feasible.)

Proofs about set cardinality (`Set::len`) and set finiteness (`ISet::finite`)
often require inductive proofs.
For example, the exact cardinality of the intersection of two sets
depends on which elements the two sets have in common.
If the two sets are disjoint,
the intersection's cardinality will be 0,
but otherwise, the intersections's cardinality will be some non-zero value.
Let's try to prove that the intersection's cardinality is no larger than
either of the two sets' cardinalities.
Without loss of generality, we can just prove that
the intersection's cardinality is no larger than the first set's cardinality:
`s1.intersect(s2).len() <= s1.len()`.

The proof (which is found in [set_lib.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/set_lib.rs))
is by induction on the size of the set `s1`.
In the induction step, we need to make `s1` smaller,
which means we need to remove an element from it.
The two methods `.choose` and `.remove` allow us to choose
an arbitrary element from `s1` and remove it:

```rust
let a = s1.choose();
... s1.remove(a) ...
```

Based on this, we expect an inductive proof to look something like the following,
where the inductive step removes `s1.choose()`:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:lemma_len_intersect_fail}}
```

Unfortunately, Verus fails to verify this proof.
Therefore, we'll need to fill in the base case and induction case with some more detail.
Before adding this detail to the code,
let's think about what a fully explicit proof might look like if we wrote it out by hand:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:lemma_len_intersect_sketch}}
```

For such a simple property, this is a surprisingly long proof!
Fortunately, the SMT solver can automatically prove most of the steps written above.
What it will not automatically prove, though, is any step requiring equality via extensionality,
as discussed earlier.
The two crucial steps requiring equality via extensionality are:
- "Therefore, s1.intersect(s2) is also empty."
- Replacing `(s1 - {a}).intersect(s2)` with `s1.intersect(s2) - {a}`

For these, we need to explicitly invoke `=~=`:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:lemma_len_intersect}}
```

With this, Verus and the SMT solver successfully complete the proof.
However, Verus and the SMT solver aren't the only audience for this proof.
Anyone maintaining this code might want to know why we invoked `=~=`,
and we probably shouldn't force them to work out the entire hand-written proof above
to rediscover this.
So although it's not strictly necessary,
it's probably polite to wrap the assertions in `assert...by` to indicate
the purpose of the `=~=`:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:lemma_len_intersect_commented}}
```

---
