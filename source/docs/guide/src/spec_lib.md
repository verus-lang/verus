# Specification libraries: Seq, Set, Map

The Verus libraries contain types `Seq<T>`, `Set<T>`, and `Map<Key, Value>`
for representing sequences, sets, and maps in specifications.
In contrast to executable Rust collection datatypes in
[std::collections](https://doc.rust-lang.org/std/collections/),
the `Seq`, `Set` and `Map` types
represent collections of arbitrary size.
For example, while the `len()` method of
[`std::collections::HashSet`](https://doc.rust-lang.org/std/collections/hash_set/struct.HashSet.html)
returns a length of type `usize`,
which is bounded,
the `len()` methods of `Seq` and `Set` return
lengths of type `nat`, which is unbounded.
Furthermore, `Set` and `Map` can represent infinite sets and maps.
(Sequences, on the other hand, are always finite.)
This allows specifications to talk about collections that
are larger than could be contained in the physical memory of a computer.

## Constructing and using Seq, Set, Map

The `seq!`, `set!`, and `map!` macros construct values of type `Seq`, `Set`, and `Map`
with particular contents:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:macro}}
```

The macros above can only construct finite sequences, sets, and maps.
There are also functions `Seq::new`, `Set::new`, and `Map::new`,
which can allocate both finite values and (for sets and maps) infinite values:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:new}}
```

Each `Map<Key, Value>` value has a domain of type `Set<Key>` given by `.dom()`.
In the `test_map2` example above, `m`'s domain is the finite set `{0, 10, 20, 30, 40}`,
while `m_infinite`'s domain is the infinite set `{..., -20, 10, 0, 10, 20, ...}`.

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
- [map.rs](https://github.com/verus-lang/verus/tree/main/source/vstd/map.rs)

See also the [API documentation](https://verus-lang.github.io/verus/verusdoc/vstd/index.html).

## Proving properties of Seq, Set, Map

The SMT solver will prove some properties about Seq, Set, and Map automatically,
as shown in the examples above.
However, some other properties may require calling lemmas in the library
or may require proofs by induction.

If two collections (`Seq`, `Set`, or `Map`) have the same elements,
Verus considers them to be equal.
This is known as equality via [extensionality](https://en.wikipedia.org/wiki/Extensionality).
However, the SMT solver will in general not automatically recognize that
the two collections are equal
if the collections were constructed in different ways.
For example, the following 3 sequences are equal,
but asserting equality fails:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:test_eq_fail}}
```

To convince the SMT solver that `s1`, `s2`, and `s3` are equal,
we have to explicitly assert the equality via the *extensional* equality operator `=~=`,
rather than just the ordinary equality operator `==`.
Using `=~=` forces the SMT solver
to check that all the elements of the collections are equal,
which it would not ordinarily do.
Once we've explicitly proven equality via extensionality,
we can then successfully assert `==`:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:test_eq}}
```

(See the [Equality via extensionality](extensional_equality.md) section for more details.)

Proofs about set cardinality (`Set::len`) and set finiteness (`Set::finite`)
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
{{#include ../../../rust_verify/example/guide/lib_examples.rs:lemma_len_intersect_fail}}
```

Unfortunately, Verus fails to verify this proof.
Therefore, we'll need to fill in the base case and induction case with some more detail.
Before adding this detail to the code,
let's think about what a fully explicit proof might look like if we wrote it out by hand:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:lemma_len_intersect_sketch}}
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
{{#include ../../../rust_verify/example/guide/lib_examples.rs:lemma_len_intersect}}
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
{{#include ../../../rust_verify/example/guide/lib_examples.rs:lemma_len_intersect_commented}}
```

---
