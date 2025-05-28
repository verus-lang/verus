# Encapsulating well-formedness with type invariants

Recall our specifications from the previous chapter:

```rust
impl<V> TreeMap<V> {
{{#include ../../../../examples/guide/bst_map.rs:new_signature}}

{{#include ../../../../examples/guide/bst_map.rs:insert_signature}}

{{#include ../../../../examples/guide/bst_map.rs:delete_signature}}

{{#include ../../../../examples/guide/bst_map.rs:get_signature}}
}
```

Observe the presenence of this `tree_map.well_formed()`  predicate, especially in the
`requires` clauses.
As a result of this,
the client needs to work with this `tree_map.well_formed()` predicate all throughout
their own code. For example:

```rust
{{#include ../../../../examples/guide/bst_map.rs:test_callee}}
```

Without the `requires` clause, the above snippet would fail to verify.

Intuitively, however, one might wonder why we have to carry this predicate around at all.
After all,
due to encapsulation, it isn't ever possible for the client to create a `tree_map` where
`well_formed()` _doesn't_ hold.

In this section, we'll show how to use Verus's [type invariants](./reference-type-invariants.md)
feature to remedy this burden from the client.

### Applying the `type_invariant` attribute.

In order to tell Verus that we want the `well_formed()` predicate to be inferred
automatically, we can mark it with the `#[verifier::type_invariant]` attribute:

```rust
{{#include ../../../../examples/guide/bst_map_type_invariant.rs:well_formed_with_attr}}
```

This has two effects:

 * It adds an extra constraint that *all* `TreeMap` objects satsify the `well_formed()` condition
    at all times. This constraint is checked by Verus whenever a `TreeMap` object is constructed
    or modified.
 * It allows the programmer to _assume_ the `well_formed()` condition at all times, even when
    it isn't present in a `requires` clause.

Note that in addition to adding the `type_invariant` attribute, we have **also removed
the `pub` specifier** from `well_formed`.
Now not only is the body invisible to the client, even the name is as well.
After all, our intent is to prevent the client from needing to reason about it, at which point
there is no reason to expose it through the public interface at all.

Of course, for this to be possible, we'll need to update the specifications of `TreeMap`'s
various `pub` methods.

### Updating the code: `new`

Let's start with an easy one: `new`.

```rust
{{#include ../../../../examples/guide/bst_map_type_invariant.rs:new}}
```

All we've done here is remove the `s.well_formed()` postcondition, which as discussed,
is no longer necessary.

Crucially, Verus still requires us to _prove_ that `s.well_formed()` holds.
Specifically, since `well_formed` has been marked with `#[verifier::type_invariant]`,
Verus checks that `well_formed()` holds when the `TreeMap` constructor returns.
As before, Verus can check this condition fairly trivially.

### Updating the code: `get`

Now let's take a look at `get`. The first thing to notice is that we remove
the `requires self.well_formed()` clause.

```rust
{{#include ../../../../examples/guide/bst_map_type_invariant.rs:get}}
```

Given that we no longer have the precondition, how _do_ we deduce `self.well_formed()`
(which is needed to prove `self.root` is well-formed and call `Node::get_from_optional`)?

This can be done with the built-in pseudo-lemma `use_type_invariant`. When called on any object,
this feature guarantees that the provided object satisfies its type invariants.

### Updating the code: `insert`

Now let's check `TreeMap::insert`, which if you recall, has to modify the tree.

```rust
{{#include ../../../../examples/guide/bst_map_type_invariant.rs:insert}}
```

As before, we use `use_type_invariant` to establish that `self.well_formed()` holds at the
beginning of the function, even without the `requires` clause.

One slight challenge that arises from the use of `#[verifier::type_invariant]` is that it
enforces type invariants to hold at _every_ program point. Sometimes, this can make
intermediate computation a little tricky.

In this case, an easy way to get around this is to [`swap`](https://doc.rust-lang.org/std/mem/fn.swap.html) the `root` field with `None`, then swap back when we're done.
This works because the empty `TreeMap` trivially satisfies the well-formedness, so it's allowed.

One might wonder why we can't just do
`Node::<V>::insert_into_optional(&mut self.root, key, value)`
without swapping. The trouble with this is that it requires us to ensure the call
to `insert_into_optional` is "unwind-safe", i.e., that all type invariants would be preserved
even if a panic occurs and `insert_into_optional` has to exit early. Right now, Verus only
has one way to ensure unwind-safety, which is to bluntly ensure that no unwinding happens
at all.
Thus, the ideal solution would be to mark `insert_into_optional`
as [`no_unwind`](./reference-unwind-sig.md). However, this is impossible in this case, because
node insertion will call `Box::new`.

Between this problem, and Verus's current limitations regarding unwind-safety, the
`swap` approach becomes the easiest solution as a way of sidestepping it.
Check [the reference page](./reference-type-invariants.md) for more information on
the limitations of the `type_invariant` feature.

### Updating the code: `delete`

This is pretty much the same as `insert`.

```rust
{{#include ../../../../examples/guide/bst_map_type_invariant.rs:delete}}
```

### The new signatures and specifications

Putting it all together, we end up with the following specifications for our public API:

```rust
impl<V> TreeMap<V> {
{{#include ../../../../examples/guide/bst_map_type_invariant.rs:new_signature}}

{{#include ../../../../examples/guide/bst_map_type_invariant.rs:insert_signature}}

{{#include ../../../../examples/guide/bst_map_type_invariant.rs:delete_signature}}

{{#include ../../../../examples/guide/bst_map_type_invariant.rs:get_signature}}
}
```

These are almost the same as what we had before; the only difference is that all
the `well_formed()` clauses have been removed.

Conveniently, there are no longer _any_ `requires` clause at all, so it's always possible
to call any of these functions. 
This is also important if we want to prove the API "safe" in the Rust sense
(see [this page](./memory-safety.md)).

### The new client code

As before, the client code gets to reason about the `TreeMap` as if it were just a 
[`Map`](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html).
Now, however, it's a bit simpler because we don't have to reason about `tree_map.well_formed()`.

```rust
{{#include ../../../../examples/guide/bst_map_type_invariant.rs:example_use}}
```

## Full source

The full source for this example can be found [here](./container_bst_all_source.md#version-with-type-invariants).
