# Making it generic

In the previous sections, we devised a `TreeMap<V>` which a used fixed key type (`u64`).
In this section, we'll show to make a `TreeMap<K, V>` which is generic over the key type `K`.

## Defining a "total order"

The main reason this is challenging is that the BST requires a way of _comparing_
values of `K`, both for equality, and to obtain an ordering. This comparison is used both
in the implementation (to find the node for a given key, or to figure out where such
a node should be inserted) and in the well-formedness invariants that enforce
the BST ordering property.

We can define the concept of ["total order"](https://en.wikipedia.org/wiki/Total_order)
generically by creating a trait.

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:trait}}
```

This trait simultaneously:

 * Requires a binary relation `le` to exist
 * Requires it to satisfy the properties of a total order
 * Requires an `executable` three-way comparison function to exist

There's one simplification we've made here: we're assuming that "equality" in the comparison
function is the same as [spec equality](./equality.md).
This isn't always suitable; some datatypes may have more than one way to represent the same
logical value. A more general specification would allow an ordering that respects
some arbitrary equivalence relation.
This is how [`vstd::hash_map::HashMapWithView`](https://verus-lang.github.io/verus/verusdoc/vstd/hash_map/struct.HashMapWithView.html) works, for example.
To keep things simple for this demonstration though, we'll use a total ordering that respects
spec equality.

### Updating the struct and definitions

We'll start by updating the structs to take a generic parameter `K: TotalOrdered`.

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:structs}}
```

We'll also update the well-formedness condition to use the generic `K::le` instead of integer `<=`.
Where the original definition used `a < b`, we now use `a.le(b) && a != b`.

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:well_formed}}
```

Meanwhile, the definition of `as_map` doesn't rely on the ordering function,
so it can be left alone, the same as before.

### Updating the implementations and proofs

Updating the implementations take a bit more work, since we need more substantial proof code.
Whereas Verus has good automation for integer inequalities (`<`), it has no such automation
for our new, hand-made `TotalOrdered` trait. Thus, we need to add proof code to invoke
its properties manually.

Let's take a look at `Node::get`.

The meat of the proof roughly goes as follows:

Supoose we're looking for the key `key` which compares less than `self.key`.
Then we need to show that recursing into the left subtree gives the correct answer; for this,
it suffices to show that `key` is _not_ in the right subtree.

Suppose (for contradiction) that `key` _were_ in the right subtree.
Then (by the well-formedness invariant), we must have `key > self.key`.
But we already established that `key < self.key`. Contradiction.
(Formally, this contradiction can be obtained by invoking antisymmetry.)

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:node_get}}
```

We can update `insert` and `delete` similarly, manually inserting lemma calls to invoke
the total-ordering properties where necessary.

## Full source

The full source for this example can be found [here](./container_bst_all_source.md#version-with-generic-key-type-and-clone-implementation).
