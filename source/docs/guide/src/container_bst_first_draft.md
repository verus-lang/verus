# A simple binary search tree

In this section, we're going to be implementing and verifying a Binary Search Tree (BST).

In the study of data structures, there are
[many](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)
[known](https://en.wikipedia.org/wiki/AVL_tree)
[ways](https://en.wikipedia.org/wiki/Treap)
[to](https://en.wikipedia.org/wiki/Splay_tree)
[balance](https://en.wikipedia.org/wiki/B-tree)
a binary search tree.
To keep things simple, we won't be implementing any of them—instead,
we'll be implementing a straightforward,
_unbalanced_ binary search tree. Improving the design to be more efficient will be left
as an exercise.

Furthermore, our first draft of an implementation is going to map keys
of the fixed orderable type, `u64`, to values of type `V`. In a later chapter,
we'll change the keys to also be generic, thus mapping `K` to `V` for arbitrary types
`K` and `V`.

## The implementation

### The structs

We'll start by defining the tree shape itself, which contains one (key, value) pair at every
node. We make no distinction between "leaf nodes" and "interior nodes". Rather, every node
has an optional left child and an optional right child.
Furthermore, the tree might be entirely empty, in which case there is no root.

```rust
{{#include ../../../../examples/guide/bst_map.rs:StructsDef}}
```

Note that only `TreeMap` is marked `pub`. Its field, `root`, as well as the `Node` type
as a whole, are implementation details, and thus are private to the module.

### The abstract view

When creating a new data structure, there are usually two important first steps:

 * Establish an interpretation of the data structure as some abstract datatype that will
   be used to write specifications.
 * Establish the well-formedness invariants of the data structure.

We'll do the first one first (in part because it will actually help with the second one).
In this case, we want to interpret the data structure as a
[`Map<u64, V>`](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html).
We can define such a function recursively.

```rust
{{#include ../../../../examples/guide/bst_map.rs:AsMapDef}}
```

Again note that only `TreeMap::as_map` is marked `pub`, and furthermore, that it's marked
`closed`. The definition of `as_map` is, again, an implementation detail.

It is customary to also implement the
[`View` trait](https://verus-lang.github.io/verus/verusdoc/vstd/view/trait.View.html)
as a convenience. This lets clients refer to the map implementation using the `@` notation,
e.g., `tree_map@` as a shorthand for `tree_map.view()`.
We'll be writing our specifications in terms of `tree_map.view()`.

```rust
{{#include ../../../../examples/guide/bst_map.rs:ViewDef}}
```

### Establishing well-formedness

Next we establish well-formedness. This amounts to upholding the BST ordering property,
namely, that for every node _N_, the nodes in _N_'s left subtree have keys less than
_N_, while the nodes in _N_'s right subtree have keys greater than _N_.
Again, this can be defined by a recursive `spec` function.

```rust
{{#include ../../../../examples/guide/bst_map.rs:WellFormedDef}}
```

### Implementing a constructor: `TreeMap::new()`

Defining a constructor is simple; we create an empty tree with no root.
The specification indicates that the returned object must represent the _empty_ map.

```rust
{{#include ../../../../examples/guide/bst_map.rs:new}}
```

Recall that `tree_map@` is equivalent to `tree_map.as_map()`.
An inspection of the definition of `tree_map.as_map()` and `Node::optional_as_map()` should
make it apparent this will be the empty map when `root` is `None`.

Observe again that this specification does not refer to the tree internals at all,
only that it is well-formed and that its abstract view is the empty map.

### Implementing the `insert` operation

We can also implement `insert` using a recursive traversal. We search for the given node,
using the well-formedness conditions to prove that we're doing the right thing.
During this traversal, we'll either find a node with the right key, in which case we update
the `value`, or we'll reach a leaf without ever finding the desired node, in which case we
create a new node.

(Aside: One slight snag has to do with a limitation of Verus's handing of mutable references.
Specifically, Verus doesn't yet support an easy way to get a
`&mut T` out of a `&mut Option<T>`. To get around this, we use [`std::mem::swap`](https://doc.rust-lang.org/std/mem/fn.swap.html) to get ownership of the node.)

```rust
{{#include ../../../../examples/guide/bst_map.rs:insert}}
```

Observe that the specification of `TreeMap::insert` is given in terms of
[`Map::insert`](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.remove).

### Implementing the `delete` operation

Implementing `delete` is a little harder, because if we need to remove an interior node,
we might have to reshape the tree a bit. However, since we aren't trying to follow
any particular balancing strategy, it's still not that bad:

```rust
{{#include ../../../../examples/guide/bst_map.rs:delete}}
```

Observe that the specification of `TreeMap::delete` is given in terms of
[`Map::remove`](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.remove).

### Implementing the `get` operation

Finally, we implement and verify `TreeMap::get`.
This function looks up a key and returns an `Option<&V>` (`None` if the key isn't in the
`TreeMap`).

```rust
{{#include ../../../../examples/guide/bst_map.rs:get}}
```

### Using the `TreeMap` as a client

A short client program illustrates how we can reason about the `TreeMap` as if it were
a [`Map`](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html).

```rust
{{#include ../../../../examples/guide/bst_map.rs:test}}
```

## Full source

The full source for this example can be found [here](./container_bst_all_source.md#first-draft).
