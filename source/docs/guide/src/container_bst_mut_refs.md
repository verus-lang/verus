# Mutable references in a container

In this chapter, we'll look at a client application using a `TreeMap<u64, &mut u64>`.
Putting mutable references in a container like this is kind of uncommon, but not unheard of.
In Verus, it takes a little additional know-how.

## A detour through `Vec`

Before looking at `TreeMap`, though, let's do an example with `Vec` to review some of the theory.
Here, we use a vector of mutable references as a way of "indexing" into a triple of local variables.

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:vec_with_mut_refs_broken}}
```

Unfortunately, all 3 assertions will fail to verify, although they are obviously true. Why is this?

Typically, when we have a mutable reference stored in a local variable (say, `a: &mut u64`),
Verus will identify the last mutation to `a` and insert an assumption of the predicate, 
[`has_resolved(a)`](./mutable-references.md#the-has_resolved-operator-when-mutable-references-are-done). This is called the _resolution assumption_ and this assumption is necessary for the
updated value to "flow back" to the borrowed-from location.

Okay, so what happens we have a vector? In this case, the local variable is `v: Vec<&mut u64>`,
so Verus will determine the resolution point for `v`. Immediately after `*v[i] = 1` we have
the resolution point for `v` and learn `has_resolved(v)`. When applied to a container like this,
`has_resolved` is recursive: it means that all mutable references contained _within_ `v` are
resolved.

So we have that `v` is resolved; how do we then get that `v[0]`, `v[1]`, and `v[2]` are resolved?

In this case, vstd provides the axiom [`axiom_vec_has_resolved`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/vec/fn.axiom_vec_has_resolved.html):

```rust
pub broadcast axiom fn axiom_vec_has_resolved<T>(vec: Vec<T>, i: int)
    ensures
        0 <= i < vec.len() ==> has_resolved::<Vec<T>>(vec) ==> has_resolved(vec@[i]);
```

Thus, this law implies that `has_resolved(v[0])`, which should give us the updated value of `a`;
that `has_resolved(v[1])`, which should give us the updated value of `b`;
and that `has_resolved(v[2])`, which should give us the updated value of `c`.

To get the above program to verify, we just need to invoke the resolution axiom,
which can be done either by calling it directly or simply [triggering](./forall.md) the quantifier:

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:vec_with_mut_refs}}
```

## A resolution lemma for `TreeMap`

Now, let's talk about `TreeMap<u64, &mut u64>`.

Using what we learned in the above section, we know that making use of a container of mutable
references requires some kind of `has_resolved` law.
Thus, our `TreeMap` library should export a lemma like:

```rust
has_resolved(map) ==> map@.dom().contains(k) ==> has_resolved(map@[k])
```

How do we prove this?

Verus automatically emits axioms about `has_resolved` for individual structs and enums
(including user-defined ones). For example, if we look at our `TreeMap` struct:

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:tree_map_struct}}
```

Verus will automatically emit an axiom that:

```rust
has_resolved::<TreeMap<K, V>>(map) ==>
    has_resolved::<Option<Box<Node<K, V>>>>(map.root)
```

(at least, when the field is visible). Likewise, there's an axiom for `Option` that will give
us `has_resolved` of the contained value for the `Some` case:

```rust
has_resolved::<Option<T>>(option) ==>
    (option matches Some(x) ==> has_resolved::<T>(x))
```

and finally for Box:

```rust
has_resolved::<Box<U>>(box) ==>
    has_resolved::<U>(*box)
```

So chaining these all together, we can get `has_resolved::<TreeMap<K, V>>(map) ==> has_resolved::<Node<K, V>>(*map.root.unwrap())`. Then we can similarly recurse within the `Node` struct
on the `left` and `right` fields until we reach a value `V`. We just need to put this all together
into an inductive proof:

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:resolved_lemmas}}
```

Now let's try it out with a client:

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:tree_map_with_mut_refs}}
```
