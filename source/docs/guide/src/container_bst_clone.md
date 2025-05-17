# Implementing Clone

As a finishing touch, let's implement `Clone` for `TreeMap<K, V>`.
The main trick here will be in figuring out the correct specification for `TreeMap::<K, V>::Clone`.

Naturally, such an implementation will require both `K: Clone` and `V: Clone`.
However, to write a sensible clone implementation for the tree, we have to consider
what the implementations of `K::clone` and `V::clone` actually do.

Generally speaking, Verus imposes no constraints on the implementations of `Clone`,
so it is not necessarily true that a `clone()` call will return a value that is spec-equal
to its input.

With this in mind, to simplify this example,
we're going to prove the following signature for `TreeMap<K, V>::clone`:

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:clone_signature}}
    {
        ...
    }
}
```
We explain the details of this signature below.

### Dealing with `K::clone`

In order to clone all the keys, we need `K::clone` to respect the ordering of elements; 
otherwise during a clone operation,
we'd need to re-sort all the keys so that the resulting tree would be valid.
However, it's unlikely that is desirable behavior. If `K::clone` doesn't respect the
`TotalOrdered` implementation, it's likely a user bug.

A general way to handle this would be to require that `Clone` actually be compatible
with the total-ordering in some sense.
However, you'll
recall from the previous section that we're already simplifying the "total ordered" specification
a bit. Likewise, we're going to continue to keep things simple here by also requiring
that `K: Copy`.

As a result, we'll be able to prove that our `TreeMap` clone implementation can preserve
all keys exactly, even when compared via spec equality. That is, we'll be able to
ensure that `self@.dom() =~= res@.dom()`.

### Dealing with `V::clone`

So what about `V`? Again, we don't know _a priori_ what `V::clone` does. It might return
a value unequal to the imput; it might even be nondeterminstic. Therefore,
a cloned `TreeMap` may have different values than the original.

In order to specify `TreeMap::<K, V>::clone` as generically as possible, we choose
to write its ensures clause _in terms of_ the ensures clause for `V::clone`.
This can be done using [`call_ensures`](./exec_funs_as_values.md).
The predicate `call_ensures(V::clone, (&self@[key],), res@[key])` effectively says
"`self@[key]` and `res@[key]` are a possible input-output pair for `V::clone`".
This predicate is a mouthful, so `vstd` provides a helper function:
<code class="hljs"><a href="https://verus-lang.github.io/verus/source/doc/vstd/pervasive/fn.cloned.html">cloned::&lt;V&gt;</a>(self@[key], res@[key])</code>

### Understanding the implications of the signature

Let's do a few examples.

First, consider cloning a `TreeMap::<u64, u32>`. The Verus standard library provides
a specification for `u32::clone`; it's the same as a copy, i.e., a cloned `u32` always
equals the input. As a result, we can deduce that cloning a `TreeMap::<u64, u32>` will
preserve its `view` exactly. We can prove this using [extensional equality](./extensional_equality.md).

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:clone_u32}}
```

We can do the same for _any_ type where `clone` guarantees spec-equality. Here's another
example with a user-defined type.

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:clone_int_wrapper}}
```

This works because of the postcondition on `IntWrapper::clone`, that is, `ensures *s == self`.
If you're new to this style, it might seem initially surprising that 
`IntWrapper::clone` has any effect on the verification of `test_clone_int_wrapper`, since
it doesn't directly call `IntWrapper::clone`. In this case, the postcondition is referenced
indirectly via `TreeMap<u64, IntWrapper>:clone`.

Let's do one more example, this time with a _less_ precise clone function.

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:clone_weird_int}}
```

This example is a bit pathological; our struct, `WeirdInt`, has an extra field that doesn't
get cloned. You could imagine real-life scenarios that have this property (for example,
if every struct needs to have a unique identifier). Anyway, the postcondition of
`WeirdInt::clone` doesn't say both objects are equal, only that the `int_value` fields are equal.
This postcondition can then be inferred for each value in the map, as shown.

### Implementing `TreeMap::<K, V>::Clone`.

As usual, we write the implementation as a recursive function.

It's not necessary to implement `Node::Clone`; one could instead just implement a normal
recursive function as a helper for `TreeMap::Clone`; but it's more Rust-idiomatic to do it
this way. This lets us call `Option<Node<K, V>>::Clone`
in the implementation of `TreeMap::clone` (the spec for `Option::clone` is provided by
vstd). However, you can see that there are a few 'gotchas' that need
to be worked around.

```rust
{{#include ../../../../examples/guide/bst_map_generic.rs:clone_full_impl}}
```

## Full source

The full source for this example can be found [here](./container_bst_all_source.md#version-with-generic-key-type-and-clone-implementation).
