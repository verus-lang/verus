# Requires and ensures with mutable references

As stated before, `requires` and `ensures` represent preconditions and postconditions that connect functions together.

If a function takes a mutable reference as an argument, then any statement in the `requires` and `ensures` about the state of the piece of memory to which the mutable reference points *before* the function is called must refer to this prior state using the `old()` function. This function takes a mutable reference and returns a mutable reference. In the `requires` clause, one can *only* refer to this prior state. Consider the following example:

```rust
{{#include ../../../../examples/guide/references.rs:requires}}
```

In the `check_and_inc` function call, `*old(a)` refers to the dereferenced value of the mutable reference `a` at the *beginning* of the function call and `*a` in the `ensures` refers to the dereferenced value of the mutable reference `a` at the end of the function call. 