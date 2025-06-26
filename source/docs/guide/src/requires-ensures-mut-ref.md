# Requires and ensures with mutable references

If a function takes a mutable reference, say `x: &mut T`, as an argument, then function specification
needs to be able to refer to _two_ different value: the value behind the mutable reference
_before_ the function executes, and the value _after_.

More specifically, the `requires` clause will need to refer to the pre-value,
while the `ensures` clause may need to refer to either (e.g., to specify how the value changes
over the course of the function).

 * To refer to the pre-state, use `*old(x)`
 * To refer to the post-state, use `*x`.

(Note that this implies that in the `requires` clause, the mutable reference's value can _only_
be referred to by using `old`.)

### Example

The following example shows how we can use the `requires` clause to constraint the input value,
while the `ensures` clause relaets to the new value to the input value:

```rust
{{#include ../../../../examples/guide/references.rs:requires}}
```

In the `increment` function call, `*old(a)` refers to the dereferenced value of the mutable reference `a` at the *beginning* of the function call and `*a` in the `ensures` clause refers to the dereferenced value of the mutable reference `a` at the end of the function call.
