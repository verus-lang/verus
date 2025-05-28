# Requires and ensures with mutable references

As stated before, `requires` and `ensures` represent preconditions and postconditions that connect functions together.

If a function takes a mutable reference as an argument, then any statement about the state of the piece of memory to which the mutable reference points *before* the function is called must refer to this prior state using the `old()` function. Consider the following example:

```rust
{{#include ../../../../examples/guide/references.rs:requires}}
```