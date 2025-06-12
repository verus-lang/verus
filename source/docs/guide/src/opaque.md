# Modules, hiding, opaque, reveal

One possible cause for verification timeouts is unfolding a function definition that is especially complex, or contains problematic quantifiers.

To prevent automatic unfolding, you can use `opaque` to hide the body of the function from the verifier. You can then use `reveal` to selectively "reveal" the body of the function in places where you want the verifier to unfold its definition.

Here's a small example of how to use `opaque` and `reveal`:

```rust
{{#include ../../../../examples/guide/opaque.rs:opaque}}
```

This is very similar to `closed spec` functions discussed in the [previous section](spec_functions.md)! The main difference is that `opaque` and `reveal` are more flexible. `opaque` hides the function body even in the current module, so you can use reveal to selectively expose the function body in specific proof blocks.

In general, you want to use `closed spec` if you want to have the function body available in the current module, and you build proof functions about this specification in the same module. So you all you need outside the module is the public proof functions related to this `spec` function. Therefore `open` and `closed` spec function are well suited for abstraction, whereas `opaque` is a mechanism for controlling automation and verification performance, rather than modularity.

You can see more advanced use of hiding a function body in the [reference](reference-reveal-hide.md).
