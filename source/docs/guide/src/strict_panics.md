# Strict verification: absolute panic-freedom

Proving absolute panic freedom is often a high bar to clear.
As explained in the [previous section](./panic_specs.md), a panic-free specification 
can be written by simply writing `no_panic`.

```rust
fn foo()
    no_panic
{
    // ...
}
```

That's simple enough, but proving it is another matter. It's one thing to prove the absence
of integer overflow and out-of-bounds accesses, but it's another to avoid every obscure error
condition. Just about any system function could potentially panic, and even using `Box` or `Vec`
accesses the allocator, which could panic in the event of an out-of-memory error.

> [!NOTE]
> The situation with allocators gets more complicated when we consider that the global allocator
> can be overridden. Rust does not currently guarantee that such an allocator will never unwind.
> We are still deciding how Verus should reason about such scenarios.

The best case scenario for a strict `no_panic` specification is something strictly computational,
like a serializer/deserializer or a cryptographic library.

For code that absolutely has to deal with the allocator or other system components, see
[Dealing with system errors](./system_errors.md).
