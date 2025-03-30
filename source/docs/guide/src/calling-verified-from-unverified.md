# Calling verified code from unverified code

When writing verified code that may be called from unverified code,
you should be careful with the specifications you provide on your external API.
In particular, any preconditions on external API functions are **assumptions**
about what your caller will pass in.  The stronger the precondition (i.e., assumption),
the more likely it is that a caller will fail to meet it, meaning that all of 
your verification work may be undermined.

Ideally, you should aim to have no preconditions on your external API;
if you don't make any assumptions about your caller, you'll never be disappointed!
You can check if your verified crate meets these requirements by using the flag `-V check-safe-api`.
Specifically, this flag will check if your crate is unconditionally safe to be used from
any unverified code that does not use `unsafe`.

### Tips for eliminating preconditions

If your API _does_ have important preconditions, you might consider adding
a wrapper around it that has no preconditions, dynamically checks that the
necessary preconditions hold, and then calls an internal version of your API.
Verus will, of course, check that your dynamic checks suffice to establish the necessary
preconditions. You can then mark the inner function—the one with the preconditions—as `unsafe`.
This will prevent the client from calling it without declaring its intent to bypass the checks.

For example:

```rust
pub unsafe fn index_unchecked<T>(vec: &Vec<T>, i: usize) -> &T
    requires i < vec.len()
{
    /* ... */
}

pub fn index<T>(vec: &Vec<T>, i: usize) -> Option<&T>
{
    if i < vec.len() {
        Some(index_unchecked(vec, i))
    } else {
        None
    }
}
```

If your API involves passing state back and forth between your code and your caller,
then you can consider defining a public struct with private fields that contain your
state.  Since your caller cannot create their own versions of the struct, or modify
values in the structs you give them, then you can (reasonably) safely use pre- and 
post-conditions on your API (or [type invariants](container_bst_type_invariant.md) 
to maintain invariants about the contents of such structs.
