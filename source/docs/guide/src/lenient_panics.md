# Lenient verification: panic whenever

Sometimes, you might not care about proving panic-freedom at all. Maybe you have much bigger things
to worry about, like data loss or corruption—in your mind, sometimes the _best_ thing a program
can do is panic because a stopped program can do no wrong.

If this is you, all you have to do is put `#![verifier::check_user_panics(false)]` at the top
of your crate, and Verus won't complain about any panics.

Not only that, but you often get to deduce certain facts about "for free"
using the fact that certain opertations _don't_ panic.

```rust
fn test(a: Vec<u64>, i: u64) {
    let j = a[i]; // might panic

    assert(i < a.len()); // this is ok; if `i >= a.len()`, then `a[i]` would
                         // have panicked and this statement would be unreachable
}
```

> [!NOTE]
> At present, many functions in `vstd` are still missing panic-level specifications, meaning
> their preconditions are still hard requirements, even with 
> `#[verifier::check_user_panics(false)]`.
> Furthermore, primitive operations like array/slice-indexing or arithmetic do not
> presently recognize this attribute.

> ![NOTE]
> Even with `#![verifier::check_user_panics(false)]` you may still be required to reason about
> unwinding paths. See [Recoverable panics](./recoverable_panics.md).
