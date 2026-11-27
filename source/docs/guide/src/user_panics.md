# User panics

By default, Verus checks for the absense of what we call "user panics", by which we mean
panics that can reasonably be defended against by conditions on their input,
but it does not check against errors due to memory exhaustion ("OOM") or unpredictable
system failures.

```rust
fn test_unwrap(a: Option<u64>) {
    let x = a.unwrap(); // possible panic: Verus makes you prove that `a != None`
}

fn test_vec_idx(v: Vec<u64>) {
    let x = v[0]; // possible panic: Verus makes you prove that the index is in bounds
}

fn test_box() {
    let x = Box::new(0); // could potentially panic due to OOM, but Verus
                         // lets this pass without issue
}

fn test_explicit_panic(a: Option<u64>) {
    panic!("panic"); // definite panic: Verus makes you prove this line is unreachable
}
```

## Disabling all panic-checking

In some cases, we may want to disable this behavior. For example, suppose we want to write
a function which panics on malformed input, like this `checked_double` function:

```rust
fn checked_double(x: u8) -> (res: u8)
    ensures res == 2 * x,
{
    if x >= 128 {
        panic!("checked_double: overflow");
    }
    x * 2
}
```

But ... we get an error.

```rust
error: possible panic
   --> panic_example.rs:9:9
    |
    |         panic!("checked_double: overflow");
    |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ call to core::panicking::panic_fmt might panic
```

Right, as we said above, Verus disallows most panics by default. That includes explicit panicking
functions like `core::panicking::panic_fmt`, the internal panic function used by the `panic!` macro.

The option that configures this is called `check_user_panics`, which is set to `true` by default.

Let's try again, with `check_user_panics` set to false. This attribute can be applied to any
function or expression, or declared once at the crate level.

```rust
#[check_user_panics(false)]
fn checked_double(x: u8) -> (res: u8)
    ensures res == 2 * x,
{
    if x >= 128 {
        panic!("checked_double: overflow");
    }
    x * 2
}
```

The ensures clause is only checked on a _normal_ exit (i.e., a non-panicking exit),
so the `panic!` branch isn't considered when proving the `res == 2 * x` postcondition.

## Caveats

Note that `check_user_panics(true)` is _not_ the same as asserting that 
no panics occur. Non-user panics can still occur; further, `check_user_panics` is not checked
transitively. 

Also note that `check_user_panics(false)` does not necessarily absolve you of conditions
related to panicking. Every function is still required to obey its specification; e.g.,
a function marked `no_panic` (as we'll see in the [next section](./panic_specs.md)) would be required not to panic.
Finally, there are some situations where "recoverable panics" are not safe,
as we'll see (TODO links), and must therefore be disallowed
regardless of the `check_user_panics` attribute.

## Conclusion

The `check_user_panics` aims to strike a good balance for beginners (and for a lot of application
code) by proving code free of common sources of failure without overburdening the user with
panics they can't reasonably defend against.

If the "user panics" idea seems a little loosey-goosey to you, read on to see how to write
(and prove) more precise specifications about panicking behavior.
