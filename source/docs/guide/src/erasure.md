# Ghost Erasure

Verus performs ghost erasure: ghost code that exists for verification purposes is removed when
building the executable artifacts, ensuring they are minimally disturbed.

One byproduct of this is that certain identifiers that exist at verification time will not exist at
compile time. This means that the code shown below would fail to _compile_:

```rust
use vstd::prelude::*;

verus! {

pub mod ghost_mod {
    pub closed spec fn ghost_fn() -> bool { true }
}

pub mod test_mod {
    use crate::ghost_mod::ghost_fn;
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//  FAILS: During compilation, ghost_fn is erased, causing rustc
//         to complain about a missing definition

    pub fn exec_fn() -> u64 {
        1
    }
}
```

To remedy this, Verus provides the `verus_only` flag, which is turned on during
verification, but is otherwise off. This allows us to guard `use` statements like the one above:

```rust
pub mod test_mod {
    #[cfg(verus_only)]
    use crate::ghost_mod::ghost_fn;
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//  OK: During compilation, the `use` statement is removed
}
```

Anoter use-case for the `verus_only` flag is setting attributes that only make sense during verification.
For instance, the code below sets the `verifier::loop_isolation` option to false for the file, only if `verus_only` is set:
```rust
#![cfg_attr(verus_only, verus::loop_isolation(false))]
```


> [!CAUTION]
> This should only be used to guard `use` statements and setting config attributes.
> Using this feature flag for conditional compilation of code can introduce **unsoundness**,
> breaking the verification guarantees.
>
> As an example, the code below will verify successfully, even though it `f()` returns
> 42 when running the executable.
>
> ```rust
> fn f() -> (u: u32)
>   ensures u != 0
> {
>   #[cfg(verus_only)]
>   { return 0; }
>   #[cfg(not(verus_only))]
>   { return 42; }
> }
> ```

> [!NOTE]
> Verus is under _active development_ meaning this option may change or be removed
> (in particular if a better solution to this problem is devised). See the [Github discussion](https://github.com/verus-lang/verus/discussions/2101)
> for more information.

## `Cargo.toml` configuration

[Since version 1.80](https://blog.rust-lang.org/2024/05/06/check-cfg/), Rust automatically checks if all `cfgs` match expected config names.
The `verus_only` feature is passed in directly by Verus and never declared in a
`Cargo.toml`. This means that Rust will emit a warning when compiling. To prevent this, add the
following to your `Cargo.toml`:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = [
  'cfg(verus_only)',
] }
```

> [!NOTE]
> This is done automatically when initializing the repository with `cargo verus new`
