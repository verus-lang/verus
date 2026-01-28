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

To remedy this, Verus provides the `verus_in_verification` flag, which is turned on during
verification, but is otherwise off. This allows us to guard `use` statements like the one above:

```rust
pub mod test_mod {
    #[cfg(verus_in_verification)]
    use crate::ghost_mod::ghost_fn;
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//  OK: During compilation, the `use` statement is removed
}
```

> [!CAUTION]
> This should only be used to guard `use` statements. Using this feature flag
> for conditional compilation of code can introduce **unsoundness**, breaking
> the verification guarantees.

> [!NOTE]
> Verus is under _active development_ meaning this option may change or be removed
> (in particular if a better solution to this problem is devised). See the [Github discussion](https://github.com/verus-lang/verus/discussions/2101)
> for more information.

## `Cargo.toml` configuration

[Since version 1.80](https://blog.rust-lang.org/2024/05/06/check-cfg/), Rust automatically checks if all `cfgs` match expected config names.
The `verus_in_verification` feature is passed in directly by Verus and never declared in a
`Cargo.toml`. This means that Rust will emit a warning when compiling. To prevent this, add the
following to your `Cargo.toml`:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = [
  'cfg(verus_in_verification)',
] }
```

> [!NOTE]
> This is done automatically when initializing the repository with `cargo verus new`
