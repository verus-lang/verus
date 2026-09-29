# Assumptions and trusted components

Often times, it's not possible to verify every line of code and some things need to be
_assumed_. In such cases, the ultimate correctness of the code is dependent not just
on verification but on the assumptions being made.

Assumptions can be introduced through the following mechanisms:

 * As [`assume`](./requires_ensures.md) statement
 * An axiom - any function introduced with [`#[verifier::external_body]`](./calling-unverified-from-verified.md) or declared as an `axiom fn`
 * An axiomatic specification - any exec function introduced with `#[verifier::external_body]` or `#[verifier::external_fn_specification]`
 * `#[verifier::external]` (See below.)

Types (structs and enums) can also be marked as `#[verifier::external_body]`,
though to be pedantic, this does not introduce a new assumption _per se_.
In practice, though, such types are usually associated with additional assumptions
to make them useful.

To control where these assumptions may appear, Verus offers a [`--no-cheating` mode](#no-cheating-mode)
that confines them to explicitly trusted code.

### The `#[verifier::external]` attribute

The `#[verifier::external]` annotation tells Verus to ignore an item entirely.
It can be applied to any item - a function, trait, trait implementation, type, etc.

For many items (functions, types, trait declarations), this does not, _on its own_,
introduce any new "assumptions" about that item.
Attempting to call an `external` function from a verified
function, for example, will result in an error from Verus. In practice, a developer
will often call an `external` function (say `f`) from an `external_body` function (say `g`),
in which case, the `external_body` attribute introduces assumptions about `g`, thus
_indirectly_ introducing assumptions about `f`.

Furthermore, adding `#[verifier::external]` to a _trait implementation_ requires even more
careful consideration, as Verus relies on rustc's trait-checking for some things,
so trait implementations can sometimes affect what code gets accepted or rejected.

For example:

```rust
#[verifier::external]
unsafe impl Send for X { }
```

## No-cheating mode

By default, Verus lets you introduce unverified assumptions through the mechanisms above.
To increase your project's assurance, we recommend using the `--no-cheating` command-line flag,
which prohibits all such "cheating" by default and forces assumptions to be confined to
explicitly trusted, auditable code.

When Verus is run with `--no-cheating`, the following are rejected anywhere assumptions are not
explicitly allowed:

 * [`assume`](./requires_ensures.md#assert-and-assume) and `admit`
 * [`#[verifier::external_body]`](./calling-unverified-from-verified.md) on functions (including axioms)
 * [`assume_specification`](./reference-assume-specification.md) and `#[verifier::external_fn_specification]`
 * [`#[verifier::assume_termination]`](./reference-attributes.md#verifierassume_termination)
 * calls enabled by `externals_available_without_declaration`

(`#[verifier::external]` is not affected, since on its own it does not introduce an assumption.)

### Marking trusted code

Code is untrusted by default. Use `#[verus::trusted]` to permit assumptions in a file, module,
or item.  An inner attribute applies at file level:

```rust
// environment.rs
#![verus::trusted]
```

Use outer attributes at the module or item level:
```rust
#[verus::trusted]
mod environment;
```

The trusted label is inherited by child items. A child can opt back into normal
no-cheating checking with `#[verus::untrusted]`.  Once an item is explicitly
marked `untrusted`, none of its descendants may use `trusted` or `trusted(spec)`.

```rust
#[verus::trusted]
mod environment {
    // Trusted through inheritance.
    proof fn platform_axiom() {
        assume(platform_property());
    }

    // Assumptions are prohibited here and in all descendants.
    #[verus::untrusted]
    mod verified_model {
        // ...
    }
}
```

### Trusted closure

Trusted code must be transitively closed within its crate: every local item referenced by trusted
code must also be trusted.  This way, changes to untrusted code within the crate cannot affect
the assumptions, definitions, etc. made by trusted code.

References to [`vstd`](./vstd.md) and other external crates are allowed.
Crate-root `use` declarations are ignored as closure roots, but a reference
through such an import is checked against the actual item it resolves to.

Untrusted code may freely reference trusted code. This gives the trusted base a clear dependency
boundary and keeps the code that must be audited self-contained.

### Trusting only a function specification

A function may use `#[verus::trusted(spec)]`. This marks only the function's interface as trusted:

 * its Rust type signature, generic bounds, and associated types;
 * its Verus specification, including `requires`, `recommends`, `ensures`, `returns`, `decreases`,
   invariant-mask, unwind, and related clauses.

The implementation body remains untrusted: it may not contain `assume`, `external_body`, or any
other construct prohibited by `--no-cheating`. References made only by the implementation body
are not part of the trusted reference-closure check, so the body may call ordinary untrusted code.
`trusted(spec)` may only be applied directly to a function.

### Example

```rust
// lib.rs (crate root)
// Trusted models of the environment and external dependencies live here:
#[verus::trusted]
mod trusted;

// ...the rest of the crate is fully verified, with no assumptions...
```

```rust
// trusted.rs
use vstd::prelude::*;

verus! {

// OK: assumptions are allowed because the module is trusted.
pub proof fn environment_axiom()
    ensures some_property(),
{
    assume(some_property());
}

}
```
