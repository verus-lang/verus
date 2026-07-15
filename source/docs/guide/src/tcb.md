# Assumptions and trusted components

Often times, it's not possible to verify every line of code and some things need to be
_assumed_. In such cases, the ultimate correctness of the code is dependent not just
on verification but on the assumptions being made.

Assumptions can be introduced through the following mechanisms:

 * As [`assume`](./requires_ensures.md) statement
 * An axiom - any proof function introduced with [`#[verifier::external_body]`](./calling-unverified-from-verified.md)
 * An axiomatic specification - any exec function introduced with `#[verifier::external_body]` or `#[verifier::external_fn_specification]`
 * `#[verifier::external]` (See below.)

Types (structs and enums) can also be marked as `#[verifier::external_body]`,
though to be pedantic, this does not introduce a new assumption _per se_.
In practice, though, such types are usually associated with additional assumptions
to make them useful.

To control where these assumptions may appear, Verus offers a [`--no-cheating` mode](#no-cheating-mode)
that confines them to an auditable set of files.

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
which prohibits all such "cheating" by default and forces all assumptions to be confined to a
small, auditable set of files. It follows
[Rust's lint levels](https://doc.rust-lang.org/rustc/lints/levels.html), using the
`verus::assumptions` lint.

When Verus is run with `--no-cheating`, the following are rejected anywhere assumptions are not
explicitly allowed:

 * [`assume`](./requires_ensures.md#assert-and-assume) and `admit`
 * [`#[verifier::external_body]`](./calling-unverified-from-verified.md) on functions (including axioms)
 * [`assume_specification`](./reference-assume-specification.md) and `#[verifier::external_fn_specification]`
 * [`#[verifier::assume_termination]`](./reference-attributes.md#verifierassume_termination)
 * calls enabled by `externals_available_without_declaration`

(`#[verifier::external]` is not affected, since on its own it does not introduce an assumption.)

### Defining trusted modules

To opt-in to the no-cheating mode checking, the crate root must include a crate-level attribute:

```rust
#![deny(verus::assumptions)]
```

With this in place, no assumptions are permitted anywhere in the crate. To carve out an exception,
mark a module with `#[allow(verus::assumptions)]`:

```rust
#![deny(verus::assumptions)]

#[allow(verus::assumptions)]
mod assumptions; // assumptions are permitted in assumptions.rs and its submodules
```

So that the assumption-bearing code is easy to find and audit, Verus enforces these rules:

 * `#[allow(verus::assumptions)]` may appear **only in the crate root**, and **only on a `mod` item**.
 * That `mod` must be a **file-level module** (`mod name;`, not an inline `mod name { ... }`),
   so every allowed file is named in one place.
 * The allowed modules must be **closed under references**: code in an allowed module (or any of
   its submodules) may only refer to other allowed modules, to [`vstd`](./vstd.md), to other
   external crates, and to items in the crate root. It may not refer to ordinary (non-allowed)
   modules of the same crate.

The last rule keeps the trusted, assumption-bearing part of the crate self-contained: the verified
core may freely build on the allowed modules, but the allowed modules cannot reach back into the
verified core.  This creates a clear separation between what code is verified, and what code
is trusted and hence must be audited.

### Example

```rust
// lib.rs (crate root)
#![deny(verus::assumptions)]

// Trusted models of the environment and external dependencies live here:
#[allow(verus::assumptions)]
mod trusted;

// ...the rest of the crate is fully verified, with no assumptions...
```

```rust
// trusted.rs
use vstd::prelude::*;

verus! {

// OK: assumptions are allowed in this module and its submodules.
pub proof fn environment_axiom()
    ensures some_property(),
{
    assume(some_property());
}

}
```
