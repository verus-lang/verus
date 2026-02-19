# External trait specifications

When writing verified code that interacts with external Rust libraries, you may need
to add specifications to traits defined in those libraries. Verus provides two attributes
for this purpose:

 * `#[verifier::external_trait_specification]` — adds requires/ensures to trait methods
 * `#[verifier::external_trait_extension]` — additionally defines spec helper functions on the trait

## Soundness warning

**Be cautious when adding specifications to external traits.** All implementations
of the trait — including those in unverified code, even code that hasn't been written yet — are
assumed to uphold the specification. For example, if you verify a crate with
`pub fn test<A: Formatter>(...)`, Verus assumes that whatever type instantiates `A` will
satisfy the `Formatter` specification, even if that type comes from an unverified crate.
This is a contract on both current and future unverified code.

[See below](the_obeys_pattern_in_vstd) for a useful pattern (employed by `vstd`) for mitigating this soundness risk.

## Basic external trait specification

Suppose we have an external trait:

```rust
{{#include ../../../../examples/guide/external_trait_specs.rs:basic_trait}}
```

We can add specifications to it with `#[verifier::external_trait_specification]`:

```rust
{{#include ../../../../examples/guide/external_trait_specs.rs:basic_spec}}
```

Key points about this syntax:
 * The specification trait (here `ExEncoder`) must contain a specially named associated type
   `ExternalTraitSpecificationFor` whose bound names the external trait being specified.
 * The trait name `ExEncoder` is arbitrary and is not used elsewhere.
 * Method signatures must match the external trait, but you can add `requires` and `ensures` clauses,
   and you can give a name to the return value (e.g., `(result: u64)`) for use in `ensures`.
 * The specification trait is not required to include all members of the external trait.
   Members that are not included are not accessible to verified code.

With the specification in place, verified code can use the trait:

```rust
{{#include ../../../../examples/guide/external_trait_specs.rs:basic_use}}
```

## External trait extension (spec helper functions)

Sometimes, a trait specification needs additional spec-mode functions that don't
exist in the original trait. For example, you may want a spec function that describes the
abstract behavior of a method. The `#[verifier::external_trait_extension]` attribute supports this.

The attribute takes the form:
```
#[verifier::external_trait_extension(SpecTrait via SpecImplTrait)]
```

 * **SpecTrait** is the name of a spec-mode trait that becomes available in verification.
   It is automatically implemented for any type implementing the external trait.
 * **SpecImplTrait** is the name of a trait that concrete types implement to define the
   spec helper functions.

Here is an example, using a fictitious external trait named `Summarizer`:

```rust
{{#include ../../../../examples/guide/external_trait_specs.rs:extension_spec}}
```

Concrete types implement `SpecImplTrait` (here `SummarizerSpecImpl`) to define the spec helpers,
and can then use the specifications in verified code:

```rust
{{#include ../../../../examples/guide/external_trait_specs.rs:extension_impl}}
```

## The `obeys_*` pattern in `vstd`

`vstd` uses `external_trait_extension` extensively for standard library traits like `PartialEq`,
`Ord`, `Add`, `From`, etc.  These specifications follow a common pattern using an `obeys_*`
spec function that indicates whether a given type implementation actually follows the
specification.

For example, `vstd`'s specification for `PartialEq` looks roughly like this:

```rust
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PartialEqSpec via PartialEqSpecImpl)]
pub trait ExPartialEq<Rhs = Self> {
    type ExternalTraitSpecificationFor: PartialEq<Rhs>;

    spec fn obeys_eq_spec() -> bool;
    spec fn eq_spec(&self, other: &Rhs) -> bool;

    fn eq(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_eq_spec() ==> r == self.eq_spec(other);
}
```

The ensures clause says: **if** the type obeys the Verus spec for `Eq` (`obeys_eq_spec()` is true), **then**
the result matches `eq_spec`. For integer types and `bool`, `vstd` defines `obeys_eq_spec()`
to be true, and proves that these types satisfy the `eq_spec`.  For other types, Verus
doesn't know whether `obeys_eq_spec()` is true or false, so it won't assume that the postcondition
holds.  This pattern lets `vstd` provide useful specifications for well-behaved types without making
unsound assumptions about all types.  If you want to use a trait like `Eq` for an external type,
you can use an [`assume_specification`](./reference-assume-specification.md)
to say that `obeys_eq_spec()` is true.

## Rules and restrictions

 * The `ExternalTraitSpecificationFor` associated type is required and must name the
   external trait.
 * The specification trait should not have a body for any method.
 * Generic parameters and associated types must match the external trait exactly.
 * When using `external_trait_extension`, the two names (`SpecTrait` and `SpecImplTrait`)
   become real trait names that can be used in bounds and `impl` blocks.

