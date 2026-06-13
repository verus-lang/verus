# Traits

Verus supports writing specifications for trait methods, including `requires` and
`ensures` clauses. Specifications on a trait method serve as a *contract* that all
implementations must satisfy, and that callers can rely on when they call the method
through a trait bound.

For traits defined in external crates (e.g., from the Rust standard library), see
[External trait specifications](./external_trait_specifications.md).

## Trait method specifications

Trait methods can have `requires` and `ensures` clauses just like ordinary functions:

```rust
{{#include ../../../../examples/guide/traits.rs:basic_trait}}
```

Any type implementing `Compressor` must provide a `compress` method whose body
satisfies `output <= input`.

## Extending specifications in implementations

An implementation automatically inherits all `requires` and `ensures` clauses from the
trait declaration.  Additionally:

 * An `impl` **can** add stronger `ensures` clauses.
 * An `impl` **cannot** add new `requires` clauses — that would be unsound, because a
   caller using the trait bound `C: Compressor` has no obligation to satisfy
   requirements that the trait doesn't mention.

```rust
{{#include ../../../../examples/guide/traits.rs:impl_extends}}
```

`HalfCompressor::compress` inherits `ensures output <= input` from the trait. 
Verus verifies that the function's body satisfies both the inherited postcondition
and the additional postcondition added by the implementation (`ensures output == input / 2`).

A trait function can also include both `requires` and `ensures`:

```rust
{{#include ../../../../examples/guide/traits.rs:requires_ensures}}
```

```rust
{{#include ../../../../examples/guide/traits.rs:requires_ensures_impl}}
```

## Generic vs. concrete dispatch

When Verus can statically determine the concrete type of a trait method call, it uses
the possibly-stronger specification from the `impl`.  When the call is through a generic
type parameter, Verus only knows the trait-level specification.

```rust
{{#include ../../../../examples/guide/traits.rs:dispatch}}
```

## Spec and proof functions

A trait may also contain `spec` and `proof` function declarations. 
For example, the trait below requires implementations to provide 
a distance metric (`dist`) as a specification function and then to prove that
their `distance` function actually computes that metric.
Moreover, the implementation must also prove (in its body for `valid_distance_metric`)
that `dist` is a reasonable metric.

```rust
{{#include ../../../../examples/guide/traits.rs:spec_trait}}
```

Here's an example of an implementation of our `Distance` trait:
```rust
{{#include ../../../../examples/guide/traits.rs:spec_trait_impl}}
```
In this case, Verus can automatically prove all of the postconditions
for `valid_distance_metric`, but a more complex distance metric might
need additional proof annotations.

Note that it's not necessary to repeat the requires/ensures that
the implementation inherits from the trait definition.


## The `View` trait

The most commonly used trait in `vstd` is `View`.  It allows users to give
executable types a mathematical abstraction (`type V`) accessed via the `view`
function.  Since this is such a commonly invoked function, Verus provides the
[`@` operator](reference-at-sign.md) as a shortcut, so that you can write `x@`
instead of `x.view()`.

```rust
pub trait View {
    type V;
    spec fn view(&self) -> Self::V;
}
```

`vstd` provides `View` implementations for common types:
- `Vec<T>` → `Seq<T>`
- `HashMap<K, V>` → `Map<K, V>`
- `HashSet<K>` → `Set<K>`
- Primitive types (`u64`, `bool`, etc.) → themselves

To implement `View` for a custom type, choose an appropriate abstraction and
then define `type V` and `spec fn view`:

```rust
{{#include ../../../../examples/guide/traits.rs:view_impl}}
```

Because `Stack`'s `data` is a private field, `view` is `closed` — callers cannot see its
definition, but they can still reason about the effect each function has on that view,
as illsutrated by the postconditions on `push` and `is_empty`.  If you want
callers to unfold `@` to its definition (e.g., for a `pub` type with a `pub`
field), use `open spec fn view` instead.

`vstd` also provides `DeepView`, which recursively applies the view abstraction
to nested elements.  Most code only needs `View`.

## `default_ensures`: specifications for default method implementations

In Rust, a trait method can provide a *default implementation* — a body that
implementations inherit if they do not override the method.  This creates a subtle
specification problem: the trait-level `ensures` clause must be weak enough to allow
any valid override, but the default body may satisfy a *stronger* postcondition.

`default_ensures` solves this by separating these two concerns:

```rust
{{#include ../../../../examples/guide/traits.rs:default_ensures}}
```

Here the **trait-level `ensures`** (`output <= input`) is what any implementation must
satisfy.  The **`default_ensures`** (`output == input / 2`) is an additional guarantee
that holds *only* when a type uses the default implementation without overriding it.

The rules:

 * `default_ensures` is only allowed on a trait method that has a default body in the
   trait declaration.
 * `default_ensures` is checked against the default body just like a normal `ensures`.
 * Callers that statically know the type inherits the default learn both `ensures` and
   `default_ensures`; callers using a generic bound `T: Trait` learn only the `ensures`.

```rust
{{#include ../../../../examples/guide/traits.rs:default_ensures_impls}}
```

```rust
{{#include ../../../../examples/guide/traits.rs:default_ensures_callers}}
```

When writing your own trait, consider using `default_ensures` on functions
where a sensible default makes a stronger promise that custom implementations
are not required to match.

## Common `vstd` trait specifications

`vstd` provides specifications for many standard library traits. A few worth knowing:

 * **`PartialEq` / `Eq`** — `vstd` wraps these with an `obeys_eq_spec()` guard so that
   only types that opt in are assumed to satisfy the functional equality contract.
   See [External trait specifications](./external_trait_specifications.md) for the
   `obeys_*` pattern.
 * **`Iterator`** — `vstd` provides `IteratorSpecImpl` (not `Iterator` directly) for
   writing specs on custom iterators.  See [Iterator Specifications](./iterator-specs.md).
 * **`PartialOrd` / `Ord`** — similar to `PartialEq`, with `obeys_ord_spec()` guards.

## External trait specifications

For adding specifications to traits from external crates (including `std`), see
[External trait specifications](./external_trait_specifications.md).
