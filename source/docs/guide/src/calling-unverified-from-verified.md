# Calling unverified code from verified code

Often we only verify part of a system, which means that we need
verified code to call unverified code. To do this, we need to make Verus
aware of the unverified code, and we need to tell Verus what it should
**assume without proof**.

## Specifications without proof

One way to apply an assumption to an unverified function is to use the `#[verifier::external_body]` attribute.
This tells Verus to process the _specification_ of a function, without verifying or processing its body.
Thus, it causes Verus to assume the specification without proof. Obviously, this should be used with care,
with wrong specifications can subvert Verus's guarantees!

```rust
#[verifier::external_body]
fn fib_impl(n: u64) -> (result: u64)
    requires
        fib(n as nat) <= u64::MAX
    ensures
        result == fib(n as nat),
{
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;
    while i < n {
        i = i + 1;
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}
```

This implementation is correct, but unproved. If the `external_body` attribute were removed,
Verus would attempt to verify the body and fail because of the lack of loop invariants.
(See [here](./invariants.md) for more about this particular example.)

## Applying specifications to _existing_ library functions

It's common that you want to apply a specification to an existing function, e.g., one defined
in some library crate, or even in the Rust standard library.

One way to do this is to write a "wrapper function" with `external_body` which calls the
library function. For example, let's suppose we want to call [`std::mem::swap`](https://doc.rust-lang.org/stable/std/mem/fn.swap.html). We could write this wrapper function:

```rust
#[verifier::external_body]
fn wrapper_swap<T>(a: &mut T, b: &mut T)
    ensures
        *a == *old(b),
        *b == *old(a),
{
    std::mem::swap(a, b);
}
```

However, this may be incovenient, because now you need to call `wrapper_swap` instead of
the more familiar `std::mem::swap`. If you want to apply the specification to
`std::mem::swap` itself, so that you can call it from verified code, you can
use the [`assume_specification` directive](./reference-assume-specification.md), which goes at the item level (like functions).

```rust
pub assume_specification<T>[ std::mem::swap::<T> ](a: &mut T, b: &mut T)
    ensures
        *a == *old(b),
        *b == *old(a);
```

Now you can call `std::mem::swap` from verified code.

(Note though, that vstd _already_ provides this specification for `std::mem::swap`. Verus doesn't allow duplicate specifications,
so it won't let you declare a second one. If you want to try out this example yourself, you'll need to run Verus with the `--no-vstd` flag, but this is not recommended for general usage.)

### Standard library specifications

In fact, vstd provides a wide range of specifications for the standard library using
this directive, so as long as you run Verus while importing vstd (as in normal usage), you will
automatically import these specifications, as documented
[here](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/struct.VstdSpecsForRustStdLib.html).

Of course, if vstd doesn't provide a specification for a stdlib function you'd like to use,
you can also add an `assume_specification` to your own crate.

## Making Verus aware of types

Sometimes, Verus will complain that it doesn't recognize a type; for this, you just need
to make Verus aware of it. For this, you can use the `#[verifier::external_type_specification]` attribute.

This will make Verus aware of the `SomeStruct`:

```rust
#[verifier::external_type_specification]
struct ExSomeStruct(SomeStruct);
```

It should have exactly this form, with the parentheses and semicolon. The `ExSomeStruct` name can be arbitrary; this is just an artificial type used for the directive and shouldn't be referenced
anywhere else.

This declaration makes Verus aware of the type `SomeStruct` and all its fields (and for an enum, all its variants). If you don't want Verus to be aware of the fields/variants, you can also mark it `#[verifier::external_body]`.

## Adding specifications for external traits

You can also add specifications to external traits using the `#[verifier::external_trait_specification]` attribute. This lets you add `requires` and `ensures` clauses to trait methods, and optionally define spec helper functions with `#[verifier::external_trait_extension]`.

For details and examples, see [External trait specifications](./external_trait_specifications.md).
