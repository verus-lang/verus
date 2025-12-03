# Verus attributes for executable code

The `#[verus_spec]` attribute macro can help add Verus specifications and proofs
to existing executable code without sacrificing readability.

## When to use `#[verus_spec]` instead of the `verus!` macro

The default way to write Verus code is by using the `verus!` macro. However,
using `verus!` to embed specifications and proofs directly in executable code
may not always be ideal for production settings. This is particularly true when
developers want to integrate verification into an existing Rust project and aim
to:

1. Minimize changes to executable code — avoid modifying function APIs to
   include tracked or ghost arguments, and preserve native Rust syntax for
   maintainability.
2. Adopt verification incrementally — apply Verus gradually to a large, existing
   codebase without requiring a full rewrite of the function APIs.
3. Maintain readability — ensure the verified code remains clean and
   understandable for developers who are not familiar with Verus or
   want to ignore verification-related annotations.
4. Optimize dependency management — use Verus components (`verus_builtin`,
   `verus_builtin_macros`, and `vstd`) in a modular way, allowing projects to
   define custom stub macros and control Verus dependencies via feature flags.

## Adding specifications to a function 

Use `#[verus_spec(requires ... ensures ...)]` to attach a specification to a
function signature.

Here is an example:

```rust
{{#include ../../../../examples/guide/exec_attr.rs:verus_spec}}
```

## Adding verification hints

Use `#[verus_verify(...)]` to provide hints to the verifier to mark a function
as `external`, `external_body`, `spinoff_prover`, or specify a different
resource limit via `rlimit(amount)`.

In addition, you can create a dual mode (spec + exec) function the via
[`verus_verify(dual_spec)`](exec_to_spec.md) attribute, which will attempt to
generate a spec function from an executable function.

## Adding proofs inside function

When a function has the `#[verus_spec(...)]` attribute, we can introduce 
proofs directly inside executable functions using the proof macros described below.

When Rust builds the code (without using Verus), the `#[verus_spec(...)]` attribute will
ensure all proof code is erased.

### Simple proof blocks

Use `proof!` to add a proof block; this is equivalent to using `proof { ... }`
inside the `verus!` macro.  This implies that ghost/tracked variables defined inside
of `proof!` are local to that proof block and cannot be used in other proof blocks.

### Ghost/Tracked variables across proof blocks

Use `proof_decl!` when you need to use ghost or tracked variables across different
proof blocks.  It will allow you to introduce a proof block and declare function-scoped
ghost/tracked variables, as shown in this example:
```rust
{{#include ../../../../examples/guide/exec_attr.rs:proof}}
```

### Adding ghost/tracked variables to executable function calls

* `#[verus_spec(with ...)]`: Adds tracked or ghost variables as parameters or
  return values in an executable function.

   This generates two versions of the original function: 
   * A verified version (with ghost/tracked parameters), used in verified code.
   * An unverified version (with the original signature), callable from unverified code.

* `proof_with!`
   Works in combination with `verus_spec` to pass tracked/ghost variables to a callee.
   
   When `proof_with!` precedes a function call, the verified version is used;
   otherwise, the unverified version is chosen. The unverified version includes
   a `requires false` precondition, ensuring that improper use of `proof_with!`
   will cause a verification failure when called from verified code.

Here is an example:

```rust
{{#include ../../../../examples/guide/exec_attr.rs:proof_with}}
```

### Using a mix of `#[verus_spec]` and `verus!`

The preferred way to use `#[verus_spec]` and `verus!` is to use `#[verus_spec]`
for all executable functions, and use `verus!` for spec/proof functions.

NOTE: The combination of `#[verus_spec(with ...)]` + `proof_with!`
currently has compatibility issues with executable functions defined in `verus!`
if the functions involved receive or return ghost/tracked variables. 

Specifically, `proof_with!` works with exec functions verified via
`#[verus_spec]`. Using `proof_with!` to pass ghost/tracked variables to an exec
function verified via `verus!` will result in this error:

```text
[E0425]: cannot find function `_VERUS_VERIFIED_xxx` in this scope.
```

This is because `verus!` always requires a real change to the function's
signature and has a single function definition, while `#[verus_spec]` expects a
verified and an unverified version of the function.

To use a function verified by `verus!`, a workaround is to create a trusted
wrapper function and then use it.

```
#[verus_verify(external_body)]
#[verus_spec(v =>
   with Tracked(perm): Tracked<&mut PointsTo<T>>
   requires
        old(perm).ptr() == ptr,
        old(perm).is_init(),
    ensures
        perm.ptr() == ptr,
        perm.is_uninit(),
        v == old(perm).value(),
)]
fn ptr_mut_read<'a, T>(ptr: *const T)  -> T
{
   vstd::raw_ptr::ptr_mut_read(ptr, Tracked::assume_new())
}
```


## More examples and tests

```rust
{{#include ../../../../examples/syntax_attr.rs}}
```

```rust
{{#include ../../../../source/rust_verify_test/tests/syntax_attr.rs}}
```
