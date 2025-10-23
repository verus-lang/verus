# Verus attributes for executable code

To add verus proof and spec to executable codes without sacrificing readability,
`#[verus_spec]` attribute macro helps on it.

## When to use `#[verus_spec]` instead of `verus!` macro

The default way to write Verus code is by using the `verus!` macro. However,
embedding specifications and proofs directly through `verus!` in executable code
may not always be ideal for production settings. This is particularly true when
developers want to integrate verification into an existing Rust project and aim
to:

1. Minimize changes to executable code — avoid modifying function APIs to
   include tracked or ghost arguments, and preserve native Rust syntax for
   maintainability.
2. Adopt verification incrementally — apply Verus gradually to a large, existing
   codebase without requiring a full rewrite to function APIs.
3. Maintain readability — ensure the verified code remains clean and
   understandable for developers who are not familiar with Verus.
4. Optimize dependency management — use Verus components (builtin,
   builtin-macro, and vstd) in a modular way, allowing projects to define custom
   stub macros and control Verus dependencies via feature flags.

## Adding specifications to function 

Use `#[verus_spec(requires ... ensures ...)]` to attach a specification to a
function signature.

Here is an example:

```rust
{{#include ../../../../examples/guide/exec_attr.rs:verus_spec}}
```

## Adding verification hints

Use #[verus_verify(...)] to provide hints to verifier to mark function as
external, external_body, rlimit(xx), etc.

In additionally, dual mode (spec + exec) function is supported via
[`verus_verify(dual_spec)`](exec_to_spec.md)  to generate a spec function from
an executable function.

## Adding proofs inside function

With #[verus_spec(...)], we can introduce proofs directly inside executable
functions using proof macros.

When build the code without using verus, #[verus_spec(...)] will erase all proof
codes.

### Simple Proof Blocks

Use `proof!` to add proof block, equivalent to proof { ... } inside `verus!`
macro. Thus, the ghost/tracked variable defined inside `proof!` is local to its
proof block and cannot be used in other proof blocks.

### Ghost/Tracked Variables cross proof blocks

Use `proof_decl!` when you need use ghost or tracked variables cross different
proof blocks, which introduce proof block and declare function-scoped
ghost/tracked variables.

Here is the example:

```rust
{{#include ../../../../examples/guide/exec_attr.rs:proof}}
```

### Ghost/Tracked variables cross executable function

* `#[verus_spec(with ...)]`: Adds tracked or ghost variables as parameters or
  return values in an executable function.

   This generates two function versions: 
   * A verified version (with ghost/tracked parameters), used in verified code.
   * An unverified version (original signature), callable from unverified code.

* `proof_with!`
   Works in combination with `verus_spec` to pass tracked/ghost variables to a callee.
   
   When `proof_with!` precedes a function call, the verified version is used;
   otherwise, the unverified version is chosen. The unverified version includes
   a `requires false` precondition, ensuring that improper use of proof_with!
   will cause verification failure when called from a verified code.

Here is an example:

```rust
{{#include ../../../../examples/guide/exec_attr.rs:proof_with}}
```

### Mix the use of `#[verus_spec]` and `verus!`

A preferred way to use `#[verus_spec]` and `verus!` is to use `#[verus_spec]`
for all executable functions, and use `verus!` for spec/proof functions.

To be noted, the combination of `#[verus_spec(with ...)]` + `proof_with!`
currently has compatibility issues with executable function defined in `verus!`,
if ghost/tracked variable used cross functions. 

Specifically, `proof_with!` works with exec functions verified via
`#[verus_spec]`. Using `proof_with!` to pass ghost/tracked variable to an exec function
verified via `verus!` causes compilation error

```text
[E0425]: cannot find function `_VERUS_VERIFIED_xxx` in this scope.
```

This is because `verus!` always require a real changes in function signature and
has a single function definition, while `#[verus_spec]` expects a verified and
an unverified version of functions.

To use function verified by `verus!`, a work-around is to create a trusted
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


## More example and tests

```rust
{{#include ../../../../examples/syntax_attr.rs}}
```

```rust
{{#include ../../../../source/rust_verify_test/tests/syntax_attr.rs}}
```
