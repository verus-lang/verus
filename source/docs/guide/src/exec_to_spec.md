# Automatically producing a spec function for executable code 

When verifying code in Verus, it’s often necessary to write spec functions that
have the exact same implementation as their corresponding executable functions.
This situation is common when the executable functions are small and purely
computational.

`#[verus_verify(dual_spec)]` simplies the process to write spec function for an
existing executable function. When applied to an executable function, it
automatically produces a corresponding spec function by:

1. Removing ghost variables and proof blocks from the executable function.
2. Generating a spec function with identical logic. By default, the spec
   function is given an internal name like _VERUS_SPEC_xxx. You can also specify
   a custom name using `#[verus_verify(dual_spec($custom_name))]`.
3. Applying the attribute `#[when_used_as_spec]` to the executable function.
   Thus, the actual spec function name does not matter a lot since the
   `when_used_as_spec` attribute allows you to use the executable function’s
   name directly as a spec function in proofs.

Here is an example:

```rust
{{#include ../../../../examples/guide/exec_attr.rs:dual_spec}}
```

## Limitations

`#[verus_verify(dual_spec)]` currently does not fully support verified
executable functions via `verus!` macro. This is because `verus_verify` macro
expects to parse an exec function in native Rust syntax, instead of in `verus!`
syntax. Thus, `#[verus_verify(dual_spec)]` should work with `#[verus_spec(...)]`
outside `verus!`.

`dual_spec` tries to generate spec from exec function, but it may not be able to
generate a valid spec function if the exec function uses features that are not
supported by spec function.

For example,

```
fn f(x: &mut u32, y: u32) -> u32 {
    *x = *x + y;
    *x
}
```

In such case, you should see following error message:

```
The verifier does not yet support the following Rust feature
```


## Related

The `dual_spec` attribute creates a spec function for executable code, which
might not cover your use case.  For example, you may want to go from [spec to
exec code](exec_spec.html), or use the [`when_used_as_spec` attribute](reference-attributes.html).
