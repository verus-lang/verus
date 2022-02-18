
# Datatype attributes

These are attributes that can be applied to `struct`s and `enum`s.

## Encoding abstractly

`#[verifier(abstract)]` marks `struct`s and `enum`s that should always be encoded as an uninterpreted sort where the fields are not visibile to the verifier. This is useful to, e.g., define a datatype whose properties are defined exclusively by functions and does not have any fields:

```rust
#[verifier(abstract)] #[spec]
struct Properties {}
```

# Function attributes

## Controlling whether a `#[spec]` function is (un)interpreted outside its defining module

A `pub` function is uninterpreted outside its defining module by default. One can use the `#[verifier(publish)]` attribute to make its body visible to other modules.

## Controlling whether a `#[spec]` function is opaque

By default, the verifier can access the definition of the body of `#[spec]` functions. One may use the `#[verifier(opaque)]` to hide the body everywhere. This is typically useful to hide quantifiers that cause triggering issues. An `opaque` function can be revealed with `reveal(function)`. The `#[verifier(opaque_outside_module)]` hides the body only in other modules, while retaining the default behaviour within the defining module.
