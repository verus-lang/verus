# Unions

Verus supports Rust unions.

Internally, Verus represents unions a lot like enums. However, Rust syntax for accessing
unions is different than enums. In Rust, a field of a union is accessed with field access:
`u.x`. Verus allows this operation in exec-mode, and Verus always checks it is well-formed,
i.e., it checks that `u` is the correct "variant".

In spec-mode, you can use the built-in spec operators `is_variant` and `get_union_field`
to reason about a union. Both operators refer to the field name via _string literals_.

 * `is_variant(u, "field_name")` returns true if `u` is in the `"field_name"` variant.
 * `get_union_field::<U, T>(u, "field_name")` returns a value of type `T`, where
    `T` is the type of `"field_name"`. (Verus will error if `T` does not match between
    the union and the generic parameter `T` of the operator.)

### Example

```rust
union U {
    x: u8,
    y: bool,
}

fn union_example() {
    let u = U { x: 3 };

    assert(is_variant(u, "x"));
    assert(get_union_field::<U, u8>(u, "x") == 3); 

    unsafe {
        let j = u.x; // this operation is well-formed
        assert(j == 3); 

        let j = u.y; // Verus rejects this operation
    }   
}   
```

### Note on `unsafe`

The `unsafe` keyword is needed to satisfy Rust, because Rust treats union field access
as an unsafe operation. However, the operation _is_ safe in Verus because Verus is able to 
check its precondition. See [more on how Verus handles memory safety](./memory-safety.md).
