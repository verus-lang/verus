# Specification code, proof code, executable code

Verus classifies code into three *modes*: `spec`, `proof`, and `exec`,
where:
- `spec` code describes properties about programs
- `proof` code proves that programs satisfy properties
- `exec` code is ordinary Rust code that can be compiled and run

Both `spec` code and `proof` code are forms of ghost code,
so we can organize the three modes in a hierarchy:
- code
    - ghost code
        - `spec` code
        - `proof` code
    - `exec` code

Every function in Verus is either a `spec` function, a `proof` function, or an `exec` function:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:fun_modes}}
```

`exec` is the default function annotation, so it is usually omitted:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:fun_modes2}}
```

The rest of this chapter will discuss these three modes in more detail.
As you read, you can keep in mind the following relationships between
the three code modes and three function modes:

|                          | spec function   | proof function   | exec function    |
|--------------------------|-----------------|------------------|------------------|
| can contain `spec` code  | yes             | yes              | yes              |
| can contain `proof` code | no              | yes              | yes              |
| can contain `exec` code  | no              | no               | yes              |

|                             | spec code      | proof code       | exec code        |
|-----------------------------|----------------|------------------|------------------|
| can call `spec` functions   | yes            | yes              | yes              |
| can call `proof` functions  | no             | yes              | yes              |
| can call `exec` functions   | no             | no               | yes              |
