# `reveal_strlit`

### Syntax

```verus-grammar
V@[reveal_strlit_stmt] ::= reveal_strlit ( R@[string_literal] ) ;
```

### Proof operation

This reveals the contents of the string literal to the prover, including the length and
the sequence of characters that compose the string.
Otherwise, the string literal is treated as opaque
data to avoid polluting the prover's context with too much information.

### Example

```rust
fn test() {
    let s = "abc";
    proof { reveal_strlit("abc"); }
    assert(s@[0] == 'a');
}
```
