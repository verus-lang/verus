# Rust subset

Much of the spec language looks like a subset of the Rust language, though
there are some subtle differences.

### Function calls

**Syntax:**

```verus-grammar
V@[fn_call_expr] ::= R@[path] ( V@[spec_expr]* )
```

Only pure function calls are allowed (i.e., calls to other `spec` functions or
functions marked with the `when_used_as_spec` directive).

### Let-assignment

**Syntax:**

```verus-grammar
V@[spec_block_expr] ::= { V@[spec_let_stmt]* V@[spec_expr] }
V@[spec_let_stmt]   ::= let R@[pattern] = V@[spec_expr];
```

Spec expressions support `let`-bindings, but not `let mut`-bindings.

### if / if let / match statements

**Syntax:**

```verus-grammar
V@[if_expr]     ::= if V@[spec_expr] { V@[spec_expr] } else { V@[spec_expr] }
V@[if_let_expr] ::= if let R@[pattern] = V@[spec_expr] { V@[spec_expr] } else { V@[spec_expr] }
V@[match_expr]  ::= match R@[expr] { R@[match_arms] }
```

These work as normal.

### `&&` and `||`

**Syntax:**

```verus-grammar
V@[and_expr] ::= V@[spec_expr] && V@[spec_expr]
V@[or_expr]  ::= V@[spec_expr] || V@[spec_expr]
V@[not_expr] ::= ! V@[spec_expr]
```

These work as normal, though as all spec expressions are pure and effectless,
there is no notion of "short-circuiting".

### Equality (==)

**Syntax:**

```verus-grammar
V@[equality_expr] ::= V@[spec_expr] == V@[spec_expr]
                | V@[spec_expr] != V@[spec_expr]
```

This is not the same thing as `==` in exec-mode; see [more on `==`](./spec-equality.md).

### Arithmetic

**Syntax:**

```verus-grammar
V@[arith_expr] ::= V@[spec_expr] \+ V@[spec_expr]
             | V@[spec_expr] - V@[spec_expr]
             | - V@[spec_expr]
             | V@[spec_expr] \* V@[spec_expr]
             | V@[spec_expr] / V@[spec_expr]
             | V@[spec_expr] % V@[spec_expr]
```

Arithmetic works a little differently in order to operate with Verus's `int`
and `nat` types. See [more on arithmetic](./spec-arithmetic.md).

### References (&T)

**Syntax:**

```verus-grammar
V@[ref_expr]   ::= & V@[spec_expr]
V@[deref_expr] ::= \* V@[spec_expr]
```

Verus attempts to ignore `Box` and references as much as possible in spec mode.
However, you still needs to satisfy the Rust type-checker, so you may need to insert
references (`&`) or dereferences (`*`) to satisfy the checker. Verus will ignore these
operations however.

### Box

**Syntax:**

```verus-grammar
V@[box_new_expr] ::= Box::new( V@[spec_expr] )
```

Verus special-cases `Box<T>` along with box operations like `Box::new(x)` or `*box`
so they may be used in spec mode. Like with references, these operations are ignored,
however they are often useful. For example, to create a recursive type you need to satisfy
Rust's sanity checks, which often involves using a `Box`.
