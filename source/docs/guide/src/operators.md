# Expressions and operators for specifications

To make specifications easier to read and write,
Verus supports syntactic sugar for various arithmetic and boolean operations in ghost code.
For example, you can write:

```
forall|i: int, j: int| 0 <= i <= j < len ==> f(i, j)
```

This is equivalent to:

```
forall|i: int, j: int| !(0 <= i && i <= j && j < len) || f(i, j)
```

# Chained inequalities

In ghost code, you can chain together multiple `<=`, `<`, `>=`, and `>` operations,
writing `0 <= i <= j < len` as a shorthand for `0 <= i && i <= j && j < len`, for example.

(If any of the expressions are complex expressions,
as in `0 <= f(x + 1, 3 * y) < n`,
for efficiency's sake,
Verus will automatically create a temporary variable for the complex expressions,
as in `{let tmp = f(x + 1, 3 * y); 0 <= tmp < n}`,
rather than duplicating the expressions.)

# Boolean operators

For boolean expressions `b1`, ..., `bn`,
Verus supports the following abbreviations:

| Expression                                                            | Meaning                                             | Name        |
|-----------------------------------------------------------------------|-----------------------------------------------------|-------------|
| b1 ==> b2                                                             | !b1 &#124;&#124; b2                                 | implies     |
| b1 <== b2                                                             | b1 &#124;&#124; !b2                                 | explies     |
| b1 <==> b2                                                            | b1 == b2                                            | equivalent  |
| &&& b1 &&& b2 ... &&& bn                                              | b1 && b2 && ... && bn                               | prefix-and  |
| &#124;&#124;&#124; b1 &#124;&#124;&#124; b2 ... &#124;&#124;&#124; bn | b1 &#124;&#124; b2 &#124;&#124; ... &#124;&#124; bn | prefix-or   |

These abbreviations have lower precedence than
[most other Rust expressions](https://doc.rust-lang.org/reference/expressions.html),
so that, for example, `a ==> b && c` means `a ==> (b && c)`:

| Operator                 | Associativity         |
|--------------------------|-----------------------|
| * / %                    | left                  |
| + -                      | left                  |
| << >>                    | left                  |
| &                        | left                  |
| ^                        | left                  |
| &#124;                   | left                  |
| === !== == != <= < >= >  | requires parentheses  |
| &&                       | left                  |
| &#124;&#124;             | left                  |
| ==>                      | right                 |
| <==                      | left                  |
| <==>                     | requires parentheses  |
| ..                       | left                  |
| =                        | right                 |
| closures, forall, exists | right                 |
| &&&                      | left                  |
| &#124;&#124;&#124;       | left                  |

# The `is` operator, and the "arrow" field access

If you define an enum,

```rust
enum ThisOrThat {
    This(nat),
    That { v: int },
}
```

you can then use (in specification code) the syntax `t is This` or `t is That`
which will be true if `t` is a value of the relevant enum variant.

If, in addition, all the fields have distinct names, like in the example above
you can then access the fields with `t->v` or `t->0` (for positional fields note
that these are supported if only one variant has "tuple like" fields).

# `matches` with `&&&`, `==>`, and `&&`

For more complex cases, and where you need an enum where multiple variants have
fields of the same name, you can use the `t matches That { v: a }` syntax, which
will result in a boolean representing whether `t` matches the provided pattern.
You can also follow it up with `==>` and `&&` and subsequent expressions (that bind at least as tightly)
will have access to the bound variables in the parttern (`a` in this example).

For example, for that enum, you can say;

```rust
proof fn uses_arrow_matches_1(t: ThisOrThat)
    requires
        t is That ==> t->v == 3,
        t is This ==> t->0 == 4,
{
    assert(t matches ThisOrThat::This(k) ==> k == 4);
    assert(t matches ThisOrThat::That { v } ==> v == 3);
}
```

The "t matches `pattern`" syntax is also valid as an expression of a `&&&` chain, e.g.

```rust
proof fn test1(t: ThisOrThat)
    requires ({
        &&& t matches ThisOrThat::That { v: a }
        &&& a > 3
        &&& a < 5
    })
{
    // ...
}
```