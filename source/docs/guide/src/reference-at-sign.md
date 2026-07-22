# The view function `@`

### Syntax

```verus-grammar
V@[view_expr] ::= V@[spec_expr] @
```

### Desugaring

The expression `expr@` desugars to the expression `expr.view()`, which is resolved as normal via
Rust's [method resolution](https://doc.rust-lang.org/reference/expressions/method-call-expr.html).
This usually, but not always, resolves to the `view` method [defined by the `View` trait](https://verus-lang.github.io/verus/verusdoc/vstd/view/trait.View.html).

### Examples

By convention, the `view()` function is spec function
for the abstraction of an exec-mode object.
See, for example:

 * [Using view to reason about `Vec`](./exec_lib.md)
 * [Defining a view function](./container_bst_first_draft.md#the-abstract-view)
