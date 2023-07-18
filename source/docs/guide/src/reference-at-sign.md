# The view function `@`

The expression `expr@` is a shorthand for `expr.view()`. The `view()` function is a Verus
convention for the abstraction of an exec-mode object, usually [defined by the `View` trait](https://verus-lang.github.io/verus/verusdoc/vstd/view/trait.View.html).
However, the expansion of the `@` syntax is purely syntactic, so it does not necessarily
correspond to the trait function.
