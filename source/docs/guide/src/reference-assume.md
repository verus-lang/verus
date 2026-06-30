# `assume`

> [!CAUTION]
> Since the `assume` statement is unchecked, it can be used to subvert Verus's guarantees.
> In particular, successful "verification" by Verus provides **no guarantees** on the program
> if it includes any `assume` statements, unless those `assume` statements could in principle
> be replaced by a successful `assert` statement.
>
> The `assume` statement is most useful during _intermediate_ stages of development,
> e.g., within an [assert/assume-driven proof-development process](./assert_assume.md).

> [!TIP]
> The `--no-cheating` flag can be used to disallow `assume` statements.

### Syntax

```verus-grammar
V@[assume] ::= assume (V@[spec_expr]) ;
```

### Proof operation

Assume the given predicate without proof.
