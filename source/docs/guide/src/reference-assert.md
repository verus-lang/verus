# `assert`

### Syntax

```verus-grammar
V@[assert] ::= assert (V@[spec_expr]) ;
```

### Proof operation

Prove the given expression using the default solver, and then assume the predicate for
subsequence code.
