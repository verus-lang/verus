# Spec expressions

Many built-in operators are in spec mode, i.e., they can be used in
specification expressions. This section discusses those operators.

## Syntax

```verus-grammar
V@[spec_expr] ::= V@[arith_expr]
            | V@[bit_expr]
            | V@[equality_expr]
            | V@[ext_eq_expr]
            | V@[implication_expr]
            | V@[prefix_and_expr]
            | V@[prefix_or_expr]
            | V@[forall_expr]
            | V@[exists_expr]
            | V@[choose_expr]
            | V@[view_expr]
            | V@[spec_index_expr]
            | V@[decreases_to_expr]
```
