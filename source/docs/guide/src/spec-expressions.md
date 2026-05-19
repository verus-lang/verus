# Spec expressions

Many built-in operators are in spec mode, i.e., they can be used in
specification expressions. This section discusses those operators.

## Syntax

```verus-grammar
V@[spec_expr] ::= V@[fn_call_expr]
            | V@[and_expr]
            | V@[or_expr]
            | V@[not_expr]
            | V@[if_expr]
            | V@[if_let_expr]
            | V@[match_expr]
            | V@[spec_block_expr]
            | V@[as_expr]
            | V@[box_new_expr]
            | V@[ref_expr]
            | V@[deref_expr]
            | V@[chained_expr]
            | V@[implies_expr]
            | V@[explies_expr]
            | V@[iff_expr]
            | V@[arith_expr]
            | V@[bit_expr]
            | V@[equality_expr]
            | V@[ext_eq_expr]
            | V@[prefix_and_expr]
            | V@[prefix_or_expr]
            | V@[forall_expr]
            | V@[exists_expr]
            | V@[choose_expr]
            | V@[view_expr]
            | V@[spec_index_expr]
            | V@[decreases_to_expr]
            | ( V@[spec_expr] )
```
