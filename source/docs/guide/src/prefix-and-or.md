# Prefix and/or (`&&&` and `|||`)

For an introduction, see [Expressions and operators for specifications](operators.md).

## Syntax

```verus-grammar
V@[prefix_and_expr] ::= (&&&  V@[spec_expr])+
V@[prefix_or_expr]  ::= (|||  V@[spec_expr])+
```

Each operand is introduced by its operator as a prefix. `&&&` is the prefix conjunction
and `|||` is the prefix disjunction. Both bind looser than all other binary operators
(see [operator precedence](./spec-operator-precedence.md)), making them convenient for
writing large conjunctions or disjunctions without parenthesization.
