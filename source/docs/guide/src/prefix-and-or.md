# Prefix and/or (`&&&` and `|||`)

For an introduction, see [Expressions and operators for specifications](operators.md).

### Syntax

```verus-grammar
V@[prefix_and_expr] ::= (&&&  V@[spec_expr])+
V@[prefix_or_expr]  ::= (|||  V@[spec_expr])+
```

Each operand is introduced by its operator as a prefix. `&&&` is the prefix conjunction
and `|||` is the prefix disjunction. Both bind looser than all other binary operators
(see [operator precedence](./spec-operator-precedence.md)).

### Typing

Each operand must have type `bool`. The expression returns `bool`.

### Semantics

`&&&` and `|||` are shorthand for `&&` and `||`, written in prefix form. A sequence of
`&&&`-prefixed operands is equivalent to the corresponding infix conjunction, and likewise
for `|||`:

```
&&& P &&& Q &&& R  ≡  P && Q && R
||| P ||| Q ||| R  ≡  P || Q || R
```

As all spec expressions are pure and effectless, there is no notion of short-circuiting.

The main motivation for these operators is readability: when writing a large conjunction
or disjunction (such as a precondition or an invariant), the leading-prefix style makes it
easy to add, remove, or reorder clauses without adjusting punctuation elsewhere.
