# Advanced triggers

The general mechanics of triggers and their usage are explained in an earlier chapter. Trigger
annotations for `forall` are explained in [forall and triggers](forall.md) and in more detail in
[Multiple variables, multiple triggers, matching loops](multitriggers.md). Trigger annotations for
`exists` are explained in [exists and choose](exists.md).

This chapter will cover triggering on arithmetic and mixed (arithmetic and normal) expressions.

## Triggering on arithmetic expressions

Verus supports placing triggers on arithmetic expressions that contain any of the operators `+`,
`-`, `*` or `/`. For example, the following trigger selection is valid:

```rust
fn lemma_add_even()
    ensures forall|x:int, y:int|
        x % 2 == 0 && y % 2 == 0 ==> #[trigger] ((x + y) % 2) == 0
{}
```

However, arithmetic triggers should be used judiciously. The pervasiveness of arithmetic operators
increases the risk of arithmetic triggers causing many quantifier instantiations and thereby
degrading verification performance.

Instead, it is often a good idea to define a function that encapsulate the arithmetic expression. So
we might rewrite the previous example to the following:

```rust
spec fn is_even(i: int) -> bool {
    i % 2 == 0
}

fn lemma_add_even2()
    ensures forall|x:int, y:int|
        #[trigger] is_even(x) && #[trigger] is_even(y) ==> is_even(x + y)
{}
```

However, note that in this case, avoiding arithmetic triggers forces us to choose the less specific
trigger with the two expressions `is_even(x)`, `is_even(y)`. The next section on mixed triggers
shows that in this particular lemma we can also use the more specific trigger `is_even(x + y)`,
which combines a function call with arithmetic.

## Mixing arithmetic and normal triggers

In many cases, Verus allows mixing arithmetic and "normal" triggers. Thus, the previous example can
also use the following trigger:

```rust
fn lemma_add_even3()
    ensures forall|x:int, y:int|
        is_even(x) && is_even(y) ==> #[trigger] is_even(x + y)
{}
```

However, for technical reasons, mixing arithmetic and normal trigger expressions isn't always
possible. Mixing is allowed if and only if every quantified variable in a trigger appears only in
arithmetic positions or only in non-arithmetic positions.

For example, the trigger in `lemma_add_even3` is the singleton set `{ is_even(x + y) }`. Both `x`
and `y` appear only in an arithmetic position, i.e. as part of `x + y`. For `lemma_add_even2`, the
trigger is `{is_even(x), is_even(y)}`, where `x` and `y` appear only as arguments to a function
call, i.e. in a non-arithmetic position.

Even the triggers in the following lemma are valid. `x` appears only in an arithmetic position while
`y` appears only in a non-arithmetic one.

```rust
spec fn is_odd(i: int) -> bool {
    i % 2 == 0
}

fn lemma_add_even4()
    ensures forall|x:int, y:int|
        is_odd(x + y) ==> #[trigger] is_odd(x) || #[trigger] is_even(y + 1)
{}
```

However, consider the following lemma:

```rust
fn lemma_add_odd()
    ensures forall|x:int|
        is_odd(x) ==> is_even(x + 1)
{}
```

In this case, we could choose the trigger `is_odd(x)` or `is_even(x + 1)` but not
the trigger `{ is_odd(x), is_even(x + 1) }`:

```rust
fn lemma_add_odd_bad()
    ensures forall|x:int|
        #[trigger] is_odd(x) ==> #[trigger] is_even(x + 1)
{}
```

This lemma results in an error:

```
error: variable `x` in trigger cannot appear in both arithmetic and non-arithmetic positions
  --> test.rs:40:27
   |
   |         #[trigger] is_odd(x) ==> #[trigger] is_even(x + 1)
   |                           ^
```
