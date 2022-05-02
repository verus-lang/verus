# Notes and related work on ghost types

These notes are meant to explore some of the design space associated with "ghost types and blocks".
(See [Initiative: Ghost types and blocks #161](https://github.com/rust-lang/lang-team/issues/161) and
the [discussion](https://rust-lang.zulipchat.com/#narrow/stream/243200-t-lang.2Fmajor-changes/topic/Initiative.3A.20Ghost.20types.20and.20blocks.20lang-team.23161).)
In particular, I want to look at various ideas related to "ghost types".
I'll assume that "ghost blocks" have been dealt with somewhere else.

## Some background on ghost variables in Dafny, F*, and Verus

For inspiration, I'll look at examples from three verification languages that I'm familiar with:
Dafny, F*, and the current version of Verus.
(Of course, there are many more languages out there to learn from.)

In order to verify executable code,
we'll need specifications to say what the executable code is supposed to do,
and we'll often need explicit proofs to prove that the executable code meets the specifications.
Verus currently uses attributes `#[spec]`, `#[proof]`, and `#[exec]` to mark
functions that define specifications, proofs, and executable code:

```
#[spec]
fn is_even(x: u8) -> bool {
    x % 2 == 0
}

#[proof]
fn sum_odd_is_even(x: u8, y: u8) {
    requires(x as int + (y as int) < 256 && !is_even(x) && !is_even(y));
    ensures(is_even(x + y));

    // SMT solver proves this automatically
}

#[exec]
fn add_one_and_print(a: u8) {
    requires(a < 255 && !is_even(a));

    let b = a + 1;
    sum_odd_is_even(a, 1);
    assert(is_even(b));
    print_u8(b);
}
```

The code above would look similar in Dafny,
but with the keywords `function`, `lemma`, and `method`
marking specification code, proof code, and executable code:

```
function is_even(x: u8): bool {
    x % 2 == 0
}

lemma sum_odd_is_even(x: u8, y: u8)
    requires x as int + y as int < 256 && !is_even(x) && !is_even(y)
    ensures is_even(x + y)
{
    // SMT solver proves this automatically
}

method add_one_and_print(a: u8)
    requires a < 255 && !is_even(a)
{
    var b := a + 1;
    sum_odd_is_even(a, 1);
    assert is_even(b);
    print(b);
}
```

F* uses a more general system of effects rather than attributes or keywords
to distinguish specifications, proofs, and executable code
(here, `GTot`, `Lemma`, and `ST` are effects for specifications,
proofs, and executable code):

```
let is_even (x:u8) : GTot bool =
    x % 2 = 0

let sum_odd_is_even (x:u8) (y:u8) : Lemma
    (requires x + y < 256 && not (is_even x) && not (is_even y))
    (ensures is_even (x + y))
    =
    // SMT solver proves this automatically
    ()

let add_one_and_print (a:u8) : ST unit
    (requires fun _ -> a < 255 && not (is_even a))
    (ensures fun _ _ _ -> true)
    =
    let b = a + 1 in
    sum_odd_is_even a 1;
    assert (is_even b);
    print_u8 b
```

Proofs typically contains specifications inside them.
For example, `sum_odd_is_even`'s requirement that `!is_even(x)` is a specification.
Executable code may contain both specifications and proofs.
For example, `add_one_and_print` proves that `a + 1` is even by calling
`sum_odd_is_even(a, 1)` (although in Verus, Dafny, and F*, this proof is superfluous,
since the SMT solver can figure out that `a + 1` is even without an explicit proof).

In the specifications and proofs shown above,
the variables `x` and `y` that are ghost:
they do not need to be compiled and they have no runtime representation.
In fact, specifications and proofs are entirely ghost,
so all variables in them are ghost.
However, executable code may also occasionally use ghost variables.
For example, a program might save a ghost copy of a runtime variable
to use in a proof later on:

```
#[exec]
fn do_something_to_v(v: &mut Vec<u8>) {
    ...
    while ... {
        #[spec] let copy_of_v = *v; // save a ghost copy of v

        ... mutate v ...

        some_lemma_about(copy_of_v, *v);
        assert(some_relation_between(copy_of_v, *v));
    }
    ...
}
```

In the code above, `copy_of_v` is ghost: it is not compiled and does not exist at runtime.
Indeed, attempting to compile and run `copy_of_v` would be illegal, as it tries to make a copy of `*v`,
which would violate Rust's borrowing rules.
In a specification or proof, though, such copying is fine (and commonplace).

## Distinguishing ghost variables and executable variables

Since ghost variables like `copy_of_v` are compiled differently from executable variables like `v`,
we need some way to distinguish them.
Dafny, F*, and Verus use various mechanisms for this.

### Modes

Both Dafny and Verus make ghostness a property of variables, independent of types.
In Dafny, you can explicitly annotate a variable as ghost:

```
ghost var copy_of_v: Vec<u8> := v;
```

To avoid confusion with a variable's type, I'll refer to "ghost" as being the "mode" of a variable.
Dafny has two modes for variables: ghost and the default mode (executable).
In proofs and specifications (lemmas and functions), variables are always ghost.

Verus has three modes for variables: spec, proof, and exec.
The spec and proof modes are both forms of ghost.
A key difference is that spec variables are always duplicable (`Copy`),
while proof variables are not necessarily duplicable.
Most proofs manipulate spec variables and freely duplicate these variables,
but proof variables are also sometimes useful for expressing separation-logic-like properties.

### Effects

F* has a sophisticated effect system that can track whether an expression depends
on ghost data.
If an expression does depend on ghost data, then the expression must also be ghost.
Unlike the modes in Dafny and Verus, this does not track ghostness of each variable
individually.
This can sometimes result in false alarms, as in the following code:

```
    let b = a + 1 in
    let dummy = is_even b in
    sum_odd_is_even a 1;
    assert (is_even b);
    print_u8 b
```
Here, `dummy` is ghost, so F* pessimistically expects everything that follows the declaration
of `dummy` to be ghost as well, causing the effect checking of `print_u8 b` to fail.

### Types

For more flexibility, F* also supports a second mechanism for distinguishing ghost and executable
values, based on types.
F* has a type `erased t` that wraps a ghost value inside an executable value,
so that subsequent effect checking succeeds:

```
    let b = a + 1 in
    let dummy: erased bool = Ghost.hide (is_even b) in
    sum_odd_is_even a 1;
    assert (is_even b);
    print_u8 b
```

Most of the time, though, `erased t` isn't needed, as effect checking takes care of managing ghostness.

Verus also has types `Spec<t>` and `Proof<t>` that can wrap ghost values
inside exec values.
As with F*'s `erased t`, most of the time `Spec<t>` and `Proof<t>` aren't needed,
as mode checking takes care of managing ghostness,
but they can be useful in particular situations such as storing a spec or proof value inside
an exec tuple (since tuple components in Verus lack mode annotations).

## Using ghost types (`ghost t` or `Ghost<t>`)

The initiative [Initiative: Ghost types and blocks #161](https://github.com/rust-lang/lang-team/issues/161)
briefly discusses introducing "ghost types", written `ghost t` or `Ghost<t>`
(I'll write `Ghost<t>` here), but doesn't yet go into much detail.
These notes will attempt to explore in more detail
what a Rust-based system with something like `Ghost<t>` might look like,
and how would verification languages could use it.

There needs to be a way to convert `t` to `Ghost<t>` and vice-versa
(the initiative, for example, refers to a `raise` operation to convert `Ghost<t>` to `t`).
A key restriction is that executable code cannot extract an executable `t` value from
a `Ghost<t>` value -- any coercion from `Ghost<t>` to `t` would only be legal inside
ghost code (e.g. inside proofs or specifications).

### `Ghost<t>` in ghost code (or not)

Notice that the distinction between `Ghost<t>` and `t` is important in executable code,
but not in specifications and proofs, where everything is always ghost.
Therefore, I believe we can avoid many headaches by not using `Ghost<t>` for variables
declared inside specifications and proofs.
In other words, instead of writing:

```
fn is_even(x: Ghost<u8>) -> Ghost<bool> {
    ghost {
        raise(x) % 2 == 0
    }
}
```

we could more easily declare an entire function ghost,
automatically making all aspects of the function ghost
and rendering `Ghost<t>` unnecessary inside the ghost function:

```
ghost function is_even(x: u8): bool {
    x % 2 == 0
}
```

Here, there's no reason to `raise` the variable `x` from `Ghost<u8>` to `u8`,
because `x` already has type `u8`, not `Ghost<u8>`.
Furthermore, in most interactions between executable code and specification/proof code,
executable values passed from executable code to specification functions and to proof functions
will have their original executable types `t` (e.g. `u8`) rather then `Ghost<t>`,
and will therefore need no conversion.
Consider the example from earlier:

```
#[spec]
fn is_even(x: u8) -> bool {
    x % 2 == 0
}

#[proof]
fn sum_odd_is_even(x: u8, y: u8) {
    requires(x as int + y as int < 256 && !is_even(x) && !is_even(y));
    ensures(is_even(x + y));

    // SMT solver proves this automatically
}

#[exec]
fn add_one_and_print(a: u8) {
    requires(a < 255 && !is_even(a));

    let b = a + 1;
    sum_odd_is_even(a, 1);
    assert(is_even(b));
    print_u8(b);
}
```

Here, the executable code `add_one_and_print` contains variables `a` and `b` of type `u8`,
and these variables are passed directly to `is_even(a)`, `is_even(b)`, and `sum_odd_is_even(a, 1)`
without ever needing any conversions to or from `Ghost<u8>`.
I think this is a good thing, and will make the type checking process simpler and more intuitive
for both the Rust type checker and for users trying to understand error messages from Rust's type checking.

My belief here stems partly from experience with F*'s `erased` type.
I've found marking types as `erased` and converting between `t` and `erased t` to be awkward,
but F*'s saving grace here is that `erased` is very seldom necessary.
F* specifications and proofs generally don't use `erased` at all,
and executable F* code usually uses `t` rather than `erased t`,
passing `t` values directly to specifications and proofs without going through
any intermediate `erased t` values.

### `Ghost<t>` in executable code

I've just argued that we don't need to use `Ghost<t>`
for variables declared in specifications and proofs,
because specifications and proofs don't make any distinction between ghost and executable variables.
Executable code, on the other hand, will need to distinguish between ghost and executable variables.
So for executable code, we need to at least occasionally use `Ghost<t>`
and when we use `Ghost<t>` we need to worry about how `t` is converted to `Ghost<t>` and vice-versa.

Consider the earlier ghost variable example:

```
#[exec]
fn do_something_to_v(v: &mut Vec<u8>) {
    ...
    while ... {
        #[spec] let copy_of_v = *v; // save a ghost copy of v

        ... mutate v ...

        some_lemma_about(copy_of_v, *v);
        assert(some_relation_between(copy_of_v, *v));
    }
    ...
}
```

In the current version of Verus, based on a mode system,
the variable `copy_of_v` has mode `spec` and type `Vec<u8>`.
By contrast, when using types instead of modes,
we expect `copy_of_v` to have type `Ghost<Vec<u8>>`.
So to make the type checker happy,
we'll need to convert `*v` from type `Vec<u8>` to type `Ghost<Vec<u8>>`,
and then in the calls to `some_lemma_about` and `some_relation_between`,
we'll need to convert back from `Ghost<Vec<u8>>` to `Vec<u8>`
(assuming, as I've already advocated,
that `some_lemma_about` and `some_relation_between`
use parameters of type `t` rather than `Ghost<t>`).

In addition, to avoid violating borrowing rules,
`v` cannot be copied in executable code, only in ghost code.
Finally, the calls to the ghost functions `some_lemma_about` and `some_relation_between`
must be inside ghost blocks, since these calls will be erased.
So the Verus code above would need to be expressed as something like:

```
fn do_something_to_v(v: &mut Vec<u8>) {
    ...
    while ... {
        let copy_of_v: Ghost<Vec<u8>> = ghost { *v }; // save a ghost copy of v

        ... mutate v ...

        ghost {
            some_lemma_about(copy_of_v, *v);
            assert(some_relation_between(copy_of_v, *v));
        }
    }
    ...
}
```

I've omitted any `raise` operations (or `lower` operations?) because I'm
sure exactly where they would need to go,
since this this depends on design decisions about the type checking rules for
ghost types and ghost blocks.
I don't have a specific proposal for these decisions,
but I'd like to at least elaborate some of the possibilities.

The first question is where `Ghost<t>` values come from.
We expect `Ghost<t>` values to come from ghost blocks one way or another.
In fact, any value returned from a ghost block to executable code must have type `Ghost<t>`,
since the ghost block will be erased before compilation and no executable value
will be returned from the ghost block at runtime.
So there are various possible design decisions:

1. If a block `b` has type `t`, then the expression `ghost b` has type `Ghost<t>`
   (always convert to `Ghost`).
2. If a block `b` has type `Ghost<t>`, then the expression `ghost b` also has type `Ghost<t>`,
   and otherwise if `b` has type `t`, then the expression `ghost b` has type `Ghost<t>`
   (convert to `Ghost` only if necessary).
3. If a block `b` has type `Ghost<t>`, then the expression `ghost b` has type `Ghost<t>`,
   and otherwise the expression `ghost b` is ill-typed (never convert to `Ghost`).

Likewise, there are various possibilities for converting from `Ghost<t>` to `t`:

1. Always require an explicit conversion (e.g. `raise`).
2. Auto-raise in the same situations that Rust would auto-dereference a reference.
   (Note, though, that auto-dereference would not apply to the expressions
   `some_lemma_about(copy_of_v, *v)` and `some_relation_between(copy_of_v, *v)`,
   since they pass `copy_of_v` directly to a function without performing any operations
   on them to trigger auto-dereferencing.)
3. Automatically convert all `Ghost<t>` variables to `t` when entering a ghost block
   from executable code.

## Implications for verification languages (particularly Verus)

For the Verus project, we've discussed using a macro to translate from Verus-style syntax,
without ghost blocks, to native Rust syntax with ghost blocks.
In particular, we've proposed having explicit `spec` blocks and `proof` blocks in the Verus syntax,
which would both be translated into Rust `ghost` blocks.
Furthermore, many other Verus features, like `requires` and `ensures` clauses,
would also be translated into Rust `ghost` blocks.

There are still unresolved questions, though.

First, would the Verus-to-Rust translation introduce `Ghost<t>` types automatically?
In other words, if the Verus code contained something like `#[spec] let x: u8 = ...`,
would the translation change `x`'s type from `u8` to `Ghost<u8>`?
This could be convenient, but it could also be confusing when users are trying
to understand type checking errors and they expect `x` to have type `u8`.

Second, Verus already has `Spec<t>` types and `Proof<t>` types,
which are already a lot like `Ghost<t>`.
`Spec<t>` always implements `Copy`, whereas `Proof<t>` does not always implement `Copy`.
Does `Ghost<t>` always implement `Copy`, and if so,
does `Spec<t>` just become an alias for `Ghost<t>`?
Or are `Spec<t>` types and `Proof<t>` different from `Ghost<t>`,
perhaps being structs with a `Ghost<t>` field inside?
Or can verification languages declare their own customizable `Ghost<t>`-like types,
so that Verus would declare `Spec<t>` and `Proof<t>` as primitives,
and never declare `Ghost<t>` at all?
Can the typing rules (e.g. for ghost blocks) be written in a way that would
be friendly to `Spec<t>` and `Proof<t>` rather than insisting on `Ghost<t>` everywhere?

Third, Verus already has a mode checker that it currently uses to check
executable code and proof code.
(Inside specification code, mode checking is almost trivial; all variables are `spec`-mode variables
that can be copied.)
I believe Verus would continue to use its own mode checking inside proofs to distinguish between
`spec`-mode variables (which can always be copied, no matter what their type)
and `proof`-mode variables (which must be checked by the borrow checker),
since the mode checking allows programmers to use natural types for variables (`x: u8` in a proof
rather than `x: Ghost<u8>` or `x: Spec<u8>` in a proof).
However, it's unresolved what role, if any, Verus's mode checker would play in executable code.
Would spec-mode variables and proof-mode variables both have the same type `Ghost<t>` in executable code,
and the mode checker distinguishes between them?
Or would types take over this responsibility in executable code,
perhaps by using separate `Spec<t>` and `Proof<t>` types, where `Spec<t>` implements `Copy`
and `Proof<t>` does not?  At the moment, the latter sounds simpler,
since we'll have to use types for ghostness anyway (at least `Ghost<t>`).

These questions relating to `Ghost<t>` may not have obvious answers.
I think that's ok, because as I said before, I expect pretty much all specification and proof
code to use type `t` rather than `Ghost<t>`,
and even in executable code I expect `Ghost<t>` to be the uncommon case
compared to `t`.
We may be able to ask users to do a little bit of extra work when using `Ghost<t>`
(or `Spec<t>` and `Proof<t>`),
as with F*'s `erased t` type.

### One minimalist approach

Rather than leaving all of these questions completely up in the air,
I'd like to work out the most minimalist approach in more detail.
Suppose we make the following design decisions:

- If a block `b` has type `t`, then the expression `ghost b` has type `Ghost<t>`
  (always convert to `Ghost`).
- Always require an explicit conversion from `Ghost<t>` to `t` (e.g. `raise`).
- `Ghost<t>` implements `Copy` for all types `t`.
- No special support for `Spec<t>` or `Proof<t>`.
  These are just library types that the Rust compiler knows nothing about.
- Verus uses mode checking for proof code, but not for exec code.
  (exec code relies on Spec<t> and Proof<t> instead.)
- The translation does not change any types; it never changes `t` to `Ghost<t>`,
  `Spec<t>`, or `Proof<t>`.

The library types `Spec<t>` and `Proof<t>` might look something like this in Rust:
```
#[derive(Clone, Copy)]
pub struct Spec<T> {
    value: Ghost<T>,
}
impl<T> Spec<T> {
    pub fn new(value: Ghost<T>) -> Spec<T> {
        Spec { value }
    }
}
impl<T> Deref for Spec<T> {
    type Target = T;
    ghost fn deref(&self) -> &T {
        &self.value.raise()
    }
}

// No Clone, no Copy
pub struct Proof<T> {
    value: Ghost<T>,
}
impl<T> Proof<T> {
    pub fn new(value: Ghost<T>) -> Proof<T> {
        Proof { value }
    }
}
impl<T> Deref for Proof<T> {
    type Target = T;
    ghost fn deref(&self) -> &T {
        &self.value.raise()
    }
}
```

The earlier Verus examples would look like:
```
#[spec]
fn is_even(x: u8) -> bool {
    x % 2 == 0
}

#[proof]
fn sum_odd_is_even(x: u8, y: u8) {
    requires(x as int + y as int < 256 && !is_even(x) && !is_even(y));
    ensures(is_even(x + y));

    // SMT solver proves this automatically
}

#[exec]
fn add_one_and_print(a: u8) {
    requires(a < 255 && !is_even(a));

    let b = a + 1;
    proof {
        sum_odd_is_even(a, 1);
        assert(is_even(b));
    }
    print_u8(b);
}

#[exec]
fn do_something_to_v(v: &mut Vec<u8>) {
    ...
    while ... {
        let copy_of_v: Spec<Vec<u8>> = spec { *v }; // save a ghost copy of v

        ... mutate v ...

        proof {
            some_lemma_about(*copy_of_v, *v);
            assert(some_relation_between(*copy_of_v, *v));
        }
    }
    ...
}
```

when macro-translated into Rust, this code might look something like:
```
#[spec]
ghost(unchecked) fn is_even(x: u8) -> bool {
    x % 2 == 0
}

#[proof]
ghost(checked) fn sum_odd_is_even(x: u8, y: u8) {
    ghost {unchecked, requires(x as int + y as int < 256 && !is_even(x) && !is_even(y))}
    ghost {unchecked, ensures(is_even(x + y))}

    // SMT solver proves this automatically
}

#[exec]
fn add_one_and_print(a: u8) {
    ghost {unchecked, requires(a < 255 && !is_even(a))}

    let b = a + 1;
    ghost {checked, {
        sum_odd_is_even(a, 1);
        assert(is_even(b));
    }}
    print_u8(b);
}

#[exec]
fn do_something_to_v(v: &mut Vec<u8>) {
    ...
    while ... {
        let copy_of_v: Spec<Vec<u8>> = Spec::new(ghost {unchecked, *v}); // save a ghost copy of v

        ... mutate v ...

        ghost {checked, {
            some_lemma_about(*copy_of_v, *v);
            assert(some_relation_between(*copy_of_v, *v));
        }}
    }
    ...
}
```
where `checked` means run the borrow checker and `unchecked` means don't run the borrow checker.
Notice that in the one place that Rust would introduce a `Ghost<t>` type
(as the value returned from a `ghost` block),
the translation wraps the result in a call to `Spec::new`,
so that the Verus code never sees `Ghost<t>` directly, only `Spec<t>` and `Proof<t>`.
In this way, all error messages from the type checker will be in terms of `t`, `Spec<t>`, or `Proof<t>`,
not `Ghost<t>`.

Overall, I think even this minimalist approach would not be too bad.

### The one minimalist approach from above, slightly formalized for those who want a little more rigor

For even more detail, here is a simplified model of Verus syntax, with expressions for integer literals,
integer addition, function calls to named functions `f` with exactly one argument
and one return value, spec blocks, proof blocks, variables `x`, and let bindings:

```
Mode = spec | proof | exec
Type = u8 | Spec<Type> | Proof<Type>
Expr = 0 | ... | 255 | Expr + Expr | f(Expr) | spec(Expr) | proof(Expr)
     | x | let Mode x: Type = Expr; Expr
```
(Note that in Verus, `let x` expands by default to `let exec x` in exec code,
and to `let spec x` in proof and spec code.)

Here is a simplified model of Rust syntax:

```
check = checked | unchecked
type = u8 | Ghost<type>
expr = 0 | ... | 255 | expr + expr | f(expr) | ghost(check, expr) | expr.raise()
     | x | let x: type = expr; expr
(also assume library types Proof<Type> and Spec<Type> are declared)
```

Let `T(Mode, Expr)` be a translation from Verus to Rust.
For a Verus function with a particular `Mode` and a body `Expr`,
`T(Mode, Expr)` translates the body into Rust code.
A helper translation `S(Expr)` inserts `ghost(unchecked, Expr)` expressions.
The translations are syntactic so that a macro should be able to handle them.
I assume that the Verus mode checker will follow up with a more precise mode checking
of proof code.
The important thing is that the mode checker can only check that
ghost blocks are in appropriate places -- it cannot decide where the ghost blocks should go,
since ghost blocks are inserted syntactically, before resolution, type checking, and mode checking.

```
T(Mode, 0) = 0
...
T(Mode, 255) = 255

T(Mode, Expr1 + Expr2) = T(Mode, Expr1) + T(Mode, Expr2)

// Note: both in both proof and spec mode, function arguments are assumed to be spec, not proof,
// since spec is the common case.
// You can override this default assumption by writing f(proof(Expr)),
// which is handled specially by S(Expr).
T(spec, f(Expr)) = f(T(spec, Expr))
T(proof, f(Expr)) = f(S(Expr))
T(exec, f(Expr)) = f(T(exec, Expr))

T(spec, spec(Expr)) disallowed (or we could make it a no-op: T(spec, Expr))
T(proof, spec(Expr)) = S(Expr)
T(exec, spec(Expr)) = Spec::new(ghost(unchecked, T(spec, Expr)))

T(spec, proof(Expr)) disallowed (you can't reenter proof mode from spec mode)
T(proof, proof(Expr)) disallowed (or we could make it a noop: T(proof, Expr))
T(exec, proof(Expr)) = Proof::new(ghost(checked, T(proof, Expr)))

T(Mode, x) = x

T(spec, let spec x: Type = Expr1; Expr2) = let x: Type = T(spec, Expr1); T(spec, Expr2)
T(spec, let proof ...) disallowed
T(spec, let exec ...) disallowed

T(proof, let spec x: Type = Expr1; Expr2) = let x: Type = S(Expr1); T(proof, Expr2)
T(proof, let proof x: Type = Expr1; Expr2) = let x: Type = T(proof, Expr1); T(proof, Expr2)
T(proof, let exec ...) disallowed (as in previous Verus)

// spec-mode and proof-mode declarations were allowed in exec mode in the original Verus checker,
// but here I'm assuming that that Spec<t> and Proof<t> will replace these:
T(exec, let spec ...) disallowed (use let exec x: Spec<t> instead)
T(exec, let proof ...) disallowed (use let exec x: Proof<t> instead)
T(exec, let exec x: Type = Expr1; Expr2) = let x: Type = T(exec, Expr1); T(exec, Expr2)

S(proof(Expr)) = T(proof, Expr) // opt-out of default-to-spec: the user didn't want spec after all
For all other Expr:
S(Expr) = ghost(unchecked, T(spec, Expr)).raise()
// Note: it's also possible to define more sophisticated versions of S that
// push the ghost(unchecked, ...) deeper inside Expr, so that fewer opt-outs will be required.
// I've omitted this for simplicity.
```
