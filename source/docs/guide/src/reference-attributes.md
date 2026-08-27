# Attributes

 - `accept_recursive_types`
 - [`all_triggers`](#all_triggers)
 - [`allow_complex_invariants`](#verifierallow_complex_invariants)
 - [`allow_in_spec`](#verifierallow_in_spec)
 - [`atomic`](#verifieratomic)
 - [`auto`](#auto)
 - [`custom_err`](#verifiercustom_errtext-and-verifiercustom_errtext)
 - [`external`](#verifierexternal)
 - [`external_body`](#verifierexternal_body)
 - `external_fn_specification`
 - `external_type_specification`
 - [`ext_equal`](#verifierext_equal)
 - [`inline`](#verifierinline)
 - [`loop_isolation`](#verifierloop_isolation)
 - [`memoize`](#verifiermemoize)
 - [`opaque`](#verifieropaque)
 - [`proof_note`](#verifierproof_notetext-and-verifierproof_notetext)
 - [`prophetic`](#verifierprophetic)
 - `reject_recursive_types`
 - `reject_recursive_types_in_ground_variants`
 - [`rlimit`](#verifierrlimitn-and-verifierrlimitinfinity)
 - [`trigger`](#trigger)
 - [`truncate`](#verifiertruncate)
 - [`type_invariant`](#verifiertype_invariant)
 - [`when_used_as_spec`](#verifierwhen_used_as_spec)
 - [`exec_allows_no_decreases_clause`](#verifierexec_allows_no_decreases_clause)
 - [`assume_termination`](#verifierassume_termination)

## `#![all_triggers]`

Applied to a quantifier, and instructs Verus to aggressively select trigger groups for
the quantifier.
See [the trigger specification procedure](./trigger-annotations.md#selecting-trigger-groups)
for more information.

Unlike most Verus attributes, this does not require the `verifier::` prefix.

## `#[verifier::allow_complex_invariants]`

By default, `invariant_except_break` and `ensures` are not supported with
[`#[verifier::loop_isolation(false)]`](#verifierloop_isolation) because they
aren't needed. When loop isolation is disabled, the weakest precondition
calculation automatically tracks all paths through breaks into the code after
the loop, making these complex invariant types unnecessary.

However, in some cases (such as experimenting with toggling the loop isolation setting,
or for our de-sugaring of for-loops), it can be useful to use these invariant types even with loop isolation disabled.
The `allow_complex_invariants` attribute enables this by transforming the invariants:
 * `invariant_except_break` clauses are converted to regular `invariant` clauses
 * `ensures` clauses are ignored (since they are redundant with the weakest precondition calculation)

**This attribute only applies when `loop_isolation` is false.** Using it with `loop_isolation(true)`
(or the default) will produce an error.

## `#![verifier::allow_in_spec]`

Can be applied to an executable function with a [`returns` clause](./reference-returns.md).
This allows the function to be used in spec mode, where it is interpreted as equivalent
to the specified return-value.

## `#[verifier::atomic]`

The attribute `#[verifier::atomic]` can be applied to any _exec-mode_ function to indicate
that it is "atomic" for the purposes of the atomicity check by
[`open_atomic_invariant!`](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_atomic_invariant.html).

Verus checks that the body is indeed atomic, unless the function is also marked
`external_body`, in which case this feature is assumed together with the rest of the function
signature.

This attribute is used by `vstd`'s [trusted atomic types](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/index.html).

## `#![auto]`

Applied to a quantifier, and indicates intent for Verus to use heuristics to automatically 
infer 
Technically has no effect on verification, but may impact verbose trigger logging.
See [the trigger specification procedure](./trigger-annotations.md#selecting-trigger-groups)
for more information.

Unlike most Verus attributes, this does not require the `verifier::` prefix.

## `#[verifier::external]`

Tells Verus to ignore the given item. Verus will error if any verified code attempts to
reference the given item.

This can have nontrivial implications for the TCB of a verified crate; see [here](./tcb.md).

## `#[verifier::external_body]`

Tells Verus to only consider the function definition but not the function body, trusting that
it correctly satisfies its specification.

This can have nontrivial implications for the TCB of a verified crate; see [here](./tcb.md).

## `#[verifier::ext_equal]`

Used to mark datatypes that need extensionality on `Seq`, `Set`, `Map`,
`Multiset`, `spec_fn` fields or fields of other `#[verifier::ext_equal]`
datatypes.

See the [discussion of equality via extensionality](./extensional_equality.md#equality-via-extensionality)
for more information.

## `#[verifier::inline]`

The attribute `#[verifier::inline]` can be applied to any _spec-mode_ function to indicate
that that Verus should automatically expand its definition in the STM-LIB encoding.

This has no effect on the semantics of the function but may impact triggering.

## `#[verifier::loop_isolation]`

The attributes `#[verifier::loop_isolation(false)]` and `#[verifier::loop_isolation(true)]`
can be applied to modules, functions, or individual loops. For any loop, the most specific
applicable attribute will take precedence. 
This attribute impacts the deductions that Verus can make automatically inside the loop
body (absent any loop invariants).

 * When set to `true`: Verus does not automatically infer anything inside the loop body,
   not even function preconditions.
 * When set the `false`: Verus automatically makes some facts from outside the loop body
   available in the loop body. In particular, any assertion outside the loop body
   that depends only on variables not mutated by the loop body will also be available
   inside the loop.

## `#[verifier::memoize]`

The attribute `#[verifier::memoize]` can be applied to any _spec-mode_ function to indicate
that the [`by(compute)` and `by(compute_only)` prover-modes](./reference-assert-by-compute.md)
should "memoize" the results of this function.

## `#[verifier::opaque]`

Directs the solver to not automatically reveal the definition of this function.
The definition can then be revealed locally via the [`reveal` and `reveal_with_fuel` directives](./reference-reveal-hide.md).

## `#[verifier::proof_note("text")]` and `#![verifier::proof_note("text")]`

These attributes attach a string note to a `requires`/`ensures` clause or `assume`/`assert` statement.

- The outer attribute `#[verifier::proof_note]` must attach to an `assume`/`assert` statement.
- The inner attribute `#![verifier::proof_note]` (note the `!`) must attach to a `requires`/`ensures` clause.

When a proof obligation (`requires`/`ensures`/`assert`) fails, then the `"text"` of the note is included in the error message, as well as in the JSON output under the key `func-details`. An `assume` statement flagged by the `--no-cheating` mode is treated similarly. This can be useful for connecting informal spec requirements (say from a text description of desired properties) to obligations in the verified code.

Cannot be used together with [`custom_err`](#verifiercustom_errtext-and-verifiercustom_errtext).

## `#[verifier::prophetic]`

This attribute is used to mark a value as _prophecy-dependent_, or _prophetic_, meaning that its value may depend
on a value from the program's future, e.g., the `final` operator (used for [mutable references](./mutable-references.md)),
or the [value of a prophecy variable](https://verus-lang.github.io/verus/verusdoc/vstd/proph/struct.ProphecyGhost.html#method.value).
This attribute aids Verus in tracking which spec values are prophecy-dependent, which are restricted in certain contexts:

 * Prophecy-dependent values cannot appear in [decreases clauses](./reference-decreases.md).
 * Prophecy-dependent values cannot appear as an operand to `Ghost`.
 * Prophecy-dependent values cannot influence the value of tracked-mode ghost state.

The rationale for these restrictions [is explained here](https://verus-lang.github.io/verus/verusdoc/vstd/proph/index.html).

The `#[verifier::prophetic]` attribute may appear on any spec function or any ghost-mode local variable.

### On spec functions

By default, every spec function is considered non-prophetic unless it is explicitly marked prophetic.
Verus considers it ill-formed to have a function with a prophetic body that is not marked prophetic.

Examples:

```rust
// Ill-formed: prophetic value not allowed for body of non-prophetic spec function
spec fn future_value_of_mut_ref(a: &mut u64) -> u64 {
    *final(a)
}
```

```rust
// Ok
#[verifier::prophetic]
spec fn future_value_of_mut_ref2(a: &mut u64) -> u64 {
    *final(a)
}
```

Furthermore, if a spec function in a trait implementation is marked `#[verifier::prophetic]`,
then it must also be marked `#[verifier::prophetic]` in the trait declaration.
The converse is not true: an implementation function may be non-prophetic even if the trait function is prophetic.

### On local variables

By default, Verus infers the propheticness of each local variable based on the propheticness of its initial value.
A local variable can be explicitly marked prophetic regardless of its initial value.

Examples:

```rust
proof fn test() {
    let ghost mut local_var = 0;
    let tracked proph_var = vstd::proph::ProphecyGhost::<u64>::new();
    local_var = proph_var.value(); // Ill-formed: prophetic value not allowed for assignment to non-prophetic location
}
```

```rust
proof fn test() {
    #[verifier::prophetic]
    let ghost mut local_var = 0;
    let tracked proph_var = vstd::proph::ProphecyGhost::<u64>::new();
    local_var = proph_var.value(); // Ok, `local_var` was explicitly marked prophetic
}
```

```rust
proof fn test(tracked some_int: &mut u64) {
    let ghost mut local_var = *final(some_int);
    let tracked proph_var = vstd::proph::ProphecyGhost::<u64>::new();
    local_var = proph_var.value(); // Ok, `local_var` was inferred as prophetic
}
```

## `#[verifier::custom_err("text")]` and `#![verifier::custom_err("text")]`

These attributes attach a custom error message to a `requires`/`ensures` clause or `assume`/`assert` statement.

- The outer attribute `#[verifier::custom_err]` must attach to an `assume`/`assert` statement.
- The inner attribute `#![verifier::custom_err]` (note the `!`) must attach to a `requires`/`ensures` clause.

When the associated proof obligation fails, the `"text"` becomes the primary displayed error message. Unlike `proof_note`, `custom_err` labels are not included in JSON `func-details` proof-note sets.

Cannot be used together with [`proof_note`](#verifierproof_notetext-and-verifierproof_notetext).

## `#[verifier::rlimit(n)]` and `#[verifier::rlimit(infinity)]`

The `rlimit` option can be applied to any function to configure the computation limit
applied to the solver for that function. 

The default `rlimit` is 10. The rlimit is roughly proportional to the amount of time taken
by the solver before it gives up. The default, 10, is meant to be around 2 seconds.

The rlmit may be set to `infinity` to remove the limit.

The rlimit can also be configured with the `--rlimit` command line option.

## `#[trigger]`

Used to manually specify trigger groups for a quantifier.
See [the trigger specification procedure](./trigger-annotations.md#selecting-trigger-groups)
for more information.

Unlike most Verus attributes, this does not require the `verifier::` prefix.

## `#[verifier::truncate]`

The `#[verifier::truncate]` attribute can be added to expressions to silence
recommends-checking regarding out-of-range as-casts.

When casting from one integer
type to another, Verus usually inserts recommends-checks that the source
value fits into the target type. For example, if `x` is a `u32` and we cast it
via `x as u8`, Verus will add a recommends-check that `0 <= x < 256`. 
However, sometimes truncation is the _desired_ behavior, so 
`#[verifier::truncate]` can be used to signal this intent, suppressing
the recommends-check.

Note that the attribute is optional, even when truncation behavior is intended.
The only effect of the attribute is to silence the recommends-check, which is
already elided if the enclosing function body has no legitimate verification errors.

**Aside.** When truncation is intended, [the bit-vector solver mode](./reference-assert-by-bit-vector.md) is often useful for writing proofs about truncation.

## `#[verifier::type_invariant]`

Declares that a spec function is a type invariant for some datatype. See [type invariants](./reference-type-invariants.md).

## `#[verifier::when_used_as_spec]`

It can be convenient to use the name of an exec function in a specification
context.  For example, if a function takes `v: Vec<u64>` as an argument, it's
convenient to use `v.len()` in the pre-/post-conditions, even though `v.len()`
is an exec function.  To add such a shortcut to your code, add a
`#[verifier::when_used_as_spec(your_spec_fn_name)]` attribute to your
executable function.  For this to work, the supplied spec function (e.g., named
`your_spec_fn_name` in the example above) must take the same number and type of
arguments and return the same return type as the exec function.

## `#[verifier::exec_allows_no_decreases_clause]`

Disables the requirement that `exec` functions with recursion or loops have a decreases clause. Can be applied to a function, module, or crate, affects all the contents.

## `#[verifier::assume_termination]`

Assumes that an `exec` function is guaranteed to terminate, even if it does not have a `decreases` clause.
This is currently unneeded, as `exec` termination checking does not check that callees also terminate.
