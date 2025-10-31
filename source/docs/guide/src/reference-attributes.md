# Attributes

 - `accept_recursive_types`
 - [`all_triggers`](#all_triggers)
 - [`allow_in_spec`](#verifierallow_in_spec)
 - [`atomic`](#verifieratomic)
 - [`auto`](#auto)
 - [`external`](#verifierexternal)
 - [`external_body`](#verifierexternal_body)
 - `external_fn_specification`
 - `external_type_specification`
 - [`ext_equal`](#verifierext_equal)
 - [`inline`](#verifierinline)
 - [`loop_isolation`](#verifierloop_isolation)
 - [`memoize`](#verifiermemoize)
 - [`opaque`](#verifieropaque)
 - `reject_recursive_types`
 - `reject_recursive_types_in_ground_variants`
 - [`rlimit`](#verifierrlimitn-and-verifierrlimitinfinity)
 - [`trigger`](#trigger)
 - [`truncate`](#verifiertruncate)
 - [`type_invariant`](#verifiertype_invariant)
 - `when_used_as_spec`
 - [`exec_allows_no_decreases_clause`](#verifierexec_allows_no_decreases_clause)
 - [`assume_termination`](#verifierassume_termination)

## `#![all_triggers]`

Applied to a quantifier, and instructs Verus to aggressively select trigger groups for
the quantifier.
See [the trigger specification procedure](./trigger-annotations.md#selecting-trigger-groups)
for more information.

Unlike most Verus attributes, this does not require the `verifier::` prefix.

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
