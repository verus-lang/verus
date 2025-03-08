# The `birds_eye` command

The `birds_eye` keyword can be used to allow unrestricted reads of the `pre` variable
without impacting the tokens that are input or output in the operation.

Specifically, `let` statements in transitions may be prefixed with the `birds_eye` annotation.

```
birds_eye let $var_name = $expr
```

The expression on the right-hand side may access `pre.field` for any field.
A `birds_eye` let can be used in any `transition!`, `readonly!`, or `property!` operation.

Though `birds_eye` allows accessing all fields, it is particularly useful for fields using
the [`not_tokenized`](./strategy-not-tokenized.md) strategy or storage-based strategies.

### Impact on determinism

Ordinarily, VerusSync operations are deterministic in the input arguments and input tokens,
a property enforced by various strategy-specific restrictions on how fields may be manipulated.
However, when `birds_eye` is used, operations may become nondeterminstic.

### Restrictions

There are two main restrictions:

 1. No preconditions can depend on a `birds_eye` variable. This means that `require`,
    `remove`, `have`, and `deposit` statements cannot depend on a `birds_eye` value.
    Since this nondeterministic information is not available at the beginning of the token
    operation, there would be no way to create a well-formed precondition.

 2. No `guard` operation can depend on a `birds_eye` variable. This is crucial for soundness;
    the value being guarded must be deterministic as otherwise, the output token `&Tok`
    might become invalid before its lifetime expires.

These restrictions are currently implemented by a coarse-grained dependency analysis
determined primarily by the order of statements, rather than the actual uses of variables.
Dependency analysis may be made more precise in the future.

### Impact on resulting ghost token operation

The presencne of a `birds_eye` let-statement does not impact the tokens that are input
or output. It does, however, create extra (ghost) out-parameters for the fields that
are referenced inside `birds_eye`. This allows the operation's postconditions to
refer to these nondeterministic values.

## Example

TODO
