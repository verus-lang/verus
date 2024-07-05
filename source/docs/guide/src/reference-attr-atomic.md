# #[verifier::atomic]

The attribute `#[verifier::atomic]` can be applied to any _exec-mode_ function to indicate
that it is "atomic" for the purposes of the atomicity check by
[`open_atomic_invariant!`](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_atomic_invariant.html).

Verus checks that the body is indeed atomic, unless the function is also marked
`external_body`, in which case this feature is assumed together with the rest of the function
signature.

This attribute is used by `vstd`'s [trusted atomic types](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/index.html).
