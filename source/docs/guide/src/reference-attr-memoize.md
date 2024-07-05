# #[verifier::memoize]

The attribute `#[verifier::memoize]` can be applied to any _spec-mode_ function to indicate
that the [`by(compute)` and `by(compute_only)` prover-modes](./reference-assert-by-compute.md)
should "memoize" the results of this function.
