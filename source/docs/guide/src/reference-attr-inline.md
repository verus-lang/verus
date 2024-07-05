# #[verifier::inline]

The attribute `#[verifier::inline]` can be applied to any _spec-mode_ function to indicate
that that Verus should automatically expand its definition in the STM-LIB encoding.

This has no effect on the semantics of the function but may impact triggering.
