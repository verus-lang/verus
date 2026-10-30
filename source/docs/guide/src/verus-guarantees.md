# What Verus guarantees

When Verus successfully runs on your program without reporting an error, what does that tell you?
First, note that Verus only examines Rust code that the developer explicitly indicates
should be verified, either by wrapping it in the [`verus!` macro](verus_macro_intro.md),
or by adding the [`#[verus_spec]` attribute](exec_attr.md).  Verus does not
inspect and hence cannot provide any guarantees for code that hasn't opted into
verification.

For code that *has* opted into verification, a successful Verus verification promises:
1. The code is memory safe.
2. The code is panic free.
3. The code is free of [undefined behavior (UB)](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).
4. The code is correct, in the sense that it meets its specification.

Note that the last guarantee is only as strong as the specification itself.  A weak spec may not provide
the guarantees you expect.  For example, given a function that returns an `Option<T>`, if the specification
only ensures interesting properties when the function returns `Some`, then the implementation might always
return `None`, satisfying the spec, but likely not satisfying the caller.

Equally important are the properties that Verus does not guarantee, even when it successfully verifies code:
1. Verus does not verify the performance of the code, so it can still be horribly slow.
2. Verus does not verify the absence of resource exhaustion,
   so your program might still run out of memory or stack space,
   and Verus does not provide guarantees about what happens after that point.
3. While Verus enforces termination of specification and proof code
   (since this is crucial for soundness), Verus does not verify
   that your executable code will terminate.  While Verus verifies 
   [decreases clauses](recursion.md#recursive-functions-decreases-fuel), 
   this only provides lightweight termination checking, not a guarantee of
   program termination.  For example, a call into a Rust standard library
   function might never return.  In general, proving termination for
   concurrent programs is a truly complex undertaking that still requires
   significant research and development.

The guarantees Verus does provide are contingent on the following:
1. The invocation of Verus is trusted.  Verus supports flags like
   `--verify-function` and `--no-verify` that disable some or all verification
   checks during development.  Verification results should only be trusted when
   flags like these are not included in the invocation of Verus.  The
   `--no-cheating` flag will report an error if these specific flags are provided,
   but even then, the invocation of Verus is still a trusted action.
2. Verus supports various ways to introduce [assumptions](tcb.md),
   since assumptions are often necessary in realistic verification projects.
   If these assumptions are wrong or violated, then that undermines the verification guarantees.
   To control for this, please see the `--no-cheating` command-line flag.
3. As discussed later in this chapter, verified code that expects to be called
   from unverified code needs to [take additional precautions](call-from-unverified-code.md).
   Verus provides the (experimental) `-V check-api-safety` flag to help with this.
4. Rust proc-macros can make arbitrary changes to Rust source code before Verus sees the code,
   or they can change what code Verus sees during verification compared to what a normal Rust compile
   sees.  Verus does not prevent such shenanigans.
5. The correctness of Verus, the solvers it depends on, and on Rust itself (including `rustc`,
   `cargo`, etc.).
