# Spinning off separate SMT solver instances

## Verus verification basics

By default, Verus spawns one SMT solver instance for each Rust module.

To verify a module, Verus needs to include all the facts used in the module, including all the types, traits, and spec/proof/exec functions used/defined in that module. When verifying a specific function in a module, the SMT solver is exposed to facts that may not be related to that function, and this may cause the SMT solver to be unstable for "flaky" proofs.

## Spinning off a fresh solver for an individual function

`#[verifier::spinoff_prover]` can be applied to a proof or exec function to run the verification of the function in a fresh SMT solver instance. Adding `#[verifier::spinoff_prover]` to the function minimizes the unrelated facts exposed to the SMT solver, hence making it a bit more stable.

### Cost

Spinning off a solver imposes some additional performance overhead. Verus must do extra preparation work to send SMT queries to the new solver instance, in addition to spawning the new solver instance in the first place. The solver must also redo some of the setup work to process the common facts that it shares with the broader module.

### Spinoff prover for parallelism

`#[verifier::spinoff_prover]` can also be used to introduce parallel verification at the function granularity.

Suppose a module has 10 functions: 9 of them verify in under 0.1 seconds each, and one complex function `slow_fn()` verifies in 1 second. This module finishes verification in 1.9 seconds. If we apply `#[verifier::spinoff_prover]` to `slow_fn()`, Verus spawns a separate SMT solver instance for `slow_fn()`, which runs in parallel alongside the rest of the module. Even though the new solver instance has to reprocess the common facts for `slow_fn()`, both finish in about 1 second. We essentially cut the total verification time by half!
