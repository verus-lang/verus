# Spinning off separate SMT queries
## Verus verification basics

By default, Verus spawns one SMT query for each Rust module.

To verify a module, Verus needs to include all the facts used in the module, including all the types, traits, and spec/proof/exec functions used/defined in that module. When verifying a specific function in a module, the SMT solver is exposed to facts that may not be related to that function, and this may cause the SMT solver to be unstable for "flaky" proofs.

## Spinoff prover
`#[verifier::spinoff_prover]` can be applied to a proof or exec function to run verification of the function in a new separate SMT query. Adding `#[verifier::spinoff_prover]` to the function minimizes the unrelated facts exposed to the SMT solver, hence making it a bit more stable.

### Cost
Spinoff prover has its overhead. Verus needs to do extra work to prepare the SMT query for the spin off prover, and the SMT solver essentially has to process the facts twice (for those used in the original module). The total amount of work increases slightly each time we spawn a spin off prover.

### Spinoff prover for parallelism
A seconary useage for spinoff prover is to introducde parallelism in a single module. 

Suppose a module has 10 functions: 9 of them finish verification in 0.1 seconds each, and one complex function `long_fn()` takes 1 second. This module finishes verification in 1.9 seconds. If we apply `#[verifier::spinoff_prover]` to `long_fn()`, Verus spawns a separate SMT query for `long_fn()`, which runs in parallel alongside the rest of the module, and both finish in about 1 second. We essentially cut the total verification time by half!


