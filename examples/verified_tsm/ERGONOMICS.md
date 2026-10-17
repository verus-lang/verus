# Checked state-machine example ergonomics

The checked examples keep the original Rust guide models, helper names, and client structure. `verified_tokenized_state_machine!` supplies the trusted macro's field tokens and `Instance` methods (the generic interface) by default. `#[verified_raw_tokens]` explicitly selects the checked low-level protocol interface when a caller needs it. This flag changes the interface, not the proof obligations or permission model.

Note: the audit below (and [ERGONOMICS_AUDIT.json](ERGONOMICS_AUDIT.json)) was recorded when the default was a set of field-shape-specific interfaces, which have since been removed together with the `#[verified_field_tokens]` marker. Its hashes, the LLCRT application rows and the recorded API adaptations (`InstanceInfo`, owned instances, mutable persistent clones) describe that earlier interface, not the current one.

```rust
use verus_state_machines_macros::verified_tokenized_state_machine;

verified_tokenized_state_machine! {
    Counter {
        fields {
            #[sharding(count)] pub counter: nat,
        }
        init! { initialize() { init counter = 0; } }
        transition! { increment() { add counter += (1); } }
    }
}
```

The declaration above illustrates the default interface. The complete audited examples are the source files in this directory; this abbreviated declaration is not a separate verification result.

For the original ordinary models `adder`, `adder_generic`, and `leader_election_complete`, `verified_state_machine_model!` keeps their original unannotated fields. Those examples have no ownership clients or properties that require token APIs, so adding token roles and sharding annotations would be unnecessary. Their original initialization lets, helpers, induction hooks, transition parameters, and empty mains remain. The generic model needs a builtin-macro import for the generated `is_variant` attribute. Atomic CountN retains its constant/variable annotations because its original `finalize` property is checked by the native token/property interface; the pure-model entrypoint does not emit that property API.

## What the source comparison measures

The audit compares the 25 guide primaries with `../state_machines`, and the eight LLCRT protocol schemas and their clients with original application Git `acd267f0`. It also records the current canonical application and the final formatted default-interface proposals. [ERGONOMICS_AUDIT.json](ERGONOMICS_AUDIT.json) binds source hashes, model fields, transition parameter patterns, function-name occurrences, and precise parameter/return/binding differences.

All 25 primaries retain every original distinct function name and add no distinct helper-function names. The combined textual function-declaration count is 298 original versus 300 checked: the two additional declarations are Interner's checked trait method and its `u64` implementation, both named `compute_eq`. This counts user source declarations, not generated kernel lemmas or supplemental histories. Twenty-four guide models have exactly the original parsed field annotations/types and transition parameter shapes; Atomic CountN has the documented sharding annotations. All eight application schemas retain those original shapes. These structural comparisons are not a claim that every contract, mode annotation, or client expression is byte-identical.

The binding audit retains the original source binding names in common function scopes. It distinguishes tracked/ghost syntax and excludes explicit proof blocks from its executable-syntax projection. It does not expand invariant macros or constitute a proof of Rust erasure equivalence. Legacy proof syntax, method relocation from operational `Instance` to `InstanceInfo`, changed return types, and new proof bindings are recorded explicitly. Existing separate source reviews and whole-crate verification supply the stronger algorithm/ownership checks.

## Simplifications implemented

Interner uses the original name `compute_eq` for the checked equality interface. Its original generic free function was an unimplemented `external_body` stub. The checked version delegates to a method whose contract establishes equality of the actual values:

```rust
pub trait VerifiedEq: Sized {
    fn compute_eq(&self, other: &Self) -> (res: bool)
        ensures res == (*self == *other);
}
```

The `u64` implementation and original free `compute_eq` remain executable. The trait/provider obligation replaces the old trust; deleting it would leave arbitrary generic equality unimplemented. The existing loop and original client main remain, with checked termination facts.

Arc and Rc use `struct_with_invariants!` again. The handwritten invariant-predicate type, alias, and `inv` implementation have been removed from user source. Each structure carries one additional `Ghost<Loc>` cache, tied by its well-formedness predicate to the actual instance's location. The generated predicate uses that cache and the original cell identity. The cache grants no token, physical permission, or completion evidence. The original cell operations, invariant references, and locking structure remain. Their previously checked overflow adaptation remains explicit: `clone` returns `Option<Self>` and returns `None` at `u64::MAX`; the original `nil`, `a5`, `a7`, and `a67` demonstration sequence is retained with result handling. This is a required, documented difference from the original unchecked `Self` return.

Disk keeps its original mathematical machines and refinement helpers. Its interpretation is now a predicate over a supplied actual authority token rather than an expression describing a token that a specification would manufacture. `take_step` uses modern `proof fn`, tracked arguments, `Ghost`, and a named tracked return; the original intermediate names remain. The added right-child case and authority/fragment facts are checked refinement work, not removable debug scaffolding. TopSort keeps the original DFS function and variables while proving the dependency and stack facts that were originally assumed. Refinement examples prove impossible branches instead of trusting them.

## Ownership-related differences that remain

The complete application keeps all eight checked schemas: BarrierMachine, RwToks, StbPhase, SingleThreadedMachine, DemoToks, MutexToks, TVarToks, and TxToks. The default change removes eight redundant opt-ins across six model files. It adds no application helper or executable action. Earlier checked adaptations still carry actual tracked resources:

| Difference | Reason it remains |
|---|---|
| Mutable persistent-token `clone` calls | Duplication is proved using the idempotence of an actually owned resource. A descriptive value or instance id cannot supply that resource. |
| Mutable basis for a zero-token operation | Empty ownership is split from a real owner and the saved owner is restored. Metadata alone cannot create a storage capability. |
| Full `InstanceInfo` and ghost caches | Cloned metadata retains the location and every original constant; operations still require actual owners and their instance agreement. |
| Physical guard lifetime and finite map/domain facts | A guard borrows the actual permission. Withdrawal while that borrow is live must fail; a ghost map image cannot replace a tracked map. |
| `same_ticketing` and `same_cancel_evidence` | These two additional free spec helpers state observable agreement after checked resource cloning instead of assuming opaque resource-object equality. |

The repeated optional persistent-clone match and the generated field-specific basis suffix could be shortened by future checked library adapters. Those adapters are not implemented or required to establish this source alignment. Removing the actual mutable borrow, clone proof, or instance/constant premises would change the ownership contract.

Initializer arity is already aligned. The original and checked Demo calls both use `new(a, b, None, None)`; the original and checked Barrier calls both supply the empty tracked map and option. Dropping those arguments would be a new convenience API for both versions, not restoration of an original shorter call.

## Verification and execution coverage

Whole-crate guide and substantial-inline gates check the complete models, induction hooks, properties, and callable client bodies. A primary's runtime result must be interpreted according to its original main: eight of the 25 mains contain an executable demonstration; seventeen are empty. TopSort's complete DFS is verified in its primary, but its DAG/cycle execution belongs to the separate executable supplement. Tracked-only protocol histories exercise proof contracts and erase at runtime. They are not execution of the original locking/client algorithm. The 93-file original/guide/substantial cohort and additional diagnostic/history cases are recorded separately; this document's source audit does not infer a fresh corpus pass from formatting.

The matching private default-API application library verified **2,335 / 0** and compiled. The complete same application plus a verified main calling the unchanged original two-thread `stb_demo::example` verified **2,336 / 0**, compiled, and executed with exit **0**. Both reports identify entire-crate verification. The temporary adapter changes only function visibility and module paths. The original application baseline remains byte-identical: two tracked slice axioms and five assumed operations in the same three files. These application runs do not claim `--no-cheating`.

The three ordinary-model alignment successors separately passed **8 / 0 each**, `--no-cheating`, normal-budget whole-crate verification, compilation, and original empty-main smoke. They do not replace or modify their native ownership histories. Actual verusfmt was used for all final formatted inputs; import ordering and the two optional trailing commas were audited structurally, and temporary generic/macro aliases were restored to exact original names. No new axiom or executable lock was introduced by the ergonomic changes.
