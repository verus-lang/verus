# Proof-producing TSM client ergonomics assessment

The audited protocol reproduction gate is complete. This assessment concerns proof bookkeeping at call sites, not coverage or trust.

| Client | Original usage | Current repeated bookkeeping | Proposed checked reduction |
| --- | --- | --- | --- |
| CountingN | Native ticket count split, then one transition with counter and ticket tokens | Sparse fragment construction, right-fragment arithmetic and split/join | Generated native field constructors, field extraction, and partial count splitting; a generic exact-local `split_off` is a reusable foundation |
| FIFO | Start returns a PCell permission; end consumes that permission and updates field tokens | Singleton tracked maps, all-completion deposit readiness, witness extraction, owner/atomic partition | Actual singleton map pack/unpack; generated native physical-value methods, exact checked observed postconditions, and mutating field façade |
| Rc/Arc | Deposit/clone return reader tokens; borrowed reader property returns a permission reference | Singleton normalization, constructor readiness, reader/counter split, map-to-value borrowed extraction | Native field constructors/extraction; checked singleton packing and borrowed guard-value utility; generated singleton observation results |
| RefCell | Borrow/update flag token and return a native reader/writer token | Five generated observation results and two compatible-State observation sites, plus runtime permission/invariant reasoning | Selected generated local readiness, exact same-witness physical observations, native field extraction and checked singleton helpers |
| Interner | Read-only properties accept persistent observations and return pure equality/value facts | All-frame equality/value readiness, native singleton-to-IMap bridge, explicit compatibility frames | Generated property observation façade, retaining independent completion frames for aliased references |
| DistRWLock | Native per-key/count operations plus explicit algorithm model reasoning | Logical map removal enabling bridge, original model refinement, protocol counter extraction | Native map operands/accessors and checked local consume conditions; preserve original algorithm and refinement reasoning |

The generic `split_off` helper requires an exact decomposition of the CURRENT owned fragment. It chooses only its owned remainder and never consults a compatible machine state. Storage singleton helpers pack/unpack actual tracked values, and direct guard-value extraction borrows an actual guarded storage map. None creates a permission from a ghost completion.

Private first-slice evidence:

- Five helper bodies plus ownership/PCell demonstration: 8 verified, 0 errors; compilation and execution succeed.
- Complete CountingN client: 30 verified, 0 errors; compilation and execution succeed. Its empty-stamp setup uses existing `empty()`, and the worker loop uses checked local subtraction followed by `split_off`.
- Oversplit, borrowed contribution consumption, and wrong singleton key: each rejected only at the corresponding helper precondition (14 verified, 1 error in the private fixtures).

The live module imports its own existing map/set lemma groups. The targeted
library rebuild verifies all five helper bodies alongside the existing TSM
modules: **130 verified, 0 errors**. The imported canonical ownership/PCell demo
verifies **3/0**, compiles and runs; each imported misuse rejects **4/1** at its
intended helper precondition. These counts separate library proofs from client
bodies rather than duplicating the private helper definitions. Evidence is in
`/tmp/verified-tsm-ergonomic-helpers-vstd-fixed.log` and
`/tmp/verified-tsm-root-ownership-helpers`.

The generic helper still needs one explicit existential-decomposition witness.
The private CountingN experiment centralized this as a checked ticket-subtraction
lemma, so that helper alone did not establish comparable client ergonomics.
The reviewed native field operations below now absorb count subtraction and
whole-field extraction; the canonical CountingN client needs no such lemma.

All-completion readiness and transition witness projections are substantial recurring costs. The selected RefCell APIs below absorb these obligations; other clients retain their existing readiness proofs. Replacing a universal readiness obligation with one chosen completion would be unsound. An ergonomic façade must prove readiness from observed local/shared fields for every compatible completion, and may expose only postconditions justified by checked transition output relations. Arbitrary borrowed references still require separate completion frames, since aliases do not establish separating sums.

## Generated native field operations

The macro now emits native specification constructors and checked ownership
operations for each logical field. These methods describe or split the current
owned component; they do not manufacture ownership.

| Interface | Meaning |
| --- | --- |
| `Fragment::field_FIELD(value)` / `with_FIELD(value)` | Describe a sparse native field or replace a component in a specification fragment |
| `owns_FIELD()` / `value_FIELD()` | Inspect local shape/value; variable and constant getters recommend the appropriate ownership tag |
| `owns_FIELD_at(key)` / `value_FIELD_at(key)` | Inspect a locally owned map entry without assuming a finite domain |
| `Protocol::take_FIELD(token)` | Extract the whole current field and return the exact remainder |
| `Protocol::take_FIELD_with_constants(token)` | Move that field and current constant observations into the selected owner |
| `Protocol::split_FIELD(token, amount)` | For a count field, extract an amount no greater than the current owned count and compute its remainder |

Persistent count values are local lower bounds. A false persistent Bool or an
empty optional component supplies no local evidence; it does not establish
global falsehood or absence. Specification setters produce descriptions, while
tracked ownership still comes from checked allocation, splitting and protocol
updates. Generated names are checked for collisions before emission.

The complete threaded Counting2 and CountingN clients now use these methods
without caller resource-algebra imports, exact split arguments or subtraction
lemmas. Their transitions, invariants, atomic specifications and executable
thread algorithms are preserved. Interner also uses native sparse factories and
shape getters; its more substantial readiness proofs remain.

| Complete client | Lines before / after | Manual exact split calls before / after |
| --- | ---: | ---: |
| Counting2 | 190 / 159 | 5 / 0 |
| CountingN | 226 / 184 | 6 / 0 |
| Interner | 355 / 350 | 0 / 0 |

These source-site and whole-file measures compare against commit `93885dd48`;
line totals are context, not a measure of executable complexity or an assertion
of identical legacy APIs. Separate review independently verified the complete
live clients **33/0**, **42/0** and **47/0**, compiled them and ran their harnesses.
Oversplitting the current local count rejects **42/1** even when another owner
holds the missing contribution. Reading ownership from an empty projection
rejects **33/1**. Ambiguous generated field names reject before emission.

The matching targeted library rebuild remains **130/0**. Retained Rc **55/0**,
Arc **61/0**, RefCell **68/0**, FlatCombine **90/0** and the full general infinite
special case **82/0** also compile and run. Evidence:
`/tmp/verified-tsm-fields-{macro,vstd}.log`,
`/tmp/verified-tsm-review-live-field-*.log` and
`/tmp/verified-tsm-root-field-regressions`.

Selected local readiness and observation contracts now simplify the complete
RefCell client, as detailed below.


## Complete RefCell caller proof bookkeeping comparison

The baseline is the complete checked client at commit `93885dd48`, compared with the original guide `examples/state_machines/tutorial/ref_cell.rs`. The final canonical source is `examples/verified_tsm/ref_cell.rs`; it preserves every protocol transition/invariant and all executable borrow, mutable borrow, replacement, disposal, conflict and runtime demonstration behavior. Its opt-in readiness/result API verifies **83/0** with the actual release macro, compiles and runs successfully. The matching targeted library verifies **130/0**. The earlier field-only stage verified 68/0 and is retained below to show where the readiness/result improvement adds value.

Counts below cover the caller portion after the state-machine declaration. Imports cover the whole source. A carrier import is a `vstd::resource` import exposing algebra/PCM/carrier types; protocol location and physical convenience imports are excluded. Sparse literals are direct `RefCounter::Fragment { ... }` expressions. Splits count direct `.split(...)` calls, not generated field takes. Snapshots count `let ghost old_fragment`; witnesses count explicit `*_witness(...)` calls. A quantified readiness block is an `assert forall|frame: ...` establishing universal compatibility conditions. Protocol invariants and unrelated bag extensionality proofs are excluded.

| Caller burden | Original guide | Checked baseline `93885dd48` | Private native-field stage | Canonical readiness/result stage |
| --- | ---: | ---: | ---: | ---: |
| Carrier/algebra import statements | 0 | 6 | 6 | 0 |
| Sparse fragment literals | 0 | 3 | 0 | 0 |
| Explicit fragment splits | 0 | 2 | 0 | 0 |
| Old-fragment snapshots | 0 | 5 | 5 | 0 |
| Transition witness calls | 0 | 5 | 5 | 0 |
| Quantified readiness blocks | 0 | 1 | 1 | 0 |
| Manual initializer State choice | 0 | 1 | 1 | 0 |
| Whole-file lines, context only | 435 | 527 | 512 | 423 |

The native-field stage uses generated sparse field constructors and setters for the flag, constant, reader and writer views. Generated `take_flag_with_constants` proves the exact current-owned partition, absorbing explicit remainder construction and split equations. Checked singleton helpers pack actual PCell permissions for deposits and extract the actual permission returned in a singleton withdrawal. They do not construct permissions from a ghost state.

The six raw import statements remain during this intermediate stage because the existing proof blocks still mention carrier operations. Some individual imported symbols are now unused; counting them before final cleanup avoids crediting cosmetic removal as proof automation.

The field-only stage still had extra proof work:

- One reusable 24-line `deposit_ready` function establishes readiness for every compatible completion. It is called at construction and mutable-borrow disposal.
- Five transition calls retain old-fragment snapshots and unpack State/frame witnesses to recover flag, writer, reader and permission observations.
- Construction chooses an initial State to prove the initial flag/writer shape.
- Reader disposal proves the emptied bag by a separate extensionality quantifier, and other call sites invoke raw unit/commutativity lemmas.

The final generated contract slice absorbs that work transparently. Local readiness is justified by every compatible State sharing the observed constant and variable fields plus checked current-owned consumption rights; invariant/safety proofs establish asserted properties and absence. A chosen completion is insufficient. Exact output projections are derived from existing checked transition output relations, retaining unchanged fields and identifying actual withdrawn permissions through returned tracked maps. New-reader ghost permission observations may be returned from those relations, but cannot replace actual tracked physical withdrawal.

The canonical readiness/result column is supported by the actual release-macro 83/0 check and execution of the unchanged whole demonstration. Generated local readiness proves the universal bridge once; a generated canonical singleton deposit expression is proved equivalent to the original AST deposit function. Observation results retain the original strong relation, invariant, exact owned output and same-witness actual withdrawal equation. The caller does not maintain a handwritten quantified wrapper or per-call normalization helper. Native field takes normalize the reinstated flag footprint without manual carrier laws, and an exact native initializer shape follows directly from the original initializer contract.

The final client still unpacks five generated observation result records. Two call sites use their compatible before/after State observations to show the reader bag and flag update, or identify the physically withdrawn permission. Those observations are not distinguished global histories. Reader ghost values are selected from the actual owned reader fragment; tracked permissions come from the actual returned storage map. This retained model reasoning is explicitly different from zero proof work. Runtime PCell flag arithmetic, permission/value invariants, and API well-formedness specifications also remain checked.

Actual evidence is in `/tmp/verified-tsm-ref-cell-local-actual{,-runtime}.log`,
`/tmp/verified-tsm-local-ready-{macro,vstd}.log` and the independent
`/tmp/verified-tsm-review-actual-ready-{refcell,names}.log`. Separate review
approved the complete client and generated proofs. No comparison claims that
removing an explicit witness method call also removes every mathematical State
observation.

## Opt-in readiness and compatible observations

`#[verified_local_ready(do_deposit, do_withdraw, new_reader, drop_reader)]`
on the machine selects mutating transitions in a physical-storage protocol.
The original universal proof API remains available.

| Generated interface | Checked behavior |
| --- | --- |
| `TRANSITION_local_requires` | Uses current ownership, declared input requirements, local variable/constant observations and the exact supplied deposit |
| `TRANSITION_local_ready` | Proves the unchanged requirement for every invariant-compatible completion |
| `TRANSITION_local` / `TRANSITION_local_with_shared` | Performs the existing checked operation after that readiness proof |
| `TRANSITION_observed` | Returns the actual owned token/withdrawn map and ghost compatible before/after/frame information |

The observation contract uses one witness for the original strong relation,
both invariants, exact owned output, unchanged frame and physical conservation.
The states describe a compatible completion, not a distinguished hidden
history. Ghost observations cannot become owned permissions: the focused
attempt to return `before.storage` as tracked `PointsTo` fails the mode check.
Borrowing actual guarded permissions retains the existing lifetimes.

Normal lexical lets, if/match and require-let desugaring are supported. Selected
hidden or special-bound requirements reject explicitly; initializers, properties
and nonphysical protocols are outside this opt-in interface. Unknown/duplicate
names and collisions also reject before generation. New internal identifiers
are fresh; the parameter-name fixture verifies **21/0**, compiles and runs.

Wrong actual physical deposits and removal using only a borrowed writer each
reject **83/1** at their local operation precondition. All seven metadata/scope
negatives reject with their intended diagnostic. The hidden-storage negative
rejects **19/1** at the original storage-presence safety assertion; it is not
claimed as an isolated new readiness-bridge failure. Evidence:
`/tmp/verified-tsm-local-ready-live-checks/summary.txt`.

The ergonomic milestone now meets its concrete complete-client targets:
native threaded counting without caller carrier/split proofs and RefCell
without manual universal readiness or snapshot/witness plumbing. Exact legacy
API parity is not claimed. Interner and other complex clients retain some
explicit readiness/model reasoning; arbitrary hidden history and unsupported
syntax still require the documented checked companion/adapters.
