# Guide source and inline example audit

Audit source: `source/docs/state_machines/src/SUMMARY.md`, all linked Markdown
chapters, their fenced snippets, and their include directives. This document
separates complete source examples from generic syntax fragments and exercises
which have no original implementation.

## Complete included examples

| Guide source | Checked reproduction in `examples/verified_tsm/` |
| --- | --- |
| `tutorial/counting_to_2.rs` | `counting_to_2.rs`: complete protocol and original two-thread atomic client |
| `tutorial/counting_to_n.rs` | `counting_to_n.rs`: complete protocol, ticket distribution and threaded atomic client |
| `tutorial/counting_to_n_atomic.rs` | `counting_to_n_atomic.rs`: complete ordinary model, operations and proofs |
| `tutorial/fifo.rs` | `fifo.rs`: complete ring protocol and PCell/atomic producer/consumer client |
| `tutorial/rc.rs` | `rc.rs`: complete protocol and reference-counted pointer client |
| `tutorial/pcell_example.rs` | `pcell_example.rs`: original empty/put/take permission demonstration |
| `reference-examples/strategy_option.rs` | `strategy_option.rs`: complete optional-ownership reference model and client |

The unverified Rust versions included by explanatory chapters illustrate the
same runtime algorithms. The verified counterparts retain those algorithms;
unverified erasure listings do not contribute proof credit. FIFO value order
is checked by its runtime harness; its formal specifications preserve the
original memory-safety scope.

## Complete inline models and valid property examples

| Chapter/snippet | Reproduction and adaptation |
| --- | --- |
| `components.md`: entire `AdderMachine` | `guide_components.rs`; variable resource adapter, both original induction hooks |
| `transition-language.md`: all valid `InitExample` alternatives | `guide_init.rs`; incomplete alternatives remain isolated failures |
| `transition-language.md`: all valid `TransitionExample` alternatives | `guide_transitions.rs`; duplicate update remains an isolated failure |
| `transition-language.md`: entire `RequireLetExample`, both equivalent operations | `guide_require_let.rs`; both positive histories retained |
| `transition-language.md`: tuple/assert-let/match/indexed update forms | complete `test_assert_require_let.rs`, `test_relation_match.rs`, `test_double_scoped_updates_match.rs`; the last retains a pure weak-relation model separately from its strengthened resource companion |
| `properties.md`: `waiting_means_positive` | `guide_properties.rs`: Bool waiting and variable count, the exact implication assertion through a `birds_eye` Bool observation, checked atomic decrement |
| `properties.md`: contradiction `in_bounds` | Same fixture: declared-variable companion checks its bound directly; explicit Count companion preserves `Have >= 10; assert false`, invokes it with a shared Count token in the contradictory branch |
| `properties.md`: `get_perm_ref` | Same fixture: actual PCell permission deposited and borrowed, Bool presence plus explicit permission authority pins the requested argument |

The properties fixture passed independent review and verification with 65 proofs
and no errors; the runtime harness checks the
atomic result and cell value. The atomic proof establishes the documented
non-wrapping decrement and an upper bound. Exact single-thread runtime output
is a harness check, rather than an extra trusted logical contract.

Two corrections to `properties.md` are explicit. The chapter declares
`num_remaining` as `variable`, but its `Have >= 10` example needs `count`.
Further, `deposited ==> perm.is_some()` alone cannot prove
`perm == Some(x)` for an arbitrary caller-selected `x`. The guard companion
adds an owned constant authority and requires equality with that authority.
A mutable ghost authority also records Bool absence before deposit. These
additions have checked invariant proofs and introduce no executable locks.

## Strategy fragments

Strategy pages generally contain field declarations and individual operations,
not complete named state machines. Their operand families are exercised by
complete cases and dedicated guide fixtures:

| Strategy page(s) | Coverage |
| --- | --- |
| `variable`, `constant` | complete adders/counting clients and `constants.rs` |
| `not_tokenized` | `adder_hidden.rs`; `adder_with_max.rs` also proves the retained initialized minimum through a checked reachable invariant |
| `count` | `test_count_codegen.rs`, complete counting-to-n and contradiction property companion |
| `bool` | `guide_bool_operands.rs`, full `test_bool_codegen.rs`, property waiting/deposit companions |
| `option` | `guide_optional_operands.rs`, full option/binding cases; empty/general operands and remove/add replacement |
| `set` | full Set/ISet cases and `set_operands.rs`; finite/general operands, empty operands, persistent variants |
| `multiset` | `guide_multiset_operands.rs`, `multiset_replacement.rs`, Rc/Arc/RefCell clients; general operands, owned-versus-borrowed removal and paired removal/addition |
| `map` | `guide_map_operands.rs`, `guide_imap_operands.rs`, both different-key move cases and full Maps/DistRwLock cases; general operands, infinite-domain operands and different-domain replacement reviewed |
| `persistent_option` | complete persistent Option case, `persistent_optional.rs` and `guide_optional_operands.rs` |
| `persistent_bool` | complete persistent Bool case and scalar guide histories |
| `persistent_map` | complete finite/infinite persistent Map cases plus the GeneralMap operand fixture; separately reviewed and committed |
| `storage_option` | complete Rc/Arc/RefCell clients, `storage_cell.rs`, `storage_option_binding.rs`, `guide_storage_optional_operands.rs`; singleton/general Some/None exchanges and real PCell guards reviewed |
| `storage_map` | complete FIFO/FlatCombine/Maps clients, binding fixtures, `guide_storage_map_operands.rs` and `storage_pair_transfers.rs`; bulk operands, two-cell transfers and paired deposit/withdrawal reviewed |

A singleton operation does not establish coverage of a page's general operand
operation. General physical operand coverage now includes checked bulk clients
and paired transfers, with a one-deposit/one-withdrawal path budget and the
existing old-base disjointness restriction. The four substantial special
exchange cases passed separate complete-source review and actual verification;
their exact pure relation proofs alone are not resource-safety credit.

## Syntax templates, formal descriptions, and unimplemented exercises

* `invariants.md` gives invariant and induction-hook templates with ellipses;
  it adds no complete named example beyond those above.
* `birds-eye.md` gives generic binding syntax and its restrictions. Complete
  AdderWithMax, Rc, RefCell, FIFO, and TopSort clients demonstrate permitted
  observations; dependency misuse remains negative coverage.
* `strategy-reference.md` gives the optional-add safety proof template.
  Checked option companions and isolated unsafe-add failures cover the rule.
* `monoid-formalism.md` describes a mathematical construction, rather than a
  compilable example. The checked completion algebra handles its frame
  quantification and explicitly valid neutral outer unit; it does not assume
  existence of an invariant witness to validate that neutral unit.
* `operations.md` is empty. The macro syntax/generated-code/refinement pages,
  hash-table, alternate counting, and reader-writer-lock guide pages contain
  TODO headings rather than implementations. Complete repository RWLock and
  DistRwLock examples are nevertheless separately ported.
* The guide's persistent-set and persistent-count summary links have no target
  pages. Full repository cases cover these strategies.
* `rc-exercises.md` requests an Arc adaptation and a Weak-pointer extension.
  Full Arc is ported. The Weak exercise provides interface specifications but
  no original protocol/client implementation; it is not counted as an original
  source reproduction or presented as solved.
