# How rustc implements auto (marker) traits like `Send` and `Sync`

Notes from reading `~/rust/compiler` (rustc 1.99.1), as background for
`rust_verify/src/unsafe_marker_impls.rs`, which checks user-written
`unsafe impl Send/Sync` blocks.

## 1. Where the logic lives

| What | Old solver | New solver |
|---|---|---|
| deciding whether the auto impl is a candidate | `rustc_trait_selection/src/traits/select/candidate_assembly.rs`, `assemble_candidates_from_auto_impls` | `rustc_next_trait_solver/src/solve/trait_goals.rs`, `consider_auto_trait_candidate` + `disqualify_auto_trait_candidate_due_to_possible_impl` |
| constituent types | `select/mod.rs`, `constituent_types_for_auto_trait` | `solve/assembly/structural_traits.rs`, `instantiate_constituent_tys_for_auto_trait` |
| turning constituents into sub-goals | `select/confirmation.rs`, `confirm_auto_impl_candidate` + `select/mod.rs`, `collect_predicates_for_types` | `consider_auto_trait_candidate` → `probe_and_evaluate_goal_for_constituent_tys` |
| coinduction | `select/mod.rs`, `coinductive_match` (uses `tcx.trait_is_coinductive`, true for auto traits) | the search graph treats cycles of coinductive goals as success |
| restrictions on writing impls of auto traits | `rustc_hir_analysis/src/coherence/orphan.rs` (`orphan_check_impl`), `coherence/unsafety.rs`, `coherence/always_applicable.rs` (negative impls) | – |

The two solvers implement the same semantics; the description below applies to both.

## 2. The algorithm

To prove `Ty: AutoTrait`, rustc collects candidates:

1. **Where-clauses** from the `ParamEnv` (`T: Send` in scope).
2. **User impls**: any explicit `impl`/`unsafe impl` (positive), including the
   one we're checking. A negative impl (`impl !Send for X`) is never a
   candidate for a positive goal.
3. **Object candidate**: `dyn Tr + Send: Send`.
4. **The built-in "auto impl" candidate** (`AutoImplCandidate`). This applies only if:
   * the trait is an auto trait (`tcx.trait_is_auto`);
   * **no explicit impl, positive or negative, exists for the root of the
     self type** (`tcx.for_each_relevant_impl(trait, self_ty, ..)` finds
     nothing). This works on the *simplified* type (the ADT's `DefId`, or
     `&`, `*mut`, etc.), so for example a single `unsafe impl Send for X<u8>`
     turns off the auto impl for *every* `X<_>`, including `X<u16>`. This is
     how `impl !Send for *mut T` and `unsafe impl<T: Sync> Send for &T`
     replace the structural rule for raw pointers and shared references;
   * if the trait is unsafe (`Send`/`Sync` are) and the type has `unsafe`
     fields (unstable `unsafe_fields` feature), the auto impl is not used;
   * the self type isn't one of: `Param`, rigid `Projection`/`Inherent`/`Free`
     alias, `Placeholder`, `Bound`, `Dynamic`, `Foreign` (except for
     `experimental_default_bounds`). For these there is no auto impl, only
     where-clauses, object candidates or item bounds. Inference variables give
     ambiguity. Opaque `impl Trait` types are revealed to their hidden type
     ("auto trait leakage") outside their defining scope, or are ambiguous inside it.

If the auto-impl candidate is picked, the sub-goals are `C: AutoTrait` for each
**constituent type** `C`:

| self type | constituents |
|---|---|
| `bool`, `char`, ints, floats, `!`, `FnDef`, `FnPtr`, `Error` | none (holds trivially) |
| `str` | `[u8]` |
| `*const T`, `*mut T`, `&T`, `&mut T` | `T` (the explicit impls in `core` override these, see below) |
| `[T; N]`, `[T]`, pattern types `T is pat` | `T` |
| `(T1, ..., Tn)` | `T1, ..., Tn` |
| `PhantomData<T>` | `T` (special-cased, `def.is_phantom_data()`) |
| ADT (struct / enum / union) | the type of every field of every variant, `def.all_fields()`, instantiated with the args (whether or not the fields are visible) |
| closures / coroutine closures | tupled upvar types |
| coroutines | upvars + the coroutine witness (types that live across awaits) |
| `unsafe<'a> T` | `T` under the binder |
| opaque `impl Trait` (outside defining scope) | the hidden type |

Each constituent is **normalized** before the sub-goal is formed
(`collect_predicates_for_types` calls `normalize_with_depth`). Late-bound regions
are turned into placeholders and then bound again.

**Coinduction**: auto traits are coinductive (`TraitDef::is_coinductive`). If
a goal shows up again while it is still being proven, and every goal on the cycle
is coinductive, the cycle counts as success. That's why
`struct List { next: Option<Box<List>> }` is `Send`. Without coinduction the
check would never terminate. Polymorphic recursion that never closes a cycle hits the
recursion limit and reports overflow.

**Regions**: auto trait impls don't add region constraints of their own, but
explicit impls used along the way can (for example `unsafe impl Send for X<'static>`).
These constraints become region obligations that borrowck/wfcheck later checks.
`predicate_must_hold_modulo_regions` would silently drop them.

### Relevant explicit impls in `core`/`alloc`/`std`

```text
impl<T: ?Sized> !Send for *const T        impl<T: ?Sized> !Sync for *const T
impl<T: ?Sized> !Send for *mut T          impl<T: ?Sized> !Sync for *mut T
unsafe impl<T: Sync + ?Sized> Send for &T                       (not structural!)
&mut T: Send  <= T: Send   (auto)         &T, &mut T: Sync <= T: Sync   (auto)
impl<T: ?Sized> !Send for NonNull<T>      impl<T: ?Sized> !Sync for NonNull<T>
impl<T: ?Sized> !Sync for UnsafeCell<T>   (and Cell/RefCell have !Sync)
unsafe impl<T: Send + ?Sized> Send for Unique<T> ...
Rc: !Send, !Sync;  Arc: Send/Sync <= T: Send + Sync;  Box/Vec: auto via Unique
```

Verus `builtin`: `Ghost<A>` is unconditionally `Send + Sync` through explicit
unsafe impls. `Tracked<A>` (external_body, contains `PhantomData<A>`) uses the
auto impl, so `Tracked<A>: Send <= A: Send`.

## 3. Rules on writing impls of auto traits (coherence)

* `orphan.rs`: if the auto trait comes from another crate (`Send`/`Sync`
  always do), the self type of an impl **must be a nominal type local to
  the current crate** (a local ADT or local `extern type`). Impls for `dyn`, type
  parameters, aliases, references, tuples, etc. are rejected. So the self type
  of the impls we check is always a local ADT (or a local foreign type).
* `unsafety.rs`: positive impls of `Send`/`Sync` must be `unsafe impl`, negative
  impls must be safe (`impl !Send`, which needs the `negative_impls` feature).
* Negative auto-trait impls must be "always applicable" (fully generic). Positive
  impls may be specialized (`unsafe impl Send for X<u8>`) and may have any
  where-clauses.

## 4. Consequences for checking `unsafe impl<Ps> Send for X<Args> where W`

The impl is sound (relative to the other impls) when the built-in auto impl
would have derived the same thing: assuming `W`, every constituent of
`X<Args>` is `Send`. Because the user impl removes the auto impl for *all*
`X<_>` (§2), recursive occurrences of `X<..>` in the fields go through the user
impl itself. That's the coinductive hypothesis `X<Args>: Send` (and, more generally,
"every impl in the crate holds", since each impl is checked separately).

Verus changes this (see `unsafe_marker_impls.rs`):

* extra hypotheses: `*mut T`, `*const T` and `PhantomData<T>` are `Send` and
  `Sync` for every `T` (raw pointers are useless without a permission token,
  and the token's own `Send`/`Sync` is what matters);
* structural recursion only goes into ADTs that are **transparent to Verus** from
  the impl's module (VIR `DatatypeTransparency`) and that have no explicit impl
  of the trait (the same disqualification rule as rustc). Anything else
  (opaque ADTs like `Rc`, `Vec`, `Box`, `Tracked`; ADTs with explicit impls;
  params; projections; `dyn`; closures; ...) is handed to rustc's trait
  solver unchanged. For these the extra hypotheses don't apply, so
  `Vec<*mut u8>: Send` fails. That's conservative;
* builtin structural types (tuples, arrays, slices, `str`, `&mut T`) recurse
  the way the auto impl does. `&T: Send` goes to `T: Sync` (the `core` impl). `&T: Sync`
  and `&mut T: Sync` go to `T: Sync`;
* goals already in progress (starting with the impl's own `X<Args>: Trait`) are
  assumed (coinduction). There's no backtracking (each goal has exactly one
  rule), so one set of visited goals is enough;
* goals handed to rustc are checked with an `ObligationCtxt` under the impl's
  `ParamEnv`, followed by region resolution using the impl's assumed-WF
  types. That way region requirements of explicit impls aren't dropped;
* the self type of the impl itself must be transparent to Verus from the impl's
  module (otherwise we can't see the fields), and must not have unsafe fields;
* the depth is bounded by `tcx.recursion_limit()`. Hitting the limit is an error.

Known corner cases and how they're handled:

| case | handling |
|---|---|
| `unsafe impl Send for X<u8>` while a field mentions `X<u16>` | `X` has an explicit impl, so `X<u16>: Send` goes to rustc, which only finds the `X<u8>` impl and fails. Same as rustc. |
| field type is a normalizable projection | normalized first, then recursed into. Rigid projections go to rustc (where-clauses). |
| ADT with a negative impl (`impl !Send for Y`) | `Y` has a relevant impl, so it goes to rustc, which fails. |
| type params `T` | rustc, so the impl's where-clauses decide |
| `dyn Tr + Send` | rustc (object candidate) |
| enum / union | all fields of all variants |
| ghost / tracked fields (`Ghost<T>`, `Tracked<T>`) | external/opaque to Verus, so rustc (`Ghost` always, `Tracked<T>` needs `T`) |
| impls inside `#[verifier::external]` code (e.g. vstd's `PCell`) | not translated by Verus, so not checked (trusted, as before) |
| `unsafe_fields` | ADTs with unsafe fields aren't recursed into. The self type is rejected. |
