# Verus bug: trait-method-impl contract inheritance ignores method-level generic parameters

## Summary

When a trait method has its own generic type parameter (in addition to `Self`), and that method is
implemented for some type with a **real proof body** (not `axiom fn`), the inherited
`requires`/`ensures` clauses are silently wrong. Facts that should be trivially true by hypothesis
are unprovable inside the body, and — more seriously — the checked `ensures` does not correspond to
the true postcondition: directly `assume`-ing the literal target proposition (with the correct,
real types) still fails the postcondition check.

## Minimal reproduction

`source/verus-bug-repro-crash.rs` (run with `./target-verus/release/verus
verus-bug-repro-crash.rs --crate-type=lib` from `source/`, after `source ../tools/activate`):

```rust
pub trait Val: Sized {
    spec fn val(self) -> nat;
}

// `nonzero`'s own generic parameter `Foo` is distinct from `Self`.
pub trait ValProps: Val {
    proof fn nonzero<Foo: Val>(&self, other: &Foo)
        requires
            self.val() != 0,
            other.val() != 0,
        ensures
            self.val() + other.val() > 0,
    ;
}

pub struct Wrapper<Bar: Val>(Bar);

impl<Bar: Val> Val for Wrapper<Bar> {
    closed spec fn val(self) -> nat {
        self.0.val()
    }
}

impl<Bar: Val> ValProps for Wrapper<Bar> {
    proof fn nonzero<Baz: Val>(&self, other: &Baz) {
        assert(other.val() != 0); // panics before this can even be checked
    }
}
```

This panics the compiler outright:

```
thread '<unnamed>' panicked at rust_verify/src/verifier.rs:843:21:
internal error: generated ill-typed AIR code: error 'error 'error 'error 'use of undeclared variable Foo&.'
  in expression 'Foo&.'' in expression '(verus_bug_repro_crash!Val.val.? Foo&. Foo& other!)''
  in expression '(%I (verus_bug_repro_crash!Val.val.? Foo&. Foo& other!))''
  in expression '(not (= (%I (verus_bug_repro_crash!Val.val.? Foo&. Foo& other!)) 0))'
```

This is the single most useful piece of evidence: it shows, at the AIR level, a literal reference
to a sort/type-tag named `Foo&.` with no corresponding declaration anywhere in the impl — i.e. the
trait method's own generic parameter `Foo` (from `nonzero<Foo: Val>` in the trait declaration), left
completely unsubstituted when lowering the inherited contract for this impl. Nothing in the impl
(`Bar`, `Baz`, `Self`) is named `Foo`, so the dangling reference has nothing to resolve to and
generation fails outright.

### The same bug, hidden by a name collision

`source/verus-bug-repro-silent.rs` is byte-for-byte the same file, except the impl's own generic
parameter (`Bar` above) is renamed to `Foo` — i.e. it now happens to share a name with the trait
method's own generic parameter, purely coincidentally:

```rust
// The impl's own generic parameter happens to also be named `Foo` - the same
// name the trait declaration above uses for `nonzero`'s own generic parameter.
pub struct Wrapper<Foo: Val>(Foo);

impl<Foo: Val> Val for Wrapper<Foo> {
    closed spec fn val(self) -> nat {
        self.0.val()
    }
}

impl<Foo: Val> ValProps for Wrapper<Foo> {
    proof fn nonzero<Baz: Val>(&self, other: &Baz) {
        // `other.val() != 0` is one of this method's own inherited `requires`.
        // It should be trivially available as a hypothesis - it isn't.
        assert(other.val() != 0); // FAILS

        // Even directly assuming the literal ensures goal (correctly typed)
        // doesn't help: the postcondition Verus actually checks isn't the
        // proposition written in the trait declaration above.
        assume(self.val() + other.val() > 0);
    } // the `ensures` clause still FAILS
}
```

Nothing else changed — same trait, same method, same bodies — and yet the crash is completely
gone. In its place: two silent, ordinary-looking verification failures, exactly the kind a proof
author would normally interpret as "my proof is wrong" rather than "the tool is inheriting the
wrong contract":

```
error: postcondition not satisfied
  --> verus-bug-repro-silent.rs:31:13
   |
31 |             self.val() + other.val() > 0,
   |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition

error: assertion failed
  --> verus-bug-repro-silent.rs:49:16
   |
49 |         assert(other.val() != 0); // FAILS
   |                ^^^^^^^^^^^^^^^^ assertion failed
```

The dangling, unsubstituted `TypParam("Foo")` reference from the trait declaration is exactly the
same as in the crash variant — but this time, since the impl *does* have an in-scope parameter
named `Foo` (its own element-type parameter), the reference resolves — purely by name coincidence —
to that, instead of erroring. It is a real, valid type, so nothing crashes. But it is **the wrong
type**: the inherited clause ends up talking about the impl's own element-type parameter (`Foo`,
i.e. `Wrapper<Foo>`'s own generic) instead of the method's actual argument type (`Baz`, the real
type of `other`). `other.val()`, as checked, is not a call to `Val::val` monomorphized at `Baz` — it
silently becomes a differently-monomorphized, unrelated uninterpreted term, and no axiom connects
the two.

## Root cause

`vir/src/ast_to_sst_func.rs`, `Lowerer::inheritance` (around line 645):

```rust
fn inheritance(
    ctx: &Ctx,
    function: &Function,
    ens_pars: &Pars,
    diagnostics: &'a D,
) -> Option<Self> {
    if let FunctionKind::TraitMethodImpl { method, trait_path, trait_typ_args, .. } =
        &function.x.kind
    {
        // Inherit requires/ensures from trait method declaration
        let tr = &ctx.trait_map[trait_path];
        let mut typ_params = vec![crate::def::trait_self_type_param()];
        for (x, _) in tr.x.typ_params.iter() {
            typ_params.push(x.clone());
        }
        let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
        assert!(typ_params.len() == trait_typ_args.len());
        for (x, t) in typ_params.iter().zip(trait_typ_args.iter()) {
            trait_typ_substs.insert(x.clone(), t.clone());
        }

        let trait_function = ctx.func_map[method].clone();

        let mut param_renames: HashMap<_, _> = trait_function
            .x
            .params
            .iter()
            .zip(function.x.params.iter())
            .map(|(p1, p2)| (p1.x.name.clone(), p2.x.name.clone()))
            .collect();
        param_renames
            .insert(trait_function.x.ret.x.name.clone(), function.x.ret.x.name.clone());
        ...
```

`trait_typ_substs` is built from exactly two sources:

1. `crate::def::trait_self_type_param()` — the placeholder for `Self`.
2. `tr.x.typ_params` — the generic parameters declared on the **trait itself**
   (`pub trait SomeTrait<A, B>`), zipped against `trait_typ_args` (the concrete types supplied at
   the `impl SomeTrait<...> for X` site).

Nothing here accounts for generic parameters declared on the **method** itself (`fn
nonzero<Foo: Val>(...)`, as opposed to the trait `ValProps`, which declares no type parameters of
its own beyond the implicit `Self`). `param_renames` (built a few lines later) does handle *value*
parameters correctly — it zips `trait_function.x.params` against `function.x.params` by position,
so `self`/`other` are renamed correctly regardless of what the impl calls them. But there is no
analogous zip of `trait_function`'s method-level type parameters against `function`'s method-level
type parameters.

The requires/ensures expression trees used for inheritance are the trait declaration's own
(`trait_function`, captured at line 681: `function: trait_function`), lowered via
`subst_exp(&inh.trait_typ_substs, &HashMap::new(), &exp)` (`lower_pure`, same file, ~line 748).
Since `trait_typ_substs` has no entry for the method's own type parameter (`Foo` in the trait
declaration), any type reference to it inside the inherited requires/ensures is left **completely
unsubstituted** — it remains a dangling `TypX::TypParam("Foo")` referring to a name that simply
isn't one of the impl-function's actual type parameters (which are `Foo` [the impl's own
element-type parameter, from `impl<Foo: Val> ValProps for Wrapper<Foo>`] and `Baz` [this method's
own fresh parameter]).

## Evidence chain

All of the following are captured directly in the two repro files above, and were also confirmed
against the original context this was found in (`source/vstd/points_to.rs`,
`SeqPointsTo::is_disjoint` — a much larger, real-world instance of the exact same shape: a
`PointsToProperties` trait method `is_disjoint<PointsToPerm: PointsToParam>`, implemented for
`SeqPointsTo<T, PointsToPerm>`, whose own element-type parameter is *also* named `PointsToPerm`).

1. **Crash vs. silent.** The two repro files above, identical except for one type parameter's name,
   establish that the trait method's own generic parameter is never substituted during contract
   inheritance — only whether that leaves a hard crash or a wrong-but-well-typed silent
   misresolution depends on incidental naming.
2. **`requires` side.** In the silent variant, `assert(self.val() != 0)` (a fact purely about
   `Self`) succeeds; `assert(other.val() != 0)` (part of the *same* `requires` clause, just about
   the method's own generic parameter) fails.
3. **`ensures` side — the more serious half.** Directly `assume`-ing the exact target
   postcondition, phrased with the real, correctly-typed `self`/`other`
   (`assume(self.val() + other.val() > 0)`), still fails the postcondition check
   immediately afterward. This is conclusive: the proposition Verus actually checks as this
   method's `ensures` is not the proposition written in the trait declaration (instantiated at the
   real argument type) — it must be the same mis-substituted, collision-resolved proposition as the
   `requires` side, just on the postcondition instead. (In the original `is_disjoint` context, this
   was additionally confirmed by writing a complete, independently-verified case-split proof of the
   real goal and showing an `assert` of that same goal passes at the end of the real proof body —
   i.e. the true goal is genuinely provable; only the trait method's own contract-checking machinery
   checks something else.)

## Impact / where else this could bite

Any trait method declared with:
- an additional generic type parameter beyond `Self` (i.e. `fn foo<X: SomeBound>(...)`, not just
  `fn foo(&self)`), **and**
- a `requires`/`ensures` clause that mentions that parameter or a value of that parameter's type,
  **and**
- an implementation with a real proof/exec body (not `axiom fn`, which has no body to check and so
  never hits this path),

is affected. The failure mode depends entirely on incidental naming:
- If the implementing type's own generic parameters happen to share a name with the trait method's
  generic parameter, the contract silently becomes a different, generally-unsatisfiable-or-vacuous
  proposition with no diagnostic pointing at the real cause (as seen here: `requires`-side facts
  silently missing, `ensures`-side goals silently unprovable).
- If no such name collision exists, it's instead a hard internal-error panic
  ("ill-typed AIR code: use of undeclared variable").

Neither failure mode gives the user any indication that the actual problem is upstream in contract
inheritance rather than in their own proof.

## Suggested fix

In `Lowerer::inheritance` (`vir/src/ast_to_sst_func.rs:645`), `trait_typ_substs` needs additional
entries mapping the trait method's own type parameters (`trait_function`'s method-level generics,
i.e. whatever is left of `trait_function.x.typ_params` after the leading `Self`/trait-level ones
already handled) to the corresponding method-level type parameters of `function` (the impl's own
method), analogous to how `param_renames` already zips `trait_function.x.params` against
`function.x.params` by position a few lines later. Absent that fix, at minimum the "leftover"
unsubstituted type parameter case should be treated as a hard internal error unconditionally
(not just when it happens to dangle past every in-scope name) — e.g. by having `Lowerer::inheritance`
validate that every type parameter appearing in `trait_function`'s requires/ensures is covered by
`trait_typ_substs` before proceeding, so that a name collision cannot silently produce a wrong-but-
well-typed substitution instead of an error.

## Workaround: aligning names so the collision resolves correctly

Since the dangling, unsubstituted type parameter is resolved by an ordinary in-scope name lookup
(see Root cause above), the wrong-type-resolution failure mode can be turned into a *correct*
resolution — without touching Verus at all — by controlling which name it collides with:

1. Rename the trait method's own generic parameter to something that cannot collide with any
   implementing type's own struct/impl-level generics (e.g. `OtherPointsToPerm` instead of a short,
   generic-sounding name like `PointsToPerm` that an impl might also use for its own type
   parameter).
2. In every impl of that method, give the impl's own method-level generic parameter (`other`'s
   type) **the same name**.

The dangling reference is still never substituted — the underlying bug in `Lowerer::inheritance` is
completely untouched — but now the *only* thing in scope it can coincidentally match by name is the
impl's own method-level generic parameter, which is exactly `other`'s real type. The same fallback
that used to silently resolve to the wrong type (an impl's outer struct-level generic) now
resolves to the right one, purely because the name it's looking for no longer exists anywhere else
in scope.

This is not a fix: it relies on the same accidental name-matching behavior that causes the bug in
the first place, just aimed at the correct target instead of the wrong one. Any trait method with
its own generic parameter needs this same discipline applied deliberately (choose a
collision-proof name for the trait's own method generic; match it in every impl) to avoid silently
hitting this failure mode again, and a future Verus fix (see Suggested fix above) would make it
unnecessary.

## Background: where this was found

This surfaced while adding `is_disjoint` to `SeqPointsTo` in `source/vstd/points_to.rs` — a
`PointsToProperties` trait method with its own generic parameter, implemented for
`SeqPointsTo<T, PointsToPerm>` (whose own element-type parameter is, by pre-existing convention in
that file, named `PointsToPerm`) — the same collision-triggered shape as the minimal repro above
(the `tracked &mut self` there is specific to `points_to.rs`'s ownership tracking and isn't needed
to trigger the bug itself, as the minimal repro's plain `&self` demonstrates).
`vstd::points_to::PointsToSingleton::is_disjoint` (the base-case, non-generic-container
implementation of the same trait method) sidesteps this entirely by being declared `axiom fn` (no
body), which is presumably why this bug had not previously surfaced in that file.

The trait originally declared `is_disjoint<PointsToPerm: PointsToParam>(...)` — colliding with
`SeqPointsTo`'s own outer `PointsToPerm` element-type generic, exactly like the silent repro above
— which is why `SeqPointsTo::is_disjoint` needed `assume(other.size() != 0)` and still failed its
`ensures` even with a complete, independently-verified case-split proof of the real goal (see
Evidence chain above). Applying the workaround above — renaming the trait's method generic to
`OtherPointsToPerm` ([points_to.rs:94](vstd/points_to.rs#L94)) and giving `SeqPointsTo::is_disjoint`'s
own method generic the same name ([points_to.rs:264](vstd/points_to.rs#L264)), while leaving the
impl block's outer element-type generic as plain `PointsToPerm` — resolved both failures: the
`assume` could be deleted, and the full case-split proof (case-split on `other`'s address relative
to `self`'s range, using elements `0`/`len - 1` for the two outer cases and a div/mod witness index
for the "starts inside" case) now verifies for real, with no workaround left in the body. The whole
file passes `vargo build --release` (1937 verified, 0 errors).
