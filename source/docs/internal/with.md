# How a `with` clause is compiled

A `with` clause gives a function extra ghost and tracked inputs and outputs that are
**not** part of its executable signature. Callers supply them with `proof_with!`.

## The surface

Attribute form:

```rust
#[verus_spec(ret =>
    with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32> -> d: Ghost<u32>
    requires b == 1, c == 2,
    ensures ret == a, d@ == c,
)]
fn f(a: u64) -> u64 {
    proof_with!{|= Ghost(c)}
    a
}
```

`verus!` form, on the signature:

```rust
fn f(a: u64) -> (ret: u64)
    with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32> -> d: Ghost<u32>
    requires b == 1, c == 2,
    ensures ret == a, d@ == c,
{
    proof_with!{|= Ghost(c)}
    a
}
```

At a call site the extras go before the call, in one `proof_with!`:

```rust
proof_with!{Tracked(1u64), Ghost(2u32) => Ghost(d)}
let r = f(0);
```

Inputs come first, extra outputs after `=>` (`=> _` discards them). Inside the callee,
`|= ..` supplies the outputs. `with -> ..` alone declares outputs with no extra inputs.

The clause is attached to the callee's *specification*; nothing about `f`'s executable
signature changes, and a caller that omits `proof_with!` calls `f` normally.

## Why it is compiled the way it is

The extras are ordinary Rust values. They have types, they can borrow, they carry
lifetimes, they are used in variance positions, and they are moved or copied. A design
that carried them only in VIR would have to re-derive all of that, and every check it
forgot would be a soundness hole that no test names.

So the extras are checked by **rustc**, not by us:

> The macro generates a second function — the *verified counterpart* — whose parameter
> list contains the extras, and an AST pass redirects the marked call to it before type
> checking. Type errors, borrow errors, lifetime errors and variance errors at a `with`
> call are rustc's own errors about the counterpart.

The counterpart is where the specification and the real body go. What is left behind
under the user's name is an unverified stub:

- **the stub** keeps `f`'s signature and name, so callers that do not use `proof_with!`
  and the compiled program still see `f`. It is `#[verifier::external_body]` with a
  `requires(false)` precondition, so calling it without `proof_with!` fails to verify.
- **the counterpart** `_VERUS_VERIFIED_f` has `f`'s parameters *plus* the extras, carries
  the specification, and holds the body.

In erase mode no split happens: the stub keeps the real body and is the item that
executes.

## Generated artifacts

| Item | Role |
|---|---|
| `f` | Unverified stub. `#[verus::internal(unverified_stub)]`, `external_body`, `requires(false)`. |
| `_VERUS_VERIFIED_f` | The call target and the verified item. `#[verus::internal(verified_with)]`. |
| `_VERUS_VERIFIED_TRAIT_Tr` | For a trait method: a subtrait of `Tr` declaring the counterparts and blanket-implemented for every implementor. `#[verus::internal(verified_trait)]`. |
| `_VERUS_VERIFIED_IMPL_TRAIT_Tr` | For a trait method: a subtrait of `Tr` that carries the body of an overriding implementation. |
| `impl _VERUS_VERIFIED_IMPL_TRAIT_Tr for S` | One per *overriding* implementation, holding that impl's counterpart body. |

Recognition is by the marker attributes, not by name, so a user-written
`_VERUS_VERIFIED_f` is an ordinary function.

## What each build mode compiles

| Mode | `cfg` | What the macro emits |
|---|---|---|
| Plain `cargo build` | neither `verus_keep_ghost` nor `verus_keep_ghost_body` | Nothing at all: the item is returned unchanged, with its original signature and body. No companion traits, no counterparts, no proof code. |
| `cargo verus build` | `verus_keep_ghost` | The stub keeps the real body and executes. The counterparts and companion traits are still emitted, but their bodies are cleared to `unimplemented!()` and nothing calls them. |
| Verification | `verus_keep_ghost_body` | The counterpart carries the body and specification; ordinary stubs use `unimplemented!()`. |

In verification mode `requires(false)` prevents verified code from calling the stub
directly. Const stubs retain their executable body for const evaluation, and external
specification proxies keep the call that identifies the target. The separate erase-mode
build retains the executable body under the original signature.

## The three stages, end to end

### Stage 1 — what the user writes

```rust
#[verus_spec(with Tracked(b): Tracked<u64>
    requires b == 1,
)]
fn f(a: u64) -> u64 {
    a
}

#[verus_spec]
fn caller() {
    proof_with!{Tracked(1u64)}
    let r = f(0);
}
```

### Stage 2 — after macro expansion

```rust
#[doc(hidden)]
#[verus::internal(unverified_stub)]
#[verifier::external_body]
fn f(a: u64) -> u64 {
    ::verus_builtin::requires([false]);
    _VERUS_VERIFIED_f(a, <Tracked<u64>>::assume_new())
}

#[verus::internal(verified_with)]
#[allow(non_snake_case)]
fn _VERUS_VERIFIED_f(a: u64, verus_tmp_b: Tracked<u64>) -> u64 {
    #[verus::internal(header_unwrap_parameter)] let b;
    #[verifier::proof_block] { b = verus_tmp_b.get() }
    ::verus_builtin::requires([b == 1]);
    a
}

fn caller() {
    let r = ::verus_builtin::proof_with_callee(
        f(0, Tracked(1u64)),
        f(0),
    );
}
```

The extras are appended to the counterpart's signature as real parameters, so the
`requires` clause and the body can name them the same way an ordinary parameter is named.
The call site appends them to the call, and passes the call a second time, as the
compiled program writes it, to the `proof_with_callee` marker. When ghost code is
erased, the macro emits just `f(0)`.

### Stage 3 — after the AST rewrite

After name resolution and before AST lowering (at the start of `construct_vir_crate`), the pass
redirects the first copy to the counterpart of the function it resolves to:

```rust
fn caller() {
    let r = ::verus_builtin::proof_with_callee(
        _VERUS_VERIFIED_f(0, Tracked(1u64)),
        f(0),
    );
}
```

rustc type checks *this*. Any mistake in the extras — wrong type, wrong arity, a borrow
that does not live long enough, a moved value used twice — is reported here as an
ordinary rustc error about `_VERUS_VERIFIED_f`.

The pass runs after name resolution, because the macro cannot resolve aliases, imports,
or method receivers during expansion, and before type checking, because that is what
makes rustc check the extras. It finds the counterpart from the callee's `DefId`
(`proof_with_ast_rewrite::ProofWithCtx::lookup_counterpart`), so aliased imports, re-exports, trait methods,
`assume_specification`s and imported crates all work. Renaming the callee is the pass's
only change; everything else is checked after type checking.

### The conformance check

Method calls and type-relative paths are only resolved by type checking, and the two
copies are type-checked separately. `rust_to_vir_expr::check_proof_with_callee` checks,
after type checking, that the second copy resolves to the function whose counterpart
the first copy calls (`proof_with_ast_rewrite::find_verified_counterpart`), with the same generic
arguments (closure types are mapped to the first copy's). The second copy is never
verified or run; it is erased, with its closures, before borrow checking.

It also checks (`proof_with_check::check_proof_with_args`) that the two copies have the
same receiver and arguments, as source code resolved the same way, so a hand-written
marker cannot verify one call and compile another.
A `with` function whose own generic is used only by ghost/tracked parameters or results
is rejected, since the executable call could not infer it.

`proof_with_callee` ties the result types of the two copies.

### What VIR sees

The counterpart is what carries the specification, so it is the item VIR verifies. To
keep diagnostics, `--verify-function` and profiler output naming the function the user
wrote, `rust_to_vir_path::with_fn_path` swaps the two names on the way into VIR:

```
_VERUS_VERIFIED_f   ->  f
f (the stub)        ->  _VERUS_UNVERIFIED_f
```

Both definitions and call sites pass through that mapping, and
`rust_to_vir_impl::translate_impl_item` names an impl method after the renamed
declaration so a trait method and its impls agree.

## The cases

### 1. Free function

The end-to-end example above.

### 2. Inherent method

The counterpart is a sibling in the same inherent impl, so it is found by ordinary method
resolution on the same receiver, with the same generics and the same `Self`.

```rust
// stage 2
impl A {
    #[verus::internal(unverified_stub)]
    fn m(&self) {
        ::verus_builtin::requires([false]);
        Self::_VERUS_VERIFIED_m(self, <Tracked<u64>>::assume_new())
    }

    #[verus::internal(verified_with)]
    fn _VERUS_VERIFIED_m(&self, verus_tmp_b: Tracked<u64>) { .. }
}

// stage 3
a._VERUS_VERIFIED_m(Tracked(1u64))
```

### 3. Trait method

A counterpart cannot be added to an external trait, and adding one to a local trait would
change its public signature and break every existing implementor. So the counterparts go
on generated **companion subtraits**, and every implementation is split in two.

There are two companions, because a single trait cannot be both blanket-implemented and
implemented per type:

- `_VERUS_VERIFIED_TRAIT_Tr` **declares** the counterparts and carries their
  specifications. It is blanket-implemented for every implementor of `Tr`, so a call can
  always name a counterpart without any extra bound. Its default body is the trait
  method's default body, or an `external_body` `unimplemented!()` stub when the trait
  method has none.
- `_VERUS_VERIFIED_IMPL_TRAIT_Tr` **carries the body** of an implementation that overrides
  the method. Its own defaults are assumed and never inherited, and an implementation that
  does not override the method generates nothing.

```rust
// stage 1
#[verus_verify]
trait Tr {
    #[verus_spec(with Tracked(b): Tracked<u64>)]
    fn m(&self, a: u64) -> u64 { DEFAULT }        // a default body is fine
}

#[verus_verify] impl Tr for S  { fn m(&self, a: u64) -> u64 { BODY } }
#[verus_verify] impl Tr for S2 { }

// stage 2
trait Tr {
    #[verus::internal(unverified_stub)]
    fn m(&self, a: u64) -> u64 { DEFAULT }        // requires(false)
}

#[verus::internal(verified_trait)]
trait _VERUS_VERIFIED_TRAIT_Tr: Tr {
    #[verus::internal(verified_with)]
    fn _VERUS_VERIFIED_m(&self, a: u64, verus_tmp_b: Tracked<u64>) -> u64 { DEFAULT }
}
impl<_VerusSelf: Tr + ?Sized> _VERUS_VERIFIED_TRAIT_Tr for _VerusSelf {}

trait _VERUS_VERIFIED_IMPL_TRAIT_Tr: Tr {
    #[verus::internal(verified_with)]
    #[verifier::external_body]
    fn _VERUS_VERIFIED_IMPL_m(&self, a: u64, verus_tmp_b: Tracked<u64>) -> u64 {
        unimplemented!()
    }
}

impl Tr for S {
    fn m(&self, a: u64) -> u64 {
        <Self as _VERUS_VERIFIED_IMPL_TRAIT_Tr>::_VERUS_VERIFIED_IMPL_m(
            self, a, <Tracked<u64>>::assume_new())
    }
}
impl _VERUS_VERIFIED_IMPL_TRAIT_Tr for S {
    fn _VERUS_VERIFIED_IMPL_m(&self, a: u64, verus_tmp_b: Tracked<u64>) -> u64 { BODY }
}

impl Tr for S2 { }                                // untouched

// stage 3
s._VERUS_VERIFIED_m(1, Tracked(1u64))
```

Because the blanket impl covers every implementor, a generic caller, a `dyn Tr` receiver,
and a concrete type all name the same counterpart, and the AST pass never has to change a
caller's bounds:

```rust
// stage 1
fn caller<A: Tr>(x: &A) -> u64 { proof_with!{Tracked(1u64)} x.m(1) }

// stage 3
fn caller<A: Tr>(x: &A) -> u64 { x._VERUS_VERIFIED_m(1, Tracked(1u64)) }
```

The price is that a call on a concrete type resolves to the *declaration*, so the
implementation's own contract would be lost at static dispatch. `fn_call_to_vir` pairs the
halves back up: when a call resolves to a counterpart declaration,
`proof_with_check::impl_counterpart` looks for an `_VERUS_VERIFIED_IMPL_TRAIT_Tr` implementation
of the receiver's type, and uses that method as the resolved target. Both counterparts
strip to the same VIR name, so the two halves line up as an ordinary trait method and its
implementation.

An implementation that overrides `m` but never reaches the macro would otherwise inherit
the assumed default silently. `check_verus_spec_with_overrides` rejects it: an
implementation that overrides a `with ..` method has to repeat the clause.

### 4. Extra outputs

The counterpart returns them, appended to the executable return value as one **flat**
tuple.

```rust
// stage 1
#[verus_spec(ret =>
    with Ghost(c): Ghost<u32> -> d: Ghost<u32>
    ensures ret == a, d@ == c,
)]
fn g(a: u64) -> u64 {
    proof_with!{|= Ghost(c)}
    a
}

#[verus_spec]
fn call_g() {
    proof_with!{Ghost(2u32) => Ghost(d)}
    let r = g(7);
}

// stage 2
#[verus::internal(verified_with)]
fn _VERUS_VERIFIED_g(a: u64, verus_tmp_c: Ghost<u32>) -> (u64, Ghost<u32>) {
    ..
    (a, Ghost(c))                                 // `|=` appends to the tail expression
}

fn call_g() {
    let r = ::verus_builtin::proof_with_callee(
        {
            let (__verus_tmp_expr_var__, Ghost(d)) = g(7, Ghost(2u32));
            proof!{ .. }
            __verus_tmp_expr_var__
        },
        g(7),
    );
}

// stage 3
let (__verus_tmp_expr_var__, Ghost(d)) = _VERUS_VERIFIED_g(7, Ghost(2u32));
```

`|= ..` rewrites the expression it follows into a tuple of that expression and the
supplied values, which is exactly the counterpart's return shape.

### 5. `assume_specification`

The specified function is foreign, so the counterpart stands beside the
`assume_specification` item. The `external_fn_specification` attribute stays on the stub —
whose body's trailing call names the external function — and the counterpart is
`external_body` with an `unimplemented!()` body, because its expanded signature cannot
name the external target directly.

`external_target_map` indexes the counterpart by the external function named in the
stub's trailing call, so a call to `ext(x)` under `proof_with!` is redirected to
`_VERUS_VERIFIED_ext_spec(x, ..)`.

### 6. `external_trait_specification`

The companion traits are generated beside the proxy, but made subtraits of the **external**
trait rather than of the proxy, found through the proxy's
`ExternalTraitSpecificationFor` member. `external_companion_traits` indexes companions
that come from other crates.

Everything else is case 3: the blanket impl covers every implementor of the external
trait, so an `impl T for S2 {}` that inherits `T::g`'s foreign default body generates
nothing and is still callable, and an implementation that overrides `g` puts its body in
`_VERUS_VERIFIED_IMPL_TRAIT_T`.

```rust
// stage 1
#[verifier::external]
trait T {
    fn g(&self) -> u64 { 2 }                      // a foreign default body
}

#[verus_verify]
#[verifier::external_trait_specification]
trait ExT {
    type ExternalTraitSpecificationFor: T;

    #[verus_spec(r =>
        with Tracked(b): Tracked<u64>
        requires b == 1,
        ensures r == 2,
    )]
    fn g(&self) -> u64;
}

#[verus_verify] impl T for S  { #[verus_spec(with Tracked(b): Tracked<u64>)]
                                fn g(&self) -> u64 { BODY } }
#[verus_verify] impl T for S2 { }

// stage 2
#[verifier::external_trait_specification]
trait ExT {
    type ExternalTraitSpecificationFor: T;
    #[verus::internal(unverified_stub)]
    fn g(&self) -> u64;                           // requires(false)
}

// the companions extend `T`, not `ExT`
#[verus::internal(verified_trait)]
trait _VERUS_VERIFIED_TRAIT_T: T {
    #[verus::internal(verified_with)]
    #[verifier::external_body]
    fn _VERUS_VERIFIED_g(&self, verus_tmp_b: Tracked<u64>) -> u64 {
        requires(b == 1); ensures(|r| r == 2);
        unimplemented!()
    }
}
impl<_VerusSelf: T + ?Sized> _VERUS_VERIFIED_TRAIT_T for _VerusSelf {}

trait _VERUS_VERIFIED_IMPL_TRAIT_T: T {
    #[verus::internal(verified_with)]
    #[verifier::external_body]
    fn _VERUS_VERIFIED_IMPL_g(&self, verus_tmp_b: Tracked<u64>) -> u64 {
        requires(b == 1); ensures(|r| r == 2);
        unimplemented!()
    }
}

impl T for S {
    fn g(&self) -> u64 {
        <Self as _VERUS_VERIFIED_IMPL_TRAIT_T>::_VERUS_VERIFIED_IMPL_g(
            self, <Tracked<u64>>::assume_new())
    }
}
impl _VERUS_VERIFIED_IMPL_TRAIT_T for S {
    fn _VERUS_VERIFIED_IMPL_g(&self, verus_tmp_b: Tracked<u64>) -> u64 { BODY }
}

impl T for S2 { }                                 // keeps the foreign default body

// stage 3
S._VERUS_VERIFIED_g(Tracked(1u64))                // redirected to `_VERUS_VERIFIED_IMPL_g`
S2._VERUS_VERIFIED_g(Tracked(1u64))               // stays on the assumed declaration
```

The declaration in `_VERUS_VERIFIED_TRAIT_T` is `external_body`, so it is an assumption in
exactly the way the proxy's own method is: `S2` runs foreign code that nothing verifies,
and the specification written on `ExT` is what verified callers get.

## Limitations

- **An implementation of a trait the macro never sees has no companion impl**, so a
  `proof_with!` call on it resolves to the assumed declaration rather than to its body.
  `check_verus_spec_with_overrides` catches the case Verus can see, an implementation that
  overrides a `with ..` method without repeating the clause.
- **The two counterpart names have to differ.** Both companion traits are in scope where
  they are generated and both may be implemented for the same type, so a shared method
  name would make the call ambiguous (E0034). Hence `_VERUS_VERIFIED_m` against
  `_VERUS_VERIFIED_IMPL_m`.
