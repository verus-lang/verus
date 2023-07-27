**Written 2023-07-27**

Traits mostly fall into two buckets:

 * Verified traits - traits known by Verus, may include spec/proof/exec functions, can be used generically
 * External traits - traits not known by Verus, can only be used if statically resolved. (These are particularly useful for traits that implement syntactic features, like Index, which are unlikely to be used generically)
  - [ ] Originally it looks like there was a check to prevent external traits from being
        used as trait bounds. However, the check for this is buggy
        (https://github.com/verus-lang/verus/issues/629). We either need to allow this
        after all, or re-classify some external traits as verified traits.

"Verified" vs "external" is currently determined by whether Verus finds a trait in its
Krate object. Thus, any trait marked `#[external]` or defined in an external crate
will count as an "external trait".
  - [ ] The way we do this classification likely needs to change when we support more std traits like `Clone`.

Verus currently allows the user to write implementations for external traits. The functions
inside are treated as normal functions.

There are also a number of special cases:

 * Marker traits (`Copy`, `Send`, `Sync`, `Sized`, `Unpin`, `Tuple`) - these are pretty much treated as external (though `Sized` has some complications)
 * `Fn`, `FnMut`, `FnOnce` and Verus `FnWithSpecification`
    * `FnWithSpecification` is defined in the `builtin` crate and is implemented for any type that implements `FnOnce`. `FnWithSpecification` is used to add `requires` and `ensures` spec functions to the function types. The 3 Rust traits are ignored, while conceptually, `FnWithSpecification` is a "verified trait" with 3 functions (spec requires, spec ensures, and the exec `call` function), though it isn't actually represented in VIR as a trait (unlike other verified traits).

### Expected Behaviors vs. current behaviors

 - External trait, external impl - Allowed, but calling one of its fns is disallowed
 - External trait, non-external impl, external fn - Allowed, but calling it is disallowed
 - External trait, verified impl - Allowed when calls are statically resolved
 - Verified trait, external impl - Allowed, but calling one of its fns is disallowed
   - [ ] TODO: fix panic
 - Verified trait, non-external impl, external f - Allowed, but calling it is disallowed
   - [ ] TODO: fix panic
 - Implement a marker trait - allowed (if unsafe, must be marked external)
 - Implement `FnWithSpecification` - disallowed
   - [ ] TODO: fix panic
 - impl Drop - should be disallowed until we have support
   - [ ] is currently unsound: https://github.com/verus-lang/verus/issues/723
 - impl FnOnce / Fn / FnMut - could be supported in principle, but probably not useful since there's no support
   - [ ] TODO: Verus currently lets you declare the impl, gives confusing error if you try to actually do the call

# Overall architecture

### Static resolution

In `fn_call_to_vir`, we identify trait functions and determine if they can be statically resolved.
If so, we include this information in the `CallTargetKind` AST object.

After the VIR Krate is constructed, we `vir/src/traits.rs`, we check all the trait functions 
(`Function` entries) and their calls (`Expr` nodes) and see if the trait is known in the VIR 
krate.  If not, then we replace the call with the static resolution and pretend that it
isn't a trait function at all. (If there is no static resolution in that case, it's an error.) 

### AIR Encoding of verified traits

TODO fill in

### AIR Encoding of associated types

TODO fill in

### Handling FnWithSpecification

Curerntly, FnWithSpecification is only handled for closure types, though support
for named function types ("FnDef types") is coming: https://github.com/verus-lang/verus/pull/565

There are 3 functions to consider:

 * The exec call function (when the user writes `f(a)`)
 * The spec functions, `requires` and `ensures`

For the exec call, we internally translate these calls into `exec_nonstatic_call`, defined
in `vstd`, which provides a precondition and postcondition.

 - [ ] Internally, Rust actually has 3 functions: `FnOnce::call_once`, `FnMut::call_mut`, and `Fn::call`. We currently collapse all 3 ways of calling into 1. This is certainly fine for `call_once` and `call` (the only difference is the `&`), but we may want to revisit `call_mut` after we have more general `&mut` support.

For the spec functions, in VIR we represent these as `BuiltinSpecFun::{ClosureReq, ClosureEns}`,
and in AIR as `closure_req` and `closure_ens`. (Bit of a misnomer, since in the future,
they'll apply to all function types, not just closures.)

Also, `closure_req` and `closure_ens` are special-cased to _not include the decoration
for the function type_. This is so we can seemlessly handle both `FnOnce::call_once` and
`Fn::call`.

# Termination checking

Right now we're considering spec/proof only, not exec-termination.

Conceptually, we think of traits as "like typeclasses in Coq". Specifically:

 * A trait is like the declaration of a record type.
 * A trait impl is a concrete instance of that record type.
 * Trait bounds (on functions or structs) are basically arguments of that record type.

For recursion checking, we need to check that everything can be defined in order.
We do this by creating a dependency graph and checking for cycles.

To do this checking, we need to know, for each call, which record instances get passed
in to satisfy the type bounds. This information is stored in the `ExprX::Call` node's `ImplPaths`
argument.

Special cases:

 * FnWithSpecification
   * Closures are easiest because Rust already prevents cyclicity with closures
   * For FnDef types (#565) we can define the record for a trait implementation
      `foo: FnWithSpecification` (for an exec function `foo`)
      when we define the `requires` and `ensures` of `foo`.

 * Marker traits
   * `Copy`, `Send`, `Sync`, `Sized`, `Unpin`, `Tuple` can all be ignored. This is fine since these traits don't have any functions.
 * External traits
   * Currently ignored. This could have implications for exec termination checking but shouldn't matter for spec termination checking. 

# Other considerations

### `broadcast_forall`

Currently no plan for handling trait bounds. Trait bounds are disallowed except for `Sized`
bounds which are implicit everywhere.

### `Sized`

Ideally we'd like to do:

```rust
#[broadcast_forall]
fn size_of_reference_type<V: Sized>()
  ensures size_of::<&V>() == size_of::<usize>()
```

Unfortunately we cannot because the `Sized` bounds are ignored. The current plan is to
not rely on `Sized` bounds at all and instead use a `is_sized::<V>() -> bool` function.

### Trait bound consistency

There are a few places where we need to check that two functions have the same function signatures, and therefore the same trait bounds:

 * `external_fn_specification` or `external_type_specification`
   * We check that the trait bounds match exactly, using `rustc_middle`'s `Predicate` objects.
     (But we might need to add special handling for https://github.com/verus-lang/verus/issues/656)
 * `when_used_as_spec`
   * Currently checked at VIR level. Marker traits and external traits are ignored at this point, as are function traits. Might be a good idea to change this check to be at the rustc level
     like the `external_fn_specification` checks.

### Drop

No plans regarding Drop support
