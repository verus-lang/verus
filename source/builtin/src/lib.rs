#![no_std]
#![allow(internal_features)]
#![cfg_attr(
    verus_keep_ghost,
    feature(rustc_attrs),
    feature(negative_impls),
    feature(unboxed_closures),
    feature(fn_traits),
    feature(register_tool),
    feature(tuple_trait),
    register_tool(verus),
    register_tool(verifier)
)]

use core::marker::PhantomData;

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::admit"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn admit() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::no_method_body"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn no_method_body() -> ! {
    unimplemented!()
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::requires"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn requires<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::ensures"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn ensures<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::returns"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn returns<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of spec function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::recommends"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn recommends<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of loop body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::invariant_except_break"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn invariant_except_break<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of loop body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::invariant"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn invariant<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::decreases"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn decreases<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
// decrease_when is automatically added to list of recommends
#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[rustc_diagnostic_item = "verus::verus_builtin::decreases_when"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn decreases_when(_b: bool) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::decreases_by"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn decreases_by<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::recommends_by"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn recommends_by<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::extra_dependency"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn extra_dependency<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::opens_invariants_none"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn opens_invariants_none() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::opens_invariants_any"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn opens_invariants_any() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::opens_invariants"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn opens_invariants<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::opens_invariants_except"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn opens_invariants_except<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::opens_invariants_set"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn opens_invariants_set<A>(_a: A) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::no_unwind"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn no_unwind() {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::no_unwind_when"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn no_unwind_when(_b: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::reveal_hide"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub const fn reveal_hide_(_f: fn(), _n: u32) {}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::reveal_hide_internal_path"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn reveal_hide_internal_path_<A>(_x: A) {
    unimplemented!();
}

/// Mark an ensures clause in a trait as applying just to the default implementation,
/// not the trait declaration in general
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::default_ensures"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn default_ensures(_b: bool) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::imply"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn imply(_b1: bool, _b2: bool) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::forall"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn forall<A>(_a: A) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::exists"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn exists<A>(_a: A) -> bool {
    unimplemented!();
}

// choose(|x: t| P(x))
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::choose"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn choose<A, F: Fn(A) -> bool>(_f: F) -> A {
    unimplemented!()
}

// let (x1, ..., xn): (t1, ..., tn) = choose_tuple(|x1: t1, ..., xn: tn| P(x1, ..., xn));
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::choose_tuple"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn choose_tuple<A, F>(_f: F) -> A {
    unimplemented!()
}

// used by with_triggers! macro
// example: forall with three triggers [f(x), g(y)], [h(x, y)], [m(y, x)]:
//   forall( |x: int, y: int| with_triggers(  ( (f(x), g(y)), (h(x, y),), (m(y, x),) )  ,  body  ) )
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::with_triggers"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn with_triggers<A, B>(_triggers_tuples: A, body: B) -> B {
    body
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::constrain_type"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn constrain_type<T>(_x: T, _y: T) -> bool {
    true
}

// example: forall with three triggers [f(x), g(y)], [h(x, y)], [m(y, x)]:
//   forall(|x: int, y: int| with_triggers!([f(x), g(y)], [h(x, y)], [m(y, x)] => body))
#[macro_export]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
macro_rules! with_triggers {
    ( $([ $($term:expr),* ]),* => $body:expr) => {
        {
            with_triggers(( $( ( $( $term, )* ), )* ), $body)
        }
    }
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::equal"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn equal<A>(_: A, _: A) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::ext_equal"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn ext_equal<A>(_: A, _: A) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::ext_equal_deep"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn ext_equal_deep<A>(_: A, _: A) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::old"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn old<A: ?Sized>(_: &mut A) -> &mut A {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::is_variant"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn is_variant<Adt>(_a: Adt, _variant: &str) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::get_variant_field"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn get_variant_field<Adt, Field>(_a: Adt, _variant: &str, _field: &str) -> Field {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::get_union_field"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn get_union_field<Adt, Field>(_a: Adt, _field: &str) -> Field {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assume_"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assume_(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_by"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_by(_: bool, _: ()) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_by_compute"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_by_compute(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_by_compute_only"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_by_compute_only(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_nonlinear_by"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_nonlinear_by(_: ()) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_bitvector_by"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_bitvector_by(_: ()) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_forall_by"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_forall_by<A>(_a: A) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_bit_vector"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn assert_bit_vector(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::use_type_invariant"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn use_type_invariant<A>(_a: A) {
    unimplemented!();
}

//
// Ghost, Tracked
//

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::Ghost")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types_in_ground_variants(A))]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct Ghost<A> {
    phantom: PhantomData<A>,
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::Tracked")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types_in_ground_variants(A))]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct Tracked<A> {
    phantom: PhantomData<A>,
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<A> core::fmt::Debug for Tracked<A> {
    fn fmt(&self, _: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Ok(())
    }
}

impl<A> Ghost<A> {
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Ghost::view"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    pub fn view(self) -> A {
        unsafe { core::mem::MaybeUninit::uninit().assume_init() }
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Ghost::new"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    #[verifier::external_body]
    pub const fn new(_a: A) -> Ghost<A> {
        core::mem::forget(_a);
        Ghost { phantom: PhantomData }
    }

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[inline(always)]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
    pub const fn assume_new() -> Self {
        Ghost { phantom: PhantomData }
    }

    // The argument here is used as part of a trick to avoid
    // type inference errors when erasing code.

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[inline(always)]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
    pub const fn assume_new_fallback(_: fn() -> A) -> Self {
        Ghost { phantom: PhantomData }
    }

    // note that because we return #[verifier::spec], not #[verifier::exec], we do not implement the Borrow trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Ghost::borrow"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    #[verifier::external_body]
    // #[allow(fuzzy_provenance_casts)]
    pub fn borrow(&self) -> &A {
        #[allow(deref_nullptr)]
        unsafe {
            &*(0 as *const A)
        }
    }

    // note that because we return #[verifier::spec], not #[verifier::exec], we do not implement the BorrowMut trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Ghost::borrow_mut"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::proof]
    #[verifier::external]
    // #[allow(fuzzy_provenance_casts)]
    pub fn borrow_mut(#[verifier::proof] &mut self) -> &mut A {
        #[allow(deref_nullptr)]
        unsafe {
            &mut *(0 as *mut A)
        }
    }
}

impl<A> Tracked<A> {
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Tracked::view"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    pub fn view(self) -> A {
        unsafe { core::mem::MaybeUninit::uninit().assume_init() }
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Tracked::new"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::proof]
    #[verifier::external_body]
    pub const fn new(#[verifier::proof] _a: A) -> Tracked<A> {
        core::mem::forget(_a);
        Tracked { phantom: PhantomData }
    }

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[inline(always)]
    pub const fn assume_new() -> Self {
        Tracked { phantom: PhantomData }
    }

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[inline(always)]
    pub const fn assume_new_fallback(_: fn() -> A) -> Self {
        Tracked { phantom: PhantomData }
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Tracked::get"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::proof]
    #[verifier::external_body]
    #[verifier::returns(proof)]
    pub const fn get(#[verifier::proof] self) -> A {
        unsafe { core::mem::MaybeUninit::uninit().assume_init() }
    }

    // note that because we return #[verifier::proof], not #[verifier::exec], we do not implement the Borrow trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Tracked::borrow"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::proof]
    #[verifier::external_body]
    #[verifier::returns(proof)]
    // #[allow(fuzzy_provenance_casts)]
    pub fn borrow(#[verifier::proof] &self) -> &A {
        #[allow(deref_nullptr)]
        unsafe {
            &*(0 as *const A)
        }
    }

    // note that because we return #[verifier::proof], not #[verifier::exec], we do not implement the BorrowMut trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::Tracked::borrow_mut"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::proof]
    #[verifier::external_body]
    #[verifier::returns(proof)]
    // #[allow(fuzzy_provenance_casts)]
    pub fn borrow_mut(#[verifier::proof] &mut self) -> &mut A {
        #[allow(deref_nullptr)]
        unsafe {
            &mut *(0 as *mut A)
        }
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<A> Clone for Ghost<A> {
    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[inline(always)]
    fn clone(&self) -> Self {
        Ghost { phantom: PhantomData }
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<A> Copy for Ghost<A> {}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<A: Copy> Clone for Tracked<A> {
    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[inline(always)]
    fn clone(&self) -> Self {
        Tracked { phantom: PhantomData }
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<A: Copy> Copy for Tracked<A> {}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::ghost_exec"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::external_body]
pub const fn ghost_exec<A>(#[verifier::spec] _a: A) -> Ghost<A> {
    core::mem::forget(_a);
    Ghost::assume_new()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::tracked_exec"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::external_body]
pub const fn tracked_exec<A>(#[verifier::proof] _a: A) -> Tracked<A> {
    core::mem::forget(_a);
    Tracked::assume_new()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::tracked_exec_borrow"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::external_body]
pub fn tracked_exec_borrow<'a, A>(#[verifier::proof] _a: &'a A) -> &'a Tracked<A> {
    // TODO: implement this (using unsafe) or mark function as ghost (if supported by Rust)
    unimplemented!();
}

//
// int and nat
//

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::int")]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct int;

// TODO: we should eventually be able to remove this and other int/nat ops,
// since we now have SpecAdd, etc.
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Add for int {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Sub for int {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Mul for int {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Div for int {
    type Output = Self;
    fn div(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Rem for int {
    type Output = Self;
    fn rem(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Neg for int {
    type Output = Self;
    fn neg(self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl PartialEq for int {
    fn eq(&self, _other: &Self) -> bool {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl Eq for int {}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::cmp::PartialOrd for int {
    fn partial_cmp(&self, _other: &Self) -> Option<core::cmp::Ordering> {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::cmp::Ord for int {
    fn cmp(&self, _other: &Self) -> core::cmp::Ordering {
        unimplemented!()
    }
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::nat")]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct nat;

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Add for nat {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Sub for nat {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Mul for nat {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Div for nat {
    type Output = Self;
    fn div(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::ops::Rem for nat {
    type Output = Self;
    fn rem(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl PartialEq for nat {
    fn eq(&self, _other: &Self) -> bool {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl Eq for nat {}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::cmp::PartialOrd for nat {
    fn partial_cmp(&self, _other: &Self) -> Option<core::cmp::Ordering> {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl core::cmp::Ord for nat {
    fn cmp(&self, _other: &Self) -> core::cmp::Ordering {
        unimplemented!()
    }
}

//
// Structural
//

/// derive(Structural) means that exec-mode == and ghost == always yield the same result.
/// derive(Structural) is only allowed when all the fields of a type are also Structural.
/// derive(StructuralEq) means derive(Structural) and also implement PartialEqSpec,
/// setting eq_spec to == and obeys_eq_spec to true.
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::Structural")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub unsafe trait Structural {
    #[doc(hidden)]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    fn assert_receiver_is_structural(&self) -> () {}
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<S: Structural + ?Sized> Structural for &S {
    #[doc(hidden)]
    fn assert_receiver_is_structural(&self) -> () {
        S::assert_receiver_is_structural(self)
    }
}

#[doc(hidden)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct AssertParamIsStructural<T: Structural + ?Sized> {
    _field: core::marker::PhantomData<T>,
}

macro_rules! impl_structural {
    ($($t:ty)*) => {
        $(
            #[stable(feature = "needed_for_compilation", since = "1.88.0")]
            unsafe impl Structural for $t { }
        )*
    }
}

impl_structural! {
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
    // TODO: support f32 f64 ?
    bool char
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T: Structural> Structural for Option<T> {}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct NoCopy {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl !Copy for NoCopy {}

#[cfg(verus_keep_ghost)]
#[derive(Clone, Copy)]
struct NoSyncSend {}
#[cfg(verus_keep_ghost)]
impl !Sync for NoSyncSend {}
#[cfg(verus_keep_ghost)]
impl !Send for NoSyncSend {}

// TODO: remove this when !Sync, !Send are supported by stable Rust
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Copy)]
struct NoSyncSend {
    _no_send_sync: core::marker::PhantomData<*const ()>,
}

// Used by verus_state_machines_macros codegen
#[doc(hidden)]
#[allow(dead_code)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct SyncSendIfSyncSend<T> {
    no_sync_send: NoSyncSend,
    t: core::marker::PhantomData<T>,
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T: Sync + Send> Sync for SyncSendIfSyncSend<T> {}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T: Sync + Send> Send for SyncSendIfSyncSend<T> {}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<T> Clone for SyncSendIfSyncSend<T> {
    fn clone(&self) -> Self {
        unimplemented!();
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<T> Copy for SyncSendIfSyncSend<T> {}

// Used by Invariant lib

#[doc(hidden)]
#[allow(dead_code)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct SendIfSend<T> {
    no_sync_send: NoSyncSend,
    t: core::marker::PhantomData<T>,
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T: Send> Send for SendIfSend<T> {}

#[doc(hidden)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct SyncSendIfSend<T> {
    no_sync_send: NoSyncSend,
    t: core::marker::PhantomData<T>,
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T: Send> Sync for SyncSendIfSend<T> {}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T: Send> Send for SyncSendIfSend<T> {}

impl<T> SyncSendIfSend<T> {
    #[cfg(verus_keep_ghost)]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    pub fn assume_new() -> Self {
        SyncSendIfSend { no_sync_send: NoSyncSend {}, t: PhantomData }
    }
    #[cfg(not(verus_keep_ghost))]
    pub fn assume_new() -> Self {
        SyncSendIfSend {
            no_sync_send: NoSyncSend { _no_send_sync: Default::default() },
            t: PhantomData,
        }
    }
}

#[doc(hidden)]
#[allow(dead_code)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct AlwaysSyncSend<T> {
    t: core::marker::PhantomData<T>,
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T> Sync for AlwaysSyncSend<T> {}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<T> Send for AlwaysSyncSend<T> {}

impl<T> AlwaysSyncSend<T> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    pub fn assume_new() -> Self {
        AlwaysSyncSend { t: PhantomData }
    }
}

//
// Integers
//

// Marker for integer types (i8 ... u128, isize, usize, nat, int)
// so that we get reasonable type error messages when someone uses a non-Integer type
// in an arithmetic operation.
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::Integer")]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub unsafe trait Integer: Copy {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    const CONST_DEFAULT: Self;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for u8 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for u16 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for u32 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for u64 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for u128 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for usize {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for i8 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for i16 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for i32 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for i64 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for i128 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for isize {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for int {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = int;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for nat {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = nat;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Integer for char {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = ' ';
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub unsafe trait Boolean: Copy {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    const CONST_DEFAULT: Self;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl Boolean for bool {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = false;
}

// spec literals of the form "33", which could have any Integer type
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_literal_integer"]
#[allow(non_camel_case_types)]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const fn spec_literal_integer<
    hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat: Integer,
>(
    _s: &str,
) -> hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat {
    hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat::CONST_DEFAULT
}

// spec literals of the form "33int",
// or spec literals in positions syntactically expected to be int (e.g. in "x + 33")
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_literal_int"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const fn spec_literal_int(_s: &str) -> int {
    int
}

// spec literals of the form "33nat"
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_literal_nat"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const fn spec_literal_nat(_s: &str) -> nat {
    nat
}

// Fixed-width add
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::add"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const fn add<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    IntegerType::CONST_DEFAULT
}

// Fixed-width sub
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::sub"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const fn sub<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    IntegerType::CONST_DEFAULT
}

// Fixed-width mul
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::mul"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const fn mul<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    IntegerType::CONST_DEFAULT
}

// represent "expr as typ", including converting to and from int and nat
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_cast_integer"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const fn spec_cast_integer<From: Copy, To: Integer>(_from: From) -> To {
    To::CONST_DEFAULT
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_eq"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_eq<Lhs, Rhs>(_lhs: Lhs, _rhs: Rhs) -> bool {
    unimplemented!()
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecOrd<Rhs = Self> {
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecOrd::spec_lt"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_lt(self, rhs: Rhs) -> bool;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecOrd::spec_le"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_le(self, rhs: Rhs) -> bool;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecOrd::spec_gt"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_gt(self, rhs: Rhs) -> bool;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecOrd::spec_ge"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_ge(self, rhs: Rhs) -> bool;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecNeg {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecNeg::spec_neg"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_neg(self) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecAdd<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecAdd::spec_add"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_add(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecSub<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecSub::spec_sub"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_sub(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecMul<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecMul::spec_mul"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_mul(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecEuclideanDiv<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecEuclideanDiv::spec_euclidean_div"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_euclidean_div(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecEuclideanMod<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecEuclideanMod::spec_euclidean_mod"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_euclidean_mod(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecBitAnd<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecBitAnd::spec_bitand"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_bitand(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecBitOr<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecBitOr::spec_bitor"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_bitor(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecBitXor<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecBitXor::spec_bitxor"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_bitxor(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecShl<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecShl::spec_shl"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_shl(self, rhs: Rhs) -> Self::Output;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait SpecShr<Rhs = Self> {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::verus_builtin::SpecShr::spec_shr"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    #[verifier::spec]
    fn spec_shr(self, rhs: Rhs) -> Self::Output;
}

// Chained inequalities x <= y < z
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct SpecChain {
    data: PhantomData<int>,
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_chained_value"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_chained_value<IntegerType: Integer>(_a: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_chained_le"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_chained_le<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_chained_lt"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_chained_lt<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_chained_ge"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_chained_ge<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_chained_gt"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_chained_gt<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_chained_cmp"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_chained_cmp(_chain: SpecChain) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::spec_chained_eq"]
#[verifier::spec]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn spec_chained_eq<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

macro_rules! impl_ord {
    ([$($t:ty)*]) => {
        $(
            #[stable(feature = "needed_for_compilation", since = "1.88.0")]
            impl<Rhs: Integer> SpecOrd<Rhs> for $t {
                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_lt(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_le(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_gt(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_ge(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_unary_op {
    ($trt:ident, $fun:ident, $ret:ty, [$($t:ty)*]) => {
        $(
            #[stable(feature = "needed_for_compilation", since = "1.88.0")]
            impl $trt for $t {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_binary_op {
    ($trt:ident, $fun:ident, $ret:ty, [$($t:ty)*]) => {
        $(
            #[stable(feature = "needed_for_compilation", since = "1.88.0")]
            impl<Rhs: Integer> $trt<Rhs> for $t {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self, _rhs: Rhs) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_binary_op_nat {
    ($trt:ident, $fun:ident, $ret:ty, [$($t:ty)*]) => {
        $(
            #[stable(feature = "needed_for_compilation", since = "1.88.0")]
            impl $trt<$t> for nat {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self, _rhs: $t) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_binary_op_rhs {
    ($trt:ident, $fun:ident, $rhs: ty, $ret:ty, [$($t:ty)*]) => {
        $(
            #[stable(feature = "needed_for_compilation", since = "1.88.0")]
            impl $trt<$rhs> for $t {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self, _rhs: $rhs) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

impl_ord!([
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
    char
]);

impl_unary_op!(SpecNeg, spec_neg, int, [
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecAdd, spec_add, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_nat!(SpecAdd, spec_add, nat, [nat]);

impl_binary_op_nat!(SpecAdd, spec_add, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecSub, spec_sub, int, [
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecMul, spec_mul, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_nat!(SpecMul, spec_mul, nat, [nat]);

impl_binary_op_nat!(SpecMul, spec_mul, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecEuclideanDiv, spec_euclidean_div, Self, Self, [
    int nat
    usize u8 u16 u32 u64 u128
]);

impl_binary_op_rhs!(SpecEuclideanDiv, spec_euclidean_div, Self, int, [
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecEuclideanMod, spec_euclidean_mod, Self, Self, [
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecBitAnd, spec_bitand, Self, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecBitOr, spec_bitor, Self, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecBitXor, spec_bitxor, Self, Self, [
    bool
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecShl, spec_shl, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecShr, spec_shr, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

#[cfg(verus_keep_ghost)]
#[verifier::spec]
#[rustc_diagnostic_item = "verus::verus_builtin::f32_to_bits"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn f32_to_bits(_f: f32) -> u32 {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[verifier::spec]
#[rustc_diagnostic_item = "verus::verus_builtin::f64_to_bits"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn f64_to_bits(_f: f64) -> u64 {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::strslice_is_ascii"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn strslice_is_ascii<A>(_a: A) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::strslice_len"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn strslice_len<A>(_a: A) -> nat {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::strslice_get_char"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn strslice_get_char<A>(_a: A, _i: int) -> char {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::reveal_strlit"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn reveal_strlit<A>(_a: A) {
    unimplemented!()
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::FnSpec")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct FnSpec<Args, Output> {
    phantom: PhantomData<(Args, Output)>,
}

#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<Args: core::marker::Tuple, Output> FnOnce<Args> for FnSpec<Args, Output> {
    type Output = Output;
    extern "rust-call" fn call_once(self, _: Args) -> <Self as FnOnce<Args>>::Output {
        todo!()
    }
}

#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<Args: core::marker::Tuple, Output> FnMut<Args> for FnSpec<Args, Output> {
    extern "rust-call" fn call_mut(&mut self, _: Args) -> <Self as FnOnce<Args>>::Output {
        todo!()
    }
}

#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<Args: core::marker::Tuple, Output> Fn<Args> for FnSpec<Args, Output> {
    extern "rust-call" fn call(&self, _: Args) -> <Self as FnOnce<Args>>::Output {
        todo!()
    }
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::closure_to_fn_spec"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn closure_to_fn_spec<Args: core::marker::Tuple, F: FnOnce<Args>>(
    _f: F,
) -> FnSpec<Args, F::Output> {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::call_requires"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn call_requires<Args: core::marker::Tuple, F: FnOnce<Args>>(_f: F, _args: Args) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::call_ensures"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn call_ensures<Args: core::marker::Tuple, F: FnOnce<Args>>(
    _f: F,
    _args: Args,
    _output: F::Output,
) -> bool {
    unimplemented!();
}

// Support for proof_fn

/// FnProof is the type of proof closures; the syntax proof_fn is used to wrap FnProof
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::FnProof")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct FnProof<'a, Options, ArgModes, OutMode, Args, Output> {
    _no_sync_send: NoSyncSend,
    _lifetime: PhantomData<&'a fn(Args) -> Output>,
    _options: PhantomData<Options>,
    _arg_modes: PhantomData<ArgModes>,
    _out_mode: PhantomData<OutMode>,
}

#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::FOpts")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct FOpts<const USAGE: u8, ReqEns, const COPY: u8, const SEND: u8, const SYNC: u8> {
    _no_sync_send: NoSyncSend,
    _req_ens: PhantomData<ReqEns>,
}

// Note: the names Trk and RqEn are kept short;
// otherwise, Rust will create a "*.long-type-*" file whenever there is a type error involving
// FnProof<...> that doesn't fit into a short enough string.
// For further brevity, integers are used for USAGE, COPY, SEND, SYNC,
// and () is used as the type to indicate "not tracked" or "no ReqEns".

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const PROOF_FN_ONCE: u8 = 1;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const PROOF_FN_MUT: u8 = 2;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const PROOF_FN: u8 = 3;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const PROOF_FN_COPY: u8 = 4;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const PROOF_FN_SEND: u8 = 5;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub const PROOF_FN_SYNC: u8 = 6;

// tracked
#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::Trk")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct Trk;

// ReqEns
#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::RqEn")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct RqEn<R>(PhantomData<R>);

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::ProofFnOnce")]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ProofFnOnce {}
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::ProofFnMut")]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ProofFnMut: ProofFnOnce {}
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::ProofFn")]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ProofFn: ProofFnMut {}

// We define ProofFnReqEns<R> as a wrapper around a trait with an associated type,
// because the broadcast lemma for ProofFnReqEns needs an associated type to trigger properly
// (it can't be directly generic over ReqEns)
#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ProofFnReqEnsAssoc {
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    type ReqEns;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ProofFnReqEns<R>: ProofFnReqEnsAssoc<ReqEns = R> {}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ProofFnReqEnsDef<Args, Output> {
    #[cfg(verus_keep_ghost)]
    #[verifier::spec]
    #[rustc_diagnostic_item = "verus::verus_builtin::ProofFnReqEnsDef::req"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    fn req(_args: Args) -> bool;

    #[cfg(verus_keep_ghost)]
    #[verifier::spec]
    #[rustc_diagnostic_item = "verus::verus_builtin::ProofFnReqEnsDef::ens"]
    #[stable(feature = "needed_for_compilation", since = "1.88.0")]
    fn ens(_args: Args, _output: Output) -> bool;
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<const USAGE: u8, ReqEns, const COPY: u8, const SEND: u8, const SYNC: u8> ProofFnOnce
    for FOpts<USAGE, ReqEns, COPY, SEND, SYNC>
{
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<ReqEns, const COPY: u8, const SEND: u8, const SYNC: u8> ProofFnMut
    for FOpts<PROOF_FN_MUT, ReqEns, COPY, SEND, SYNC>
{
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<ReqEns, const COPY: u8, const SEND: u8, const SYNC: u8> ProofFnMut
    for FOpts<PROOF_FN, ReqEns, COPY, SEND, SYNC>
{
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<ReqEns, const COPY: u8, const SEND: u8, const SYNC: u8> ProofFn
    for FOpts<PROOF_FN, ReqEns, COPY, SEND, SYNC>
{
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<const USAGE: u8, R, const COPY: u8, const SEND: u8, const SYNC: u8> ProofFnReqEnsAssoc
    for FOpts<USAGE, RqEn<R>, COPY, SEND, SYNC>
{
    type ReqEns = R;
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<const USAGE: u8, R, const COPY: u8, const SEND: u8, const SYNC: u8> ProofFnReqEns<R>
    for FOpts<USAGE, RqEn<R>, COPY, SEND, SYNC>
{
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<const USAGE: u8, ReqEns, const SEND: u8, const SYNC: u8> Clone
    for FOpts<USAGE, ReqEns, PROOF_FN_COPY, SEND, SYNC>
{
    fn clone(&self) -> Self {
        unimplemented!()
    }
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<const USAGE: u8, ReqEns, const SEND: u8, const SYNC: u8> Copy
    for FOpts<USAGE, ReqEns, PROOF_FN_COPY, SEND, SYNC>
{
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<const USAGE: u8, ReqEns, const COPY: u8, const SYNC: u8> Send
    for FOpts<USAGE, ReqEns, COPY, PROOF_FN_SEND, SYNC>
{
}
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<const USAGE: u8, ReqEns, const COPY: u8, const SEND: u8> Sync
    for FOpts<USAGE, ReqEns, COPY, SEND, PROOF_FN_SYNC>
{
}

#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<'a, Options: ProofFnOnce, ArgModes, OutMode, Args: core::marker::Tuple, Output> FnOnce<Args>
    for FnProof<'a, Options, ArgModes, OutMode, Args, Output>
{
    type Output = Output;
    extern "rust-call" fn call_once(self, _: Args) -> <Self as FnOnce<Args>>::Output {
        unimplemented!()
    }
}

#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<'a, Options: ProofFnMut, ArgModes, OutMode, Args: core::marker::Tuple, Output> FnMut<Args>
    for FnProof<'a, Options, ArgModes, OutMode, Args, Output>
{
    extern "rust-call" fn call_mut(&mut self, _: Args) -> <Self as FnOnce<Args>>::Output {
        unimplemented!()
    }
}

#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<'a, Options: ProofFn, ArgModes, OutMode, Args: core::marker::Tuple, Output> Fn<Args>
    for FnProof<'a, Options, ArgModes, OutMode, Args, Output>
{
    extern "rust-call" fn call(&self, _: Args) -> <Self as FnOnce<Args>>::Output {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<'a, Options: Copy, ArgModes, OutMode, Args, Output> Clone
    for FnProof<'a, Options, ArgModes, OutMode, Args, Output>
{
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<'a, Options: Copy, ArgModes, OutMode, Args, Output> Copy
    for FnProof<'a, Options, ArgModes, OutMode, Args, Output>
{
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<'a, Options: Send, ArgModes, OutMode, Args, Output> Send
    for FnProof<'a, Options, ArgModes, OutMode, Args, Output>
{
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
unsafe impl<'a, Options: Sync, ArgModes, OutMode, Args, Output> Sync
    for FnProof<'a, Options, ArgModes, OutMode, Args, Output>
{
}

#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ConfirmUsage<Args, Output, const USAGE: u8, F> {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<Args: core::marker::Tuple, Output, F: FnOnce<Args, Output = Output>>
    ConfirmUsage<Args, Output, PROOF_FN_ONCE, F> for ProofFnConfirm
{
}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<Args: core::marker::Tuple, Output, F: FnMut<Args, Output = Output>>
    ConfirmUsage<Args, Output, PROOF_FN_MUT, F> for ProofFnConfirm
{
}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<Args: core::marker::Tuple, Output, F: Fn<Args, Output = Output>>
    ConfirmUsage<Args, Output, PROOF_FN, F> for ProofFnConfirm
{
}

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct ProofFnConfirm;

#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ConfirmCopy<const COPY: u8, F> {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<F: Copy> ConfirmCopy<PROOF_FN_COPY, F> for ProofFnConfirm {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<F> ConfirmCopy<0, F> for ProofFnConfirm {}

#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ConfirmSend<const SEND: u8, F> {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<F: Send> ConfirmSend<PROOF_FN_SEND, F> for ProofFnConfirm {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<F> ConfirmSend<0, F> for ProofFnConfirm {}

#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ConfirmSync<const SYNC: u8, F> {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<F: Sync> ConfirmSync<PROOF_FN_SYNC, F> for ProofFnConfirm {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl<F> ConfirmSync<0, F> for ProofFnConfirm {}

#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub trait ConfirmTracked {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl ConfirmTracked for Trk {}
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
impl ConfirmTracked for () {}

// Note: Rust can check the well-formedness of all the type arguments except ArgModes;
// we check ArgModes in the conversion to VIR
#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::verus_builtin::closure_to_fn_proof")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn closure_to_fn_proof<
    'a,
    const USAGE: u8,
    const COPY: u8,
    const SEND: u8,
    const SYNC: u8,
    ArgModes,
    OutMode,
    Args,
    Output,
    F: 'a,
>(
    _f: F,
) -> FnProof<'a, FOpts<USAGE, (), COPY, SEND, SYNC>, ArgModes, OutMode, Args, Output>
where
    ProofFnConfirm: ConfirmUsage<Args, Output, USAGE, F>,
    ProofFnConfirm: ConfirmCopy<COPY, F>,
    ProofFnConfirm: ConfirmSend<SEND, F>,
    ProofFnConfirm: ConfirmSync<SYNC, F>,
    ArgModes: core::marker::Tuple,
    OutMode: ConfirmTracked,
    Args: core::marker::Tuple,
{
    unimplemented!()
}

// Intrinsics defined in the AIR prelude related to word-sizes and bounded ints
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::unsigned_max"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn unsigned_max(_word_bits: nat) -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::signed_min"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn signed_min(_word_bits: nat) -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::signed_max"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn signed_max(_word_bits: nat) -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::arch_word_bits"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn arch_word_bits() -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::is_smaller_than"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn is_smaller_than<A, B>(_: A, _: B) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::is_smaller_than_lexicographic"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn is_smaller_than_lexicographic<A, B>(_: A, _: B) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::is_smaller_than_recursive_function_field"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn is_smaller_than_recursive_function_field<A, B>(_: A, _: B) -> bool {
    unimplemented!();
}

#[macro_export]
#[cfg(not(verus_verify_core))]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
macro_rules! decreases_to_internal {
    ($($x:expr),* $(,)? => $($y:expr),* $(,)?) => {
        $crate::is_smaller_than_lexicographic(($($y,)*), ($($x,)*))
    }
}

/// decreases_to!(b => a) means that height(a) < height(b), so that b can decrease to a
/// in decreases clauses.
/// decreases_to!(b1, ..., bn => a1, ..., am) can compare lexicographically ordered values,
/// which can be useful when making assertions about decreases clauses.
/// Notes:
/// - decreases_to! desugars to a call to is_smaller_than_lexicographic.
/// - you can write #[trigger](decreases_to!(b => a)) to trigger on height(a).
///   (in the SMT encoding, height is a function call and is a useful trigger,
///   while is_smaller_than/is_smaller_than_lexicographic is not a function call
///   and is not a useful trigger.)
#[macro_export]
#[cfg(not(verus_verify_core))]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
macro_rules! decreases_to {
    ($($x:tt)*) => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::decreases_to_internal!($($x)*))
    };
}

#[macro_export]
#[cfg(verus_verify_core)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
macro_rules! decreases_to_internal {
    ($($x:expr),* $(,)? => $($y:expr),* $(,)?) => {
        $crate::verus_builtin::is_smaller_than_lexicographic(($($y,)*), ($($x,)*))
    }
}

#[macro_export]
#[cfg(verus_verify_core)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
macro_rules! decreases_to {
    ($($x:tt)*) => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::verus_builtin::decreases_to_internal!($($x)*))
    };
}

#[cfg(verus_verify_core)]
pub use decreases_to;
#[cfg(verus_verify_core)]
pub use decreases_to_internal;

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::infer_spec_for_loop_iter"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn infer_spec_for_loop_iter<A>(_: A, _: A, _print_hint: bool) -> Option<A> {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::global_size_of"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[rustc_const_stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub const fn global_size_of<T>(_bytes: usize) {}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::inline_air_stmt"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::proof]
pub fn inline_air_stmt(_s: &str) {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::array_index"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn array_index<T, const N: usize>(_a: [T; N], _i: int) -> T {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::erased_ghost_value"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn erased_ghost_value<S, T>(_: S) -> T {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::DummyCapture"]
#[derive(Clone, Copy)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub struct DummyCapture<'a> {
    _ph: core::marker::PhantomData<&'a ()>,
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::dummy_capture_new"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn dummy_capture_new<'a>() -> DummyCapture<'a> {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::dummy_capture_consume"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub fn dummy_capture_consume<'a>(_dc: DummyCapture<'a>) {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::resolve"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn resolve<T>(_t: T) {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::has_resolved"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn has_resolved<T>(_t: T) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::mut_ref_current"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn mut_ref_current<T>(_mut_ref: &mut T) -> T {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::verus_builtin::mut_ref_future"]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
#[verifier::spec]
pub fn mut_ref_future<T>(_mut_ref: &mut T) -> T {
    unimplemented!()
}
