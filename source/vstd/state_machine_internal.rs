//! Helper utilities used by the `state_machine_macros` codegen.
#![allow(unused_imports)]
#![doc(hidden)]

use super::map::*;
use super::pervasive::*;
use super::prelude::*;
use super::seq::*;

#[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(T))]
pub struct SyncSendIfSyncSend<T> {
    _sync_send: super::prelude::SyncSendIfSyncSend<T>,
}

#[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
pub struct NoCopy {
    _no_copy: super::prelude::NoCopy,
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove assertion safety condition")] /* vattr */
pub fn assert_safety(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove safety condition that the pattern matches")] /* vattr */
pub fn assert_let_pattern(b: bool) {
    requires(b);
    ensures(b);
}

// SpecialOps

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: to add a value Some(_), field must be None before the update")] /* vattr */
pub fn assert_add_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: to add a singleton set, the value must not be in the set before the update")] /* vattr */
pub fn assert_add_set(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: to add a value `true`, field must be `false` before the update")] /* vattr */
pub fn assert_add_bool(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the given key must be absent from the map before the update")] /* vattr */
pub fn assert_add_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: if the key is already in the map, its existing value must agree with the provided value")] /* vattr */
pub fn assert_add_persistent_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: if the previous value is Some(_), then this existing value must agree with the newly provided value")] /* vattr */
pub fn assert_add_persistent_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the given value to be withdrawn must be stored before the withdraw")] /* vattr */
pub fn assert_withdraw_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: to deposit a value into Some(_), the field must be None before the deposit")] /* vattr */
pub fn assert_deposit_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err(
    "unable to prove inherent safety condition: the value being guarded must be stored"
)] /* vattr */
pub fn assert_guard_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the value to be withdrawn must be stored at the given key before the withdraw")] /* vattr */
pub fn assert_withdraw_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the given key must be absent from the map before the deposit")] /* vattr */
pub fn assert_deposit_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the value being guarded must be stored at the given key")] /* vattr */
pub fn assert_guard_map(b: bool) {
    requires(b);
    ensures(b);
}

// SpecialOps (with general element)

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the optional values being composed cannot both be Some(_)")] /* vattr */
pub fn assert_general_add_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err(
    "unable to prove inherent safety condition: the sets being composed must be disjoint"
)] /* vattr */
pub fn assert_general_add_set(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the boolean values being composed cannot both be `true`")] /* vattr */
pub fn assert_general_add_bool(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the key domains of the maps being composed must be disjoint")] /* vattr */
pub fn assert_general_add_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the maps being composed must agree on their values for any key in both domains")] /* vattr */
pub fn assert_general_add_persistent_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: if the previous value and the newly added values are both Some(_), then their values must agree")] /* vattr */
pub fn assert_general_add_persistent_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the optional value to be withdrawn must be stored before the withdraw")] /* vattr */
pub fn assert_general_withdraw_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the optional values being composed cannot both be Some(_)")] /* vattr */
pub fn assert_general_deposit_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err(
    "unable to prove inherent safety condition: the value being guarded must be stored"
)] /* vattr */
pub fn assert_general_guard_option(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the map being withdrawn must be a submap of the stored map")] /* vattr */
pub fn assert_general_withdraw_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the key domains of the maps being composed must be disjoint")] /* vattr */
pub fn assert_general_deposit_map(b: bool) {
    requires(b);
    ensures(b);
}

#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[verifier::custom_req_err("unable to prove inherent safety condition: the map being guarded must be a submap of the stored map")] /* vattr */
pub fn assert_general_guard_map(b: bool) {
    requires(b);
    ensures(b);
}

// used by the `update field[idx] = ...;` syntax
//
// note: the built-in rust trait IndexMut doesn't work here
// (because these functions need to be 'spec' code, and IndexMut uses a &mut to do its job)
// perhaps we'll make our own trait for this purpose some day, but regardless, this suffices
// for our purposes

verus! {

#[doc(hidden)]
pub open spec fn nat_max(a: nat, b: nat) -> nat {
    if a > b {
        a
    } else {
        b
    }
}

#[doc(hidden)]
impl<A> Seq<A> {
    #[verifier::inline]
    pub open spec fn update_at_index(self, i: int, a: A) -> Self
        recommends
            0 <= i < self.len(),
    {
        self.update(i, a)
    }
}

#[doc(hidden)]
impl<K, V> Map<K, V> {
    // note that despite the name, this is allowed to insert
    #[verifier::inline]
    pub open spec fn update_at_index(self, k: K, v: V) -> Self {
        self.insert(k, v)
    }
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_is_none<V>(a: Option<V>) -> bool {
    a.is_None()
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_ge<V>(a: Option<V>, b: Option<V>) -> bool {
    b.is_Some() ==> a === b
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_add<V>(a: Option<V>, b: Option<V>) -> Option<V> {
    if b.is_Some() {
        b
    } else {
        a
    }
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_agree<V>(a: Option<V>, b: Option<V>) -> bool {
    a.is_Some() && b.is_Some() ==> a.get_Some_0() === b.get_Some_0()
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_sub<V>(a: Option<V>, b: Option<V>) -> Option<V> {
    if b.is_Some() {
        Option::None
    } else {
        a
    }
}

} // verus!
