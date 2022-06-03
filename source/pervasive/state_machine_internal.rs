//! Helper utilities used by the `state_machine_macros` codegen.

#![allow(unused_imports)]

use builtin::*;
use crate::pervasive::*;
use crate::pervasive::seq::*;
use crate::pervasive::map::*;

#[verifier(external_body)]
pub struct SyncSendIfSyncSend<#[verifier(strictly_positive)] T> {
    _sync_send: builtin::SyncSendIfSyncSend<T>,
}

#[proof]
#[verifier(custom_req_err("unable to prove assertion safety condition"))]
pub fn assert_safety(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove safety condition that the pattern matches"))]
pub fn assert_let_pattern(b: bool) { requires(b); ensures(b); }

// SpecialOps

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: to add a value into Some(_), field must be None before the update"))]
pub fn assert_add_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the given key must be absent from the map before the update"))]
pub fn assert_add_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: if the key is already in the map, its existing value must agree with the provided value"))]
pub fn assert_add_persistent_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the given value to be withdrawn must be stored before the withdraw"))]
pub fn assert_withdraw_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: to deposit a value into Some(_), the field must be None before the deposit"))]
pub fn assert_deposit_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the value being guarded must be stored"))]
pub fn assert_guard_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the value to be withdrawn must be stored at the given key before the withdraw"))]
pub fn assert_withdraw_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the given key must be absent from the map before the deposit"))]
pub fn assert_deposit_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the value being guarded must be stored at the given key"))]
pub fn assert_guard_map(b: bool) { requires(b); ensures(b); }

// SpecialOps (with general element)

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the optional values being composed cannot both be Some(_)"))]
pub fn assert_general_add_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the key domains of the maps being composed must be disjoint"))]
pub fn assert_general_add_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the maps being composed must agree on their values for any key in both domains"))]
pub fn assert_general_add_persistent_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the optional value to be withdrawn must be stored before the withdraw"))]
pub fn assert_general_withdraw_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the optional values being composed cannot both be Some(_)"))]
pub fn assert_general_deposit_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the value being guarded must be stored"))]
pub fn assert_general_guard_option(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the map being withdrawn must be a submap of the stored map"))]
pub fn assert_general_withdraw_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the key domains of the maps being composed must be disjoint"))]
pub fn assert_general_deposit_map(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the map being guarded must be a submap of the stored map"))]
pub fn assert_general_guard_map(b: bool) { requires(b); ensures(b); }

// used by the `update field[idx] = ...;` syntax
//
// note: the built-in rust trait IndexMut doesn't work here
// (because these functions need to be 'spec' code, and IndexMut uses a &mut to do its job)
// perhaps we'll make our own trait for this purpose some day, but regardless, this suffices
// for our purposes

impl<A> Seq<A> {
    #[spec] #[verifier(publish)]
    pub fn update_at_index(self, i: int, a: A) -> Self {
        recommends(0 <= i && i < self.len());

        self.update(i, a)
    }
}

impl<K, V> Map<K, V> {
    // note that despite the name, this is allowed to insert

    #[spec] #[verifier(publish)]
    pub fn update_at_index(self, k: K, v: V) -> Self {
        self.insert(k, v)
    }
}
