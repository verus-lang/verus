// EXPECTED-ERROR: assertion failed
//! Original pattern_binding_withdraw_assert_fails tr2, isolated.
//! The original assumed mere presence; this checked companion requires it.
//! An explicit ghost authority mirrors the unowned physical storage.
//! Presence still cannot establish the requested enum variant.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub enum Goo {
    Bar,
    Qux(u64),
    Tal(u64, u64),
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 Y {
    fields { #[sharding(storage_option)] pub storage_opt: Option<Goo>, #[sharding(variable)] pub auth: Option<Goo>, }
    #[invariant] pub fn authority(&self) -> bool { self.auth == self.storage_opt }
    transition! { tr2() {
        require pre.auth is Some;
        withdraw storage_opt -= Some(let Goo::Qux(id1));
        update auth = None;
    } }
    #[inductive(tr2)] fn preserve(pre: Self, post: Self) {}
} }

} // verus!
fn main() {}
