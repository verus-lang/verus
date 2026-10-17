// EXPECTED-ERROR: assertion failed
//! Original pattern_binding_withdraw_assert_fails tr1, isolated.
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
    transition! { tr1() {
        require pre.auth is Some;
        withdraw storage_opt -= Some(let Goo::Bar);
        update auth = None;
    } }
    #[inductive(tr1)] fn preserve(pre: Self, post: Self) {}
} }

} // verus!
fn main() {}
