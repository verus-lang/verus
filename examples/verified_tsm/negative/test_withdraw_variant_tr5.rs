// EXPECTED-ERROR: assertion failed
//! Original pattern_binding_withdraw_assert_fails tr5, isolated.
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
    fields { #[sharding(storage_imap)] pub storage_m: IMap<int, Goo>, #[sharding(variable)] pub auth: IMap<int, Goo>, }
    #[invariant] pub fn authority(&self) -> bool { self.auth == self.storage_m }
    transition! { tr5() {
        require pre.auth.dom().contains(1);
        withdraw storage_m -= [1 => let Goo::Qux(id1)];
        update auth = pre.auth.remove(1);
    } }
    #[inductive(tr5)] fn preserve(pre: Self, post: Self) {}
} }

} // verus!
fn main() {}
