//! Helper utilities used by the `state_machine_macros` codegen.

#[allow(unused_imports)] use builtin::*;

#[verifier(external_body)]
pub struct SyncSendIfSyncSend<#[verifier(strictly_positive)] T> {
    sync_send: builtin::SyncSendIfSyncSend<T>,
}

#[proof]
#[verifier(custom_req_err("unable to prove assertion safety condition"))]
pub fn assert_safety(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: to add a value into Some(_), field must be None before the update"))]
pub fn assert_add_some(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the given key must be absent from the map before the update"))]
pub fn assert_add_kv(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the given value to be withdrawn must be stored before the withdraw"))]
pub fn assert_withdraw_some(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: to deposit a value into Some(_), the field must be None before the deposit"))]
pub fn assert_deposit_some(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the value being guarded must be stored"))]
pub fn assert_guard_some(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the value to be withdrawn must be stored at the given key before the withdraw"))]
pub fn assert_withdraw_kv(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the givden key must be absent from the map before the deposit"))]
pub fn assert_deposit_kv(b: bool) { requires(b); ensures(b); }

#[proof]
#[verifier(custom_req_err("unable to prove inherent safety condition: the value being guarded must be stored at the given key"))]
pub fn assert_guard_kv(b: bool) { requires(b); ensures(b); }
