use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {

X {
           fields {
               #[sharding(storage_imap)] pub v: IMap<int, int>,
           }

           init!{
               initialize() {
                   init v = IMap::empty();
               }
           }

           transition!{
               tr() {
                   // this is ok:
                   withdraw v -= [{ let s = pre; s.v.index(0) } => 5]
                         by { assume(false); };
               }
           }
       }}

verified_tokenized_state_machine! {

 Generic<#[verifier::reject_recursive_types] r#__tsm_owned_imap_before, #[verifier::reject_recursive_types] r#__tsm_owned_imap_result> {
 fields { #[sharding(storage_imap)] pub storage: IMap<r#__tsm_owned_imap_before,r#__tsm_owned_imap_result>, }
 init! { initialize(initial: IMap<r#__tsm_owned_imap_before,r#__tsm_owned_imap_result>) { init storage = initial; } }
 transition! { withdraw_at(k: r#__tsm_owned_imap_before, v: r#__tsm_owned_imap_result) { withdraw storage -= [{let s=pre; let _all=s.storage; k} => v]; } }
 }
}
verus! {

proof fn generic_custody<r#__tsm_owned_imap_before, r#__tsm_owned_imap_result>(
    k: r#__tsm_owned_imap_before,
    v: r#__tsm_owned_imap_result,
    tracked m: IMap<r#__tsm_owned_imap_before, r#__tsm_owned_imap_result>,
)
    requires
        m == IMap::<r#__tsm_owned_imap_before, r#__tsm_owned_imap_result>::empty().insert(k, v),
{
    let tracked mut inst = Generic::Instance::initialize(m, m);
    let tracked borrowed = inst.borrow_at(k);
    assert(*borrowed == v);
    let tracked actual = inst.withdraw_at(k, v);
    assert(actual == v);
    assert(inst.value() == IMap::<r#__tsm_owned_imap_before, r#__tsm_owned_imap_result>::empty());
}

} // verus!
fn main() {}
