// EXPECTED-ERROR: cannot borrow `inst` as mutable because it is also borrowed as immutable
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

 ActualCell {
 fields { #[sharding(storage_imap)] pub storage: IMap<int,(int,vstd::cell::PointsTo<u64>)>, }
 init! { initialize(initial:IMap<int,(int,vstd::cell::PointsTo<u64>)>) { init storage=initial; } }
 transition! { withdraw_at(p:vstd::cell::PointsTo<u64>) {
 withdraw storage -= [{let s=pre; s.storage.index(0).0} => (7,p)];
 } }
 }
}
verus! {

fn main() {
    let (cell0, Tracked(p0)) = vstd::cell::PCell::new(11u64);
    let (cell7, Tracked(p7)) = vstd::cell::PCell::new(23u64);
    let tracked mut inst;
    proof {
        let tracked mut m: IMap<int, (int, vstd::cell::PointsTo<u64>)> = IMap::tracked_empty();
        m.tracked_insert(0, (7, p0));
        m.tracked_insert(7, (7, p7));
        let initial = m;
        inst = ActualCell::Instance::initialize(initial, m);
    }
    let Tracked(loan) = Tracked(inst.borrow_at(7));
    proof {
        let tracked moved = inst.withdraw_at(p7);
    }
    let value = cell7.borrow(Tracked(&loan.1));
    assert(*value == 23);

}

} // verus!
