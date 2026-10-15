use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(count)]
        pub c: nat,
    }

    init!{
        initialize() {
            init c = 9;
        }
    }

    transition!{
        tr_add(__tsm_logical_count_owned: nat) {
            add c += (__tsm_logical_count_owned);
        }
    }

    transition!{
        tr_have(__tsm_logical_count_input: nat) {
            have c >= (__tsm_logical_count_input);
        }
    }

    transition!{
        tr_remove(__tsm_logical_count_before: nat) {
            remove c -= (__tsm_logical_count_before);
        }
    }
}}

verus! {

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut t1)) = Y::Instance::initialize();
        let tracked t2 = t1.split(2);
        inst.tr_have(2, &t2);
        inst.tr_remove(2, t2);
        let tracked t4 = inst.tr_add(2);
        t1.join(t4);
        assert(t1.count() == 9);
    }
}

} // verus!
