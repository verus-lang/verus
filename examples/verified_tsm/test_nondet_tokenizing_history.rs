use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {  Z {
    fields {
        #[sharding(variable)]
        pub v1: int,

        #[sharding(variable)]
        pub v2: int,

        #[sharding(not_tokenized)]
        pub nt: int,

        #[sharding(constant)]
        pub c: int,
    }

    init!{
        initialize() {
            init v1 = 0;
            init v2 = 1;
            init nt = 2;
            init c = 3;
        }
    }

    transition!{
        tr1() {
            update nt = pre.nt + 1; // this is ok because the exchange fn ignores this line
            update v1 = pre.v1 + 2;
        }
    }

    transition!{
        tr2() {
            // v1 should be passed in as tokens, v2 read nondeterministically
            birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
            update v1 = x;
        }
    }

    transition!{
        tr3() {
            // v1, v2 both passed in as tokens
            birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
            update v1 = x + 4 * pre.v2;
        }
    }
}}

verus! {

proof fn go() {
    let tracked (Tracked(instance), Tracked(mut v1), Tracked(v2)) = Z::Instance::initialize();
    assert(equal(v1.instance_id(), instance.id()));
    assert(equal(v2.instance_id(), instance.id()));
    assert(equal(v1.value(), 0));
    assert(equal(v2.value(), 1));
    assert(equal(instance.c(), 3));

    instance.tr1(&mut v1);
    assert(equal(v1.instance_id(), instance.id()));
    assert(equal(v1.value(), 2));

    let old_v1_value = v1.value();
    let tracked (Ghost(birds_eye_v2), Ghost(birds_eye_nt)) = instance.tr2(&mut v1);
    assert(equal(v1.instance_id(), instance.id()));
    assert(equal(v1.value(), birds_eye_nt + instance.c() + old_v1_value - birds_eye_v2));

    let old_v1_value = v1.value();
    let birds_eye_nt = instance.tr3(&mut v1, &v2);
    assert(equal(v1.instance_id(), instance.id()));
    assert(equal(v1.value(), birds_eye_nt + instance.c() + old_v1_value + 3 * v2.value()));
}

} // verus!
verus! {

fn main() {
    proof {
        go();
        let tracked (Tracked(instance), Tracked(mut v1), Tracked(v2)) = Z::Instance::initialize();
        let tracked cloned = instance.clone();
        assert(cloned.id() == instance.id());
        assert(cloned.c() == instance.c());
        cloned.tr1(&mut v1);
        let old_v1_value = v1.value();
        let tracked (Ghost(birds_eye_v2), Ghost(birds_eye_nt)) = cloned.tr2(&mut v1);
        assert(v1.value() == birds_eye_nt + cloned.c() + old_v1_value - birds_eye_v2);
        let old_v1_value = v1.value();
        let birds_eye_nt = instance.tr3(&mut v1, &v2);
        assert(v1.value() == birds_eye_nt + instance.c() + old_v1_value + 3 * v2.value());
    }
}

} // verus!
