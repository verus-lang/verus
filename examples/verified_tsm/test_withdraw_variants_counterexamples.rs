use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

pub enum Goo {
    Bar,
    Qux(u64),
    Tal(u64, u64),
}

verified_state_machine_model!{ Y {
            fields {
                #[sharding(storage_imap)]
                pub storage_m: IMap<int, Goo>,

                #[sharding(storage_option)]
                pub storage_opt: Option<Goo>,
            }

            transition!{
                tr1() {
                    withdraw storage_opt -= Some(let Goo::Bar) by { // FAILS
                        /* Original existence hypothesis is stated in the checked safety companion. */
                    };
                }
            }

            transition!{
                tr2() {
                    withdraw storage_opt -= Some(let Goo::Qux(id1)) by { // FAILS
                        /* Original existence hypothesis is stated in the checked safety companion. */
                    };
                }
            }

            transition!{
                tr3() {
                    withdraw storage_opt -= Some(let Goo::Tal(id1, id2)) by { // FAILS
                        /* Original existence hypothesis is stated in the checked safety companion. */
                    };
                }
            }

            transition!{
                tr4() {
                    withdraw storage_m -= [1 => let Goo::Bar] by { // FAILS
                        /* Original existence hypothesis is stated in the checked safety companion. */
                    };
                }
            }

            transition!{
                tr5() {
                    withdraw storage_m -= [1 => let Goo::Qux(id1)] by { // FAILS
                        /* Original existence hypothesis is stated in the checked safety companion. */
                    };
                }
            }

            transition!{
                tr6() {
                    withdraw storage_m -= [1 => let Goo::Tal(id1, id2)] by { // FAILS
                        /* Original existence hypothesis is stated in the checked safety companion. */
                    };
                }
            }
        }}

fn main() {
    proof {
        let pre = Y::State { storage_opt: Some(Goo::Qux(0)), storage_m: IMap::empty() };
        assert(pre.storage_opt is Some);
        assert(!Y::State::tr1_enabled_strong(pre));

    }
    proof {
        let pre = Y::State { storage_opt: Some(Goo::Bar), storage_m: IMap::empty() };
        assert(pre.storage_opt is Some);
        assert(!Y::State::tr2_enabled_strong(pre));

    }
    proof {
        let pre = Y::State { storage_opt: Some(Goo::Qux(0)), storage_m: IMap::empty() };
        assert(pre.storage_opt is Some);
        assert(!Y::State::tr3_enabled_strong(pre));

    }
    proof {
        let pre = Y::State { storage_opt: None, storage_m: IMap::empty().insert(1, Goo::Qux(0)) };
        assert(pre.storage_m.dom().contains(1));
        assert(!Y::State::tr4_enabled_strong(pre));

    }
    proof {
        let pre = Y::State { storage_opt: None, storage_m: IMap::empty().insert(1, Goo::Bar) };
        assert(pre.storage_m.dom().contains(1));
        assert(!Y::State::tr5_enabled_strong(pre));

    }
    proof {
        let pre = Y::State { storage_opt: None, storage_m: IMap::empty().insert(1, Goo::Qux(0)) };
        assert(pre.storage_m.dom().contains(1));
        assert(!Y::State::tr6_enabled_strong(pre));

    }
}

} // verus!
