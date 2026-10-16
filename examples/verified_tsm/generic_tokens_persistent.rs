//! Checked generic field tokens for persistent strategies (`persistent_map`,
//! `persistent_set`, `persistent_option`): tokens are `Copy` knowledge, created
//! by `(union)=` and read by `have`, including bulk outputs (`MapToken`,
//! `SetToken`) and initial collections.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    P {
        fields {
            #[sharding(persistent_map)]
            pub names: Map<int, int>,

            #[sharding(persistent_set)]
            pub seen: Set<int>,

            #[sharding(persistent_option)]
            pub leader: Option<int>,

            #[sharding(variable)]
            pub next: int,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.names.dom().contains(k) ==> k < self.next
            &&& forall|k: int| #[trigger] self.seen.contains(k) ==> k < self.next
            &&& self.leader is Some ==> self.leader == Some(0int) && 0 < self.next
        }

        init!{
            initialize() {
                init names = Map::empty().insert(-1, 7);
                init seen = Set::empty().insert(-1);
                init leader = None;
                init next = 0;
            }
        }

        transition!{
            register(v: int) {
                add names (union)= [pre.next => v];
                add seen (union)= set { pre.next };
                update next = pre.next + 1;
            }
        }

        transition!{
            register_many(m: Map<int, int>) {
                require(forall|k: int| #[trigger] m.dom().contains(k) ==> pre.next <= k < pre.next + 10);
                add names (union)= (m);
                update next = pre.next + 10;
            }
        }

        transition!{
            elect(k: int) {
                have seen >= set { k };
                require(k == 0);
                add leader (union)= Some(k);
            }
        }

        property!{
            known(k: int, v: int) {
                have names >= [k => v];
                have leader >= Some(k);
                assert(k < pre.next);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(register)]
        fn register_inductive(pre: Self, post: Self, v: int) { }

        #[inductive(register_many)]
        fn register_many_inductive(pre: Self, post: Self, m: Map<int, int>) { }

        #[inductive(elect)]
        fn elect_inductive(pre: Self, post: Self, k: int) { }
    }
}

verus! {
proof fn client() {
    let tracked (Tracked(inst), Tracked(names), Tracked(seen), Tracked(leader), Tracked(next)) = P::Instance::initialize();
    assert(names.map() == Map::<int, int>::empty().insert(-1, 7));
    assert(seen.set().contains(-1));
    assert(leader is None);
    let tracked mut next = next;
    let tracked (Tracked(n0), Tracked(s0)) = inst.register(42, &mut next);
    assert(n0.key() == 0 && n0.value() == 42 && s0.element() == 0);
    // Persistent tokens are Copy.
    let tracked s0b = s0;
    let tracked l = inst.elect(0, &s0);
    let tracked l2 = l.clone();
    assert(l2.value() == 0 && s0b.element() == 0);
    inst.known(0, 42, &n0, &l, &next);
    let tracked many = inst.register_many(Map::empty().insert(1, 43).insert(2, 44), &mut next);
    assert(many.map().dom().contains(2) && next.value() == 11);
    let tracked n2 = many.into_map().tracked_remove(2);
    assert(n2.value() == 44);
    n0.agree(&n0b_copy(n0));
    let tracked mut names = names;
    let tracked m1 = names.remove(-1);
    assert(m1.value() == 7);
}

proof fn n0b_copy(tracked t: P::names) -> (tracked out: P::names) ensures out == t { t }
}

fn main() {}
