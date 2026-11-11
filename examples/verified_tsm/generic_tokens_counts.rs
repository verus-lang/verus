//! Checked generic field tokens for `count`, `persistent_count`, `bool` and
//! `persistent_bool` fields: fungible counts (join/split), monotone lower
//! bounds (`weaken`, `Copy`), and boolean flags (`Option<token>` outputs).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    C {
        fields {
            #[sharding(count)]
            pub tickets: nat,

            #[sharding(persistent_count)]
            pub issued: nat,

            #[sharding(bool)]
            pub open: bool,

            #[sharding(persistent_bool)]
            pub closed_once: bool,

            #[sharding(variable)]
            pub total: nat,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.tickets <= self.total
            &&& self.issued == self.total
        }

        init!{
            initialize() {
                init tickets = 0;
                init issued = 0;
                init open = true;
                init closed_once = false;
                init total = 0;
            }
        }

        transition!{
            issue(n: nat) {
                have open >= true;
                add tickets += (n);
                update total = pre.total + n;
                add issued (union)= (pre.total + n);
            }
        }

        transition!{
            spend(n: nat) {
                remove tickets -= (n);
            }
        }

        transition!{
            close() {
                remove open -= true;
                add closed_once (union)= true;
            }
        }

        property!{
            lower_bound(n: nat) {
                have issued >= (n);
                assert(pre.total >= n);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(issue)]
        fn issue_inductive(pre: Self, post: Self, n: nat) { }

        #[inductive(spend)]
        fn spend_inductive(pre: Self, post: Self, n: nat) { }

        #[inductive(close)]
        fn close_inductive(pre: Self, post: Self) { }
    }
}

verus! {
proof fn client() {
    let tracked (Tracked(inst), Tracked(tickets), Tracked(issued), Tracked(open), Tracked(closed_once), Tracked(total)) =
        C::Instance::initialize();
    assert(tickets.count() == 0 && issued.count() == 0);
    assert(open is Some && closed_once is None);
    let tracked open = open.tracked_unwrap();
    let tracked mut total = total;
    let tracked (Tracked(t5), Tracked(i5)) = inst.issue(5, &open, &mut total);
    assert(t5.count() == 5 && i5.count() == 5 && total.value() == 5);
    // A persistent lower bound is Copy and can be weakened.
    let tracked i5b = i5;
    let tracked i3 = i5.weaken(3);
    assert(i5b.count() == 5 && i3.count() == 3);
    inst.lower_bound(3, &i3, &total);
    assert(total.value() >= 3);
    // Count tokens are fungible.
    let tracked mut t5 = t5;
    let tracked t2 = t5.split(2);
    assert(t5.count() == 3 && t2.count() == 2);
    inst.spend(2, t2);
    let tracked mut tickets = tickets;
    tickets.join(t5);
    assert(tickets.count() == 3);
    let tracked c = inst.close(open);
    assert(c.instance_id() == inst.id());
}
}

fn main() {}
