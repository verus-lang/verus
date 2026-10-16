//! Checked generic field tokens for `variable` and `constant` fields, in a
//! machine without storage: `&mut` token updates, borrowed reads, constants
//! read from the instance, a property, and an operation that consumes no
//! token (its unit resource comes from the instance).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::multiset::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    V {
        fields {
            #[sharding(constant)]
            pub limit: int,

            #[sharding(variable)]
            pub value: int,

            #[sharding(variable)]
            pub steps: nat,

            #[sharding(multiset)]
            pub marks: Multiset<int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& 0 <= self.value <= self.limit
            &&& forall|m: int| #[trigger] self.marks.count(m) > 0 ==> 0 <= m <= self.limit
        }

        init!{
            initialize(limit: int) {
                require(limit >= 0);
                init limit = limit;
                init value = 0;
                init steps = 0;
                init marks = Multiset::empty();
            }
        }

        transition!{
            bump(by: int) {
                require(by >= 0);
                require(pre.value + by <= pre.limit);
                update value = pre.value + by;
                update steps = pre.steps + 1;
            }
        }

        transition!{
            mark() {
                // Reads `value` without changing it.
                require(!(pre.value == pre.limit + 1));
                add marks += { pre.value };
            }
        }

        transition!{
            mark_zero() {
                add marks += { 0 };
            }
        }

        property!{
            in_range() {
                assert(0 <= pre.value <= pre.limit);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, limit: int) { }

        #[inductive(bump)]
        fn bump_inductive(pre: Self, post: Self, by: int) { }

        #[inductive(mark)]
        fn mark_inductive(pre: Self, post: Self) {
            assert forall|m: int| #[trigger] post.marks.count(m) > 0 implies 0 <= m <= post.limit by {
                if m != pre.value { assert(pre.marks.count(m) > 0); }
            }
        }

        #[inductive(mark_zero)]
        fn mark_zero_inductive(pre: Self, post: Self) {
            assert forall|m: int| #[trigger] post.marks.count(m) > 0 implies 0 <= m <= post.limit by {
                if m != 0 { assert(pre.marks.count(m) > 0); }
            }
        }
    }
}

verus! {
proof fn client() {
    let tracked (Tracked(inst), Tracked(value), Tracked(steps), Tracked(marks)) = V::Instance::initialize(10);
    assert(inst.limit() == 10);
    let tracked mut value = value;
    let tracked mut steps = steps;
    inst.bump(3, &mut value, &mut steps);
    assert(value.value() == 3 && steps.value() == 1);
    inst.in_range(&value);
    assert(value.value() <= inst.limit());
    let tracked m = inst.mark(&value);
    assert(m.element() == 3);
    let tracked z = inst.mark_zero();
    assert(z.element() == 0 && z.instance_id() == inst.id());
    let tracked mut all = marks;
    all.insert(m);
    all.insert(z);
    assert(all.multiset().count(3) == 1);
    let tracked mut v2 = value;
    v2.unique(&steps_as_value_impossible());
}

// Two `value` tokens of one instance cannot coexist; a placeholder can.
proof fn steps_as_value_impossible() -> (tracked t: V::value) {
    V::value::arbitrary()
}
}

fn main() {}
