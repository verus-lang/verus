//! Checked generic field tokens for the infinite-collection strategies
//! (`imap`, `iset`, `persistent_imap`, `persistent_iset`): single tokens,
//! finite initial collections, and bulk outputs and inputs (finite
//! collections only: they are split and joined token by token).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    I {
        fields {
            #[sharding(imap)]
            pub slots: IMap<int, int>,

            #[sharding(iset)]
            pub free: ISet<int>,

            #[sharding(persistent_imap)]
            pub log: IMap<int, int>,

            #[sharding(persistent_iset)]
            pub done: ISet<int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.free.contains(k) ==> !self.slots.dom().contains(k)
            &&& forall|k: int| #[trigger] self.slots.dom().contains(k) ==> !self.log.dom().contains(k)
            &&& forall|k: int| #[trigger] self.free.contains(k) ==> !self.log.dom().contains(k)
            &&& forall|k: int| #[trigger] self.done.contains(k) <==> self.log.dom().contains(k)
        }

        init!{
            initialize() {
                init slots = IMap::empty().insert(0, 0);
                init free = ISet::empty().insert(1).insert(2).insert(3);
                init log = IMap::empty();
                init done = ISet::empty();
            }
        }

        transition!{
            claim(k: int, v: int) {
                remove free -= set { k };
                add slots += [k => v];
            }
        }

        transition!{
            claim_many(s: ISet<int>) {
                remove free -= (s);
                add slots += (IMap::new(|k: int| s.contains(k), |k: int| 7int));
            }
        }

        transition!{
            finish(k: int) {
                remove slots -= [k => let v];
                add log (union)= [k => v];
                add done (union)= set { k };
            }
        }

        property!{
            finished(k: int, v: int) {
                have log >= [k => v];
                have done >= set { k };
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(claim)]
        fn claim_inductive(pre: Self, post: Self, k: int, v: int) { }

        #[inductive(claim_many)]
        fn claim_many_inductive(pre: Self, post: Self, s: ISet<int>) { }

        #[inductive(finish)]
        fn finish_inductive(pre: Self, post: Self, k: int) { }
    }
}

verus! {
proof fn client() {
    let tracked (Tracked(inst), Tracked(slots), Tracked(free), Tracked(log), Tracked(done)) = I::Instance::initialize();
    assert(slots.map().dom().contains(0));
    assert(free.set().contains(1) && free.set().contains(2));
    let tracked mut free = free;
    let tracked f1 = free.remove(1);
    let tracked s1 = inst.claim(1, 10, f1);
    assert(s1.key() == 1 && s1.value() == 10);
    let s = ISet::<int>::empty().insert(2).insert(3);
    assert(s <= free.set());
    // Bulk `imap`/`iset` operands must be finite (an extra requirement of the
    // checked interface).
    broadcast use vstd::iset::group_iset_lemmas;
    assert(s.finite());
    assert(IMap::new(|k: int| s.contains(k), |k: int| 7int).dom() =~= s);
    let tracked many = inst.claim_many(s, free);
    assert(many.map().dom() == s);
    let tracked (Tracked(l1), Tracked(d1)) = inst.finish(1, s1);
    assert(l1.value() == 10 && d1.element() == 1);
    inst.finished(1, 10, &l1, &d1);
    let tracked mut slots = slots;
    let tracked s0 = slots.remove(0);
    let tracked mut many = many;
    let tracked s2 = many.remove(2);
    let tracked mut s0 = s0;
    s0.unique(&s2);
}
}

fn main() {}
