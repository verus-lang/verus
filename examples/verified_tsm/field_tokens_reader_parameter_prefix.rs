use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
RefCounter<Perm> {
    fields {
        #[sharding(variable)]
        pub left: nat,

        #[sharding(storage_option)]
        pub physical: Option<Perm>,

        #[sharding(multiset)]
        pub auditor: Multiset<Perm>,
    }
// ANCHOR_END: fields

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: Perm| self.auditor.count(t) > 0 ==>
            self.physical == Option::Some(t)
    }

    #[invariant]
    pub fn counter_agrees_storage(&self) -> bool {
        self.left == 0 ==> self.physical is None
    }

    #[invariant]
    pub fn counter_agrees_storage_rev(&self) -> bool {
        self.physical is None ==> self.left == 0
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.physical is Some ==>
            self.auditor.count(self.physical->Some_0) == self.left
    }

    init!{
        begin() {
            init left = 0;
            init physical = Option::None;
            init auditor = Multiset::empty();
        }
    }

    #[inductive(begin)]
    fn initialize_empty_inductive(post: Self) { }

    transition!{
        deposit_one(pair: Perm) {
            require(pre.left == 0);
            update left = 1;
            deposit physical += Some(pair);
            add auditor += {pair};
        }
    }

    #[inductive(deposit_one)]
    fn do_deposit_inductive(pre: Self, post: Self, pair: Perm) { }

    property!{
        borrow_actual(pair: Perm) {
            have auditor >= {pair};
            guard physical >= Some(pair);
        }
    }

    transition!{
        copy_one(pair: Perm) {
            have auditor >= {pair};
            add auditor += {pair};
            update left = pre.left + 1;
        }
    }

    #[inductive(copy_one)]
    fn do_clone_inductive(pre: Self, post: Self, pair: Perm) {
        assert(pre.auditor.count(pair) > 0);
        assert(pre.physical == Option::Some(pair));
        assert(pre.physical is Some);
        assert(pre.left > 0);
    }

    transition!{
        drop_one(pair: Perm) {
            require(pre.left >= 2);
            remove auditor -= {pair};
            update left = (pre.left - 1) as nat;
        }
    }

    transition!{
        take_last(pair: Perm) {
            remove auditor -= {pair};
            require(pre.left < 2);
            assert(pre.left == 1);
            update left = 0;
            withdraw physical -= Some(pair);
        }
    }

    #[inductive(drop_one)]
    fn dec_basic_inductive(pre: Self, post: Self, pair: Perm) {
        assert(pre.auditor.count(pair) > 0);
        assert(pre.physical == Option::Some(pair));
    }

    #[inductive(take_last)]
    fn dec_to_zero_inductive(pre: Self, post: Self, pair: Perm) { }
});

fn main() {
    let (p, Tracked(perm)) = cell::PCell::new(7u64);
    let tracked (Tracked(inst), Tracked(mut left), _) = RefCounter::Instance::begin(None);
    let tracked auditor = inst.deposit_one(perm, &mut left, perm);
    let tracked cloned = inst.clone();
    let tracked first = inst.borrow_actual(auditor.element(), &auditor);
    let tracked second = cloned.borrow_actual(auditor.element(), &auditor);
    let a = p.borrow(Tracked(first));
    let b = p.borrow(Tracked(second));
    assert(*a == 7);
    assert(*b == 7);
}

} // verus!
