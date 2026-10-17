use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
RefCounter<Perm> {
    fields {
        #[sharding(variable)]
        pub counter: nat,

        #[sharding(storage_option)]
        pub storage: Option<Perm>,

        #[sharding(multiset)]
        pub reader: Multiset<Perm>,
    }
// ANCHOR_END: fields

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: Perm| self.reader.count(t) > 0 ==>
            self.storage == Option::Some(t)
    }

    #[invariant]
    pub fn counter_agrees_storage(&self) -> bool {
        self.counter == 0 ==> self.storage is None
    }

    #[invariant]
    pub fn counter_agrees_storage_rev(&self) -> bool {
        self.storage is None ==> self.counter == 0
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.storage is Some ==>
            self.reader.count(self.storage->Some_0) == self.counter
    }

    init!{
        initialize_empty() {
            init counter = 0;
            init storage = Option::None;
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: Self) { }

    transition!{
        do_deposit(__tsm_reader_initial: Perm) {
            require(pre.counter == 0);
            update counter = 1;
            deposit storage += Some(__tsm_reader_initial);
            add reader += {__tsm_reader_initial};
        }
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(pre: Self, post: Self, __tsm_reader_initial: Perm) { }

    property!{
        reader_guard(__tsm_reader_initial: Perm) {
            have reader >= {__tsm_reader_initial};
            guard storage >= Some(__tsm_reader_initial);
        }
    }

    transition!{
        do_clone(__tsm_reader_initial: Perm) {
            have reader >= {__tsm_reader_initial};
            add reader += {__tsm_reader_initial};
            update counter = pre.counter + 1;
        }
    }

    #[inductive(do_clone)]
    fn do_clone_inductive(pre: Self, post: Self, __tsm_reader_initial: Perm) {
        assert(pre.reader.count(__tsm_reader_initial) > 0);
        assert(pre.storage == Option::Some(__tsm_reader_initial));
        assert(pre.storage is Some);
        assert(pre.counter > 0);
    }

    transition!{
        dec_basic(__tsm_reader_initial: Perm) {
            require(pre.counter >= 2);
            remove reader -= {__tsm_reader_initial};
            update counter = (pre.counter - 1) as nat;
        }
    }

    transition!{
        dec_to_zero(__tsm_reader_initial: Perm) {
            remove reader -= {__tsm_reader_initial};
            require(pre.counter < 2);
            assert(pre.counter == 1);
            update counter = 0;
            withdraw storage -= Some(__tsm_reader_initial);
        }
    }

    #[inductive(dec_basic)]
    fn dec_basic_inductive(pre: Self, post: Self, __tsm_reader_initial: Perm) {
        assert(pre.reader.count(__tsm_reader_initial) > 0);
        assert(pre.storage == Option::Some(__tsm_reader_initial));
    }

    #[inductive(dec_to_zero)]
    fn dec_to_zero_inductive(pre: Self, post: Self, __tsm_reader_initial: Perm) { }
});

fn main() {
    let (p, Tracked(perm)) = cell::PCell::new(7u64);
    let tracked (Tracked(inst), Tracked(mut counter), empty) = RefCounter::Instance::<
        cell::PointsTo<u64>,
    >::initialize_empty(None);
    let tracked reader = inst.do_deposit(perm, &mut counter, perm);
    let tracked cloned = inst.do_clone(reader.element(), &mut counter, &reader);
    proof {
        assert(counter.value() == 2);
        inst.dec_basic(cloned.element(), &mut counter, cloned);
        assert(counter.value() == 1);
    }
    let tracked mut returned = inst.dec_to_zero(reader.element(), &mut counter, reader);
    let value = p.take(Tracked(&mut returned));
    assert(value == 7);
}

} // verus!
