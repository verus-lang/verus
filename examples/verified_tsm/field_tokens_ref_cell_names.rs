use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::cell::CellId;
use vstd::multiset::*;
use vstd::prelude::*;
verus! {

pub enum BorrowFlag {
    MutBorrow,
    ReadBorrow(nat),
}

type Perm<S> = cell::PointsTo<S>;

verified_tokenized_state_machine!(
RefCounter<S> {
    fields {
        #[sharding(constant)]
        pub metadata: CellId,

        #[sharding(variable)]
        pub owner: BorrowFlag,

        #[sharding(storage_option)]
        pub storage: Option<Perm<S>>,

        #[sharding(multiset)]
        pub slot: Multiset<Perm<S>>,

        #[sharding(bool)]
        pub actual: bool,
    }
// ANCHOR_END: fields

    #[invariant]
    pub fn slot_agrees_storage(&self) -> bool {
        forall |t: Perm<S>| #[trigger] self.slot.count(t) > 0 ==>
            self.storage == Option::Some(t)
    }

    #[invariant]
    pub fn owner_inv(&self) -> bool {
        match self.owner {
            BorrowFlag::MutBorrow => {
                self.actual && self.slot == Multiset::<Perm<S>>::empty()
                  && self.storage is None
            }
            BorrowFlag::ReadBorrow(n) => {
                !self.actual
                  && self.storage is Some
                  && self.slot.count(self.storage->0) == n
            }
        }
    }

    #[invariant]
    pub fn storage_inv(&self) -> bool {
        match self.storage {
            Some(__tsm_borrow_owner) => __tsm_borrow_owner.id() == self.metadata && __tsm_borrow_owner.is_init(),
            None => true,
        }
    }

    init!{
        initialize_empty(loc: CellId) {
            init metadata = loc;
            init owner = BorrowFlag::MutBorrow;
            init storage = Option::None;
            init slot = Multiset::empty();
            init actual = true;
        }
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: Self, loc: CellId) { }

    transition!{
        do_deposit(__tsm_borrow_owner: Perm<S>) {
            require(__tsm_borrow_owner.id() == pre.metadata && __tsm_borrow_owner.is_init());
            remove actual -= true;
            assert(pre.owner == BorrowFlag::MutBorrow);
            update owner = BorrowFlag::ReadBorrow(0);

            deposit storage += Some(__tsm_borrow_owner);
        }
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(pre: Self, post: Self, __tsm_borrow_owner: Perm<S>) { }

    transition!{
        do_withdraw() {
            require(pre.owner == BorrowFlag::ReadBorrow(0));
            update owner = BorrowFlag::MutBorrow;

            add actual += true;

            withdraw storage -= Some(let __tsm_borrow_owner);
            assert(__tsm_borrow_owner.id() == pre.metadata && __tsm_borrow_owner.is_init());
        }
    }

    #[inductive(do_withdraw)]
    fn do_withdraw_inductive(pre: Self, post: Self) {
        assert_multisets_equal!(post.slot, Multiset::<Perm<S>>::empty());
    }

    property!{
        slot_guard(__tsm_borrow_owner: Perm<S>) {
            have slot >= {__tsm_borrow_owner};
            guard storage >= Some(__tsm_borrow_owner);
        }
    }

    transition!{
        new_slot() {
            require let BorrowFlag::ReadBorrow(n) = pre.owner;
            update owner = BorrowFlag::ReadBorrow(n + 1);

            birds_eye let __tsm_borrow_owner = pre.storage->0;
            add slot += { __tsm_borrow_owner };
            assert(__tsm_borrow_owner.id() == pre.metadata && __tsm_borrow_owner.is_init());
        }
    }

    #[inductive(new_slot)]
    fn new_slot_inductive(pre: Self, post: Self) { }

    transition!{
        drop_slot(__tsm_borrow_owner: Perm<S>) {
            remove slot -= { __tsm_borrow_owner };
            assert let BorrowFlag::ReadBorrow(n) = pre.owner;
            assert n >= 1;
            update owner = BorrowFlag::ReadBorrow((n - 1) as nat);
        }
    }

    #[inductive(drop_slot)]
    fn drop_slot_inductive(pre: Self, post: Self, __tsm_borrow_owner: Perm<S>) {
        assert(pre.slot.count(__tsm_borrow_owner) > 0);
        assert(pre.storage == Option::Some(__tsm_borrow_owner));
        assert(pre.storage is Some);
    }
});

fn main() {
}

} // verus!
