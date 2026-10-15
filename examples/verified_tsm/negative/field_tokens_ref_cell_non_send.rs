// EXPECTED-ERROR: `std::rc::Rc<u64>` cannot be sent between threads safely
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
#[verified_local_ready(do_deposit,do_withdraw,new_reader,drop_reader)]
RefCounter<S> {
    fields {
        #[sharding(constant)]
        pub pcell_loc: CellId,

        #[sharding(variable)]
        pub flag: BorrowFlag,

        #[sharding(storage_option)]
        pub storage: Option<Perm<S>>,

        #[sharding(multiset)]
        pub reader: Multiset<Perm<S>>,

        #[sharding(bool)]
        pub writer: bool,
    }
// ANCHOR_END: fields

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: Perm<S>| #[trigger] self.reader.count(t) > 0 ==>
            self.storage == Option::Some(t)
    }

    #[invariant]
    pub fn flag_inv(&self) -> bool {
        match self.flag {
            BorrowFlag::MutBorrow => {
                self.writer && self.reader == Multiset::<Perm<S>>::empty()
                  && self.storage is None
            }
            BorrowFlag::ReadBorrow(n) => {
                !self.writer
                  && self.storage is Some
                  && self.reader.count(self.storage->0) == n
            }
        }
    }

    #[invariant]
    pub fn storage_inv(&self) -> bool {
        match self.storage {
            Some(x) => x.id() == self.pcell_loc && x.is_init(),
            None => true,
        }
    }

    init!{
        initialize_empty(loc: CellId) {
            init pcell_loc = loc;
            init flag = BorrowFlag::MutBorrow;
            init storage = Option::None;
            init reader = Multiset::empty();
            init writer = true;
        }
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: Self, loc: CellId) { }

    transition!{
        do_deposit(x: Perm<S>) {
            require(x.id() == pre.pcell_loc && x.is_init());
            remove writer -= true;
            assert(pre.flag == BorrowFlag::MutBorrow);
            update flag = BorrowFlag::ReadBorrow(0);

            deposit storage += Some(x);
        }
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(pre: Self, post: Self, x: Perm<S>) { }

    transition!{
        do_withdraw() {
            require(pre.flag == BorrowFlag::ReadBorrow(0));
            update flag = BorrowFlag::MutBorrow;

            add writer += true;

            withdraw storage -= Some(let x);
            assert(x.id() == pre.pcell_loc && x.is_init());
        }
    }

    #[inductive(do_withdraw)]
    fn do_withdraw_inductive(pre: Self, post: Self) {
        assert_multisets_equal!(post.reader, Multiset::<Perm<S>>::empty());
    }

    property!{
        reader_guard(x: Perm<S>) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    transition!{
        new_reader() {
            require let BorrowFlag::ReadBorrow(n) = pre.flag;
            update flag = BorrowFlag::ReadBorrow(n + 1);

            birds_eye let x = pre.storage->0;
            add reader += { x };
            assert(x.id() == pre.pcell_loc && x.is_init());
        }
    }

    #[inductive(new_reader)]
    fn new_reader_inductive(pre: Self, post: Self) { }

    transition!{
        drop_reader(x: Perm<S>) {
            remove reader -= { x };
            assert let BorrowFlag::ReadBorrow(n) = pre.flag;
            assert n >= 1;
            update flag = BorrowFlag::ReadBorrow((n - 1) as nat);
        }
    }

    #[inductive(drop_reader)]
    fn drop_reader_inductive(pre: Self, post: Self, x: Perm<S>) {
        assert(pre.reader.count(x) > 0);
        assert(pre.storage == Option::Some(x));
        assert(pre.storage is Some);
    }
});

fn require_trait<T: Send>() {
}

fn main() {
    require_trait::<RefCounter::flag<std::rc::Rc<u64>>>();
}

} // verus!
