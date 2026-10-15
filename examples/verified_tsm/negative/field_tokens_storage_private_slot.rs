// EXPECTED-ERROR: field `raw`
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub enum TxState {
    Ready,
    Gathering,
    GatheringWithdrawn,
    Mutating,
    MutatingWithdrawn,
}

pub trait TxPredicate<V, M>: Sized {
    spec fn inv(self, v: V) -> bool;

    spec fn metadata(self, v: V) -> M;
}

verified_tokenized_state_machine!(
#[verified_local_ready(gather,withdraw,deposit,withdraw_mutating,deposit_mutating,mutate)] TxToks<V, M, Pred: TxPredicate<V, M>> {
    fields {
        #[sharding(constant)]
        pub pred: Pred,

        #[sharding(variable)]
        pub state: TxState,

        #[sharding(variable)]
        pub metadata: M,

        #[sharding(variable)]
        pub valid: bool,

        #[sharding(storage_option)]
        pub val: Option<V>,
    }

    #[invariant]
    pub fn val_state(&self) -> bool {
        (self.state is GatheringWithdrawn
            || self.state is MutatingWithdrawn) <==> self.val is None
    }

    #[invariant]
    pub fn valid_v(&self) -> bool {
        self.val matches Some(v) ==> self.valid == self.pred.inv(v)
    }

    #[invariant]
    pub fn valid_metadata(&self) -> bool {
        self.val matches Some(v) ==> self.metadata == self.pred.metadata(v)
    }

    init! {
        new(v: V, pred: Pred) {
            require pred.inv(v);
            init pred = pred;
            init state = TxState::Ready;
            init metadata = pred.metadata(v);
            init valid = true;
            init val = Some(v);
        }
    }

    #[inductive(new)]
    fn new_inductive(post: Self, v: V, pred: Pred) {
    }

    transition! {
        gather() {
            require pre.state is Ready;
            update state = TxState::Gathering;
        }
    }

    #[inductive(gather)]
    fn gather_inductive(pre: Self, post: Self) {
    }

    transition! {
        withdraw() {
            require pre.state is Gathering || pre.state is Mutating;
            require pre.valid;
            birds_eye let v = pre.val->0;
            withdraw val -= Some(v);
            assert(pre.pred.inv(v));
            assert(pre.metadata == pre.pred.metadata(v));
            update state = TxState::GatheringWithdrawn;
        }
    }

    #[inductive(withdraw)]
    fn withdraw_inductive(pre: Self, post: Self) {
    }

    transition! {
        deposit(v: V) {
            require pre.state is GatheringWithdrawn;
            require pre.pred.inv(v);
            deposit val += Some(v);
            update metadata = pre.pred.metadata(v);
            update valid = true;
            update state = TxState::Gathering;
        }
    }

    #[inductive(deposit)]
    fn deposit_inductive(pre: Self, post: Self, v: V) {
    }

    transition! {
        withdraw_mutating() {
            require pre.state is Mutating;
            require pre.valid;
            birds_eye let v = pre.val->0;
            withdraw val -= Some(v);
            assert(pre.pred.inv(v));
            assert(pre.metadata == pre.pred.metadata(v));
            update state = TxState::MutatingWithdrawn;
        }
    }

    #[inductive(withdraw_mutating)]
    fn withdraw_mutating_inductive(pre: Self, post: Self) {
    }

    transition! {
        deposit_mutating(v: V) {
            require pre.state is MutatingWithdrawn;
            require pre.pred.inv(v);
            deposit val += Some(v);
            update metadata = pre.pred.metadata(v);
            update valid = true;
            update state = TxState::Mutating;
        }
    }

    #[inductive(deposit_mutating)]
    fn deposit_mutating_inductive(pre: Self, post: Self, v: V) {
    }

    transition! {
        mutate() {
            require pre.state is Gathering;
            update state = TxState::Mutating;
        }
    }

    #[inductive(mutate)]
    fn mutate_inductive(pre: Self, post: Self) {
    }
});

} // verus!
use vstd::cell::pcell_maybe_uninit as cell;
verus! {

pub struct Pred {
    pub ghost id: vstd::cell::CellId,
}

impl TxPredicate<cell::PointsTo<u64>, u64> for Pred {
    open spec fn inv(self, v: cell::PointsTo<u64>) -> bool {
        v.id() == self.id && v.is_init()
    }

    open spec fn metadata(self, v: cell::PointsTo<u64>) -> u64 {
        if v.is_init() {
            v.value()
        } else {
            0
        }
    }
}

fn main() {
    let (pcell, Tracked(permission)) = cell::PCell::new(7u64);
    let ghost pred = Pred { id: pcell.id() };
    let tracked (Tracked(instance), Tracked(mut state), Tracked(mut metadata), Tracked(mut valid)) =
        TxToks::Instance::new(permission, pred, Some(permission));
    proof {
        let tracked stolen = metadata.raw;
    }
}

} // verus!
