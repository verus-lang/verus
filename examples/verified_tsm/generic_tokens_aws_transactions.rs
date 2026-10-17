//! TVarToks and TxToks: a constant whose type is a type parameter, with a payload type that is not `'static`.
//!
//! The machine definitions are copied verbatim from the AWS concurrency
//! theory (transactions_proofs.rs), as inline modules with the crate's module names, and
//! verified on the generic interface with a client.
#![allow(unused_imports, non_snake_case, non_camel_case_types, dead_code)]
#![feature(sized_hierarchy)]
use vstd::prelude::*;

#[allow(unused_imports, non_snake_case, non_camel_case_types, dead_code)]
pub mod transactions_proofs {

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

    /// The fragment of a TVar's logical value that travels with the value protected
    /// by its mutex.
    ///
    /// `Synced(v)` means the physical value must also be `v`.  While a transaction
    /// holds the mutex, it changes the fragment to `Dirty(v)`, preserving the value
    /// observed at acquisition while permitting the physical cell to be modified.
    pub enum TVarFragment<T> {
        Synced(T),
        Dirty(T),
    }

    /// Whether the TVar is available for acquisition or currently held by a
    /// transaction.
    pub enum TVarPhase {
        Available,
        Held,
    }

    verified_tokenized_state_machine!(

    TVarToks<T> {
        fields {
            /// The authoritative logical value, intended to live in a client
            /// invariant.
            #[sharding(variable)]
            pub authoritative: T,

            /// The matching fragment stored under the TVar mutex.
            #[sharding(variable)]
            pub fragment: TVarFragment<T>,

            /// The acquisition-phase token carried by `TVarAccess`.
            #[sharding(variable)]
            pub phase: TVarPhase,
        }

        #[invariant]
        pub fn authoritative_agrees_with_fragment(&self) -> bool {
            match self.fragment {
                TVarFragment::Synced(v) => self.authoritative == v,
                TVarFragment::Dirty(v) => self.authoritative == v,
            }
        }

        #[invariant]
        pub fn phase_agrees_with_fragment(&self) -> bool {
            match self.phase {
                TVarPhase::Available => self.fragment is Synced,
                TVarPhase::Held => self.fragment is Dirty,
            }
        }

        init! {
            new(value: T) {
                init authoritative = value;
                init fragment = TVarFragment::Synced(value);
                init phase = TVarPhase::Available;
            }
        }

        transition! {
            begin() {
                require pre.phase is Available;
                require pre.fragment is Synced;
                update fragment = TVarFragment::Dirty(pre.fragment->Synced_0);
                update phase = TVarPhase::Held;
            }
        }

        transition! {
            commit(value: T) {
                require pre.phase is Held;
                require pre.fragment is Dirty;
                update authoritative = value;
                update fragment = TVarFragment::Synced(value);
                update phase = TVarPhase::Available;
            }
        }

        /// Finish a transaction that did not change the physical value.  The
        /// authoritative value is unchanged, so this transition does not require
        /// the authoritative token.
        transition! {
            finish_read() {
                require pre.phase is Held;
                require pre.fragment is Dirty;
                update fragment = TVarFragment::Synced(pre.fragment->Dirty_0);
                update phase = TVarPhase::Available;
            }
        }

        property! {
            observe() {
                assert(match pre.fragment {
                    TVarFragment::Synced(v) => pre.authoritative == v,
                    TVarFragment::Dirty(v) => pre.authoritative == v,
                });
            }
        }

        #[inductive(new)]
        fn new_inductive(post: Self, value: T) {
        }

        #[inductive(begin)]
        fn begin_inductive(pre: Self, post: Self) {
        }

        #[inductive(commit)]
        fn commit_inductive(pre: Self, post: Self, value: T) {
        }

        #[inductive(finish_read)]
        fn finish_read_inductive(pre: Self, post: Self) {
        }
    });

    pub trait TxPredicate<V, M>: Sized {
        spec fn inv(self, v: V) -> bool;

        spec fn metadata(self, v: V) -> M;
    }

    verified_tokenized_state_machine!(

    #[verified_local_ready(gather, withdraw, deposit, withdraw_mutating, deposit_mutating, mutate)]
    TxToks<V, M, Pred: TxPredicate<V, M>> {
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

}

/// Clients: the payload need not be `'static` (the constant `pred` mentions
/// only `Pred`; the instance owns its descriptor).
pub mod client {
    use crate::transactions_proofs::*;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verus! {

    pub struct Pointer;

    impl<'b> TxPredicate<&'b u64, nat> for Pointer {
        open spec fn inv(self, v: &'b u64) -> bool { *v > 0 }
        open spec fn metadata(self, v: &'b u64) -> nat { *v as nat }
    }

    /// A transaction over a borrowed value (`V = &'b u64`).
    pub proof fn round_trip<'b>(tracked v: &'b u64)
        requires *v > 0,
    {
        let tracked (Tracked(inst), Tracked(mut state), Tracked(mut metadata), Tracked(mut valid)) =
            TxToks::Instance::<&'b u64, nat, Pointer>::new(v, Pointer, Some(v));
        let tracked inst2 = inst.clone();
        assert(inst2.id() == inst.id() && inst2.pred() == Pointer);
        inst.gather(&mut state);
        let tracked (Ghost(orig), Tracked(w)) = inst.withdraw(&mut state, &metadata, &valid);
        assert(*w > 0 && metadata.value() == *w as nat);
        let ghost wv = w;
        inst2.deposit(wv, &mut state, &mut metadata, &mut valid, w);
        assert(state.value() is Gathering);
    }

    }
}

fn main() {}
