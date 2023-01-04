// rust_verify/tests/example.rs ignore
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::vec::*;
use pervasive::modes::*;
use pervasive::multiset::*;
use pervasive::map::*;
use pervasive::seq::*;
use pervasive::option::*;
use pervasive::atomic_ghost::*;

use state_machines_macros::tokenized_state_machine;
use option::Option::{Some, None};

verus!{

pub struct StoredType {
    placeholder: int
}

pub enum Flag {
    Unmapped,
    Loading,
    LoadingExcLock,
    Available,
    Claimed,
    Writeback,
    WritebackAndClaimed,
    WritebackAndPendingExcLock,
    PendingExcLock,
    ExcLockClean,
    ExcLockDirty,
}

// Threads are clumped together, each accessing one bucket or
// another. More buckets -> less contention among threads sharing that bucket.
pub type BucketId = nat;
// TODO(chris): can't 4 as nat! (issue #344)
//pub const RC_WIDTH: BucketId = 4; // nat;   // How many refcounting buckets we use.
pub open spec fn RC_WIDTH() -> BucketId { 4 as nat }

#[is_variant]
pub enum SharedState {
   SharedPending{bucket: Option<BucketId>},   // inc refcount
                                         // None means the shared lock is being acquired for
                                         // writeback.

   SharedPending2{bucket: Option<BucketId>},  // !free & !writelocked

   SharedObtained{bucket: Option<BucketId>, value: StoredType}, // !reading
}

impl SharedState {
    pub open spec fn get_bucket(self) -> Option<BucketId> {
        match self {
            SharedState::SharedPending{bucket} => bucket,
            SharedState::SharedPending2{bucket} => bucket,
            SharedState::SharedObtained{bucket, value: _} => bucket,
        }
    }
}

#[is_variant]
pub enum ExcState {
    ExcClaim{bucket: Option<BucketId>, value: StoredType},
    ExcPendingAwaitWriteback{bucket: Option<BucketId>, value: StoredType},
    ExcPending{bucket: Option<BucketId>, visited_count: BucketId, clean: bool, value: StoredType},
    ExcObtained{bucket: Option<BucketId>, clean: bool},
}

impl ExcState {
    // TODO: Ugh I hate this boilerplate stuff that would be free in Dafny.
    // verus! or is_variant should throw us a bone here.
    pub open spec fn get_bucket(self) -> Option<BucketId> {
        match self {
            ExcState::ExcClaim{bucket, value: _} => bucket,
            ExcState::ExcPendingAwaitWriteback{bucket, value: _} => bucket,
            ExcState::ExcPending{bucket, visited_count: _, clean: _, value: _} => bucket,
            ExcState::ExcObtained{bucket, clean: _} => bucket
        }
    }

//    pub open spec fn get_clean(self) -> bool
//        recommends self.is_ExcPending() || self.is_ExcObtained()
//    {
//        match self {
//            ExcState::ExcPending{bucket: _, visited_count: _, clean, value: _} => clean,
//            ExcState::ExcObtained{bucket: _, clean} => clean,
//            _ => false  // nonsense; recommends violated
//        }
//    }
}

// bucket is associated with the thread trying to acquire
// the shared lock, or None if it's just a prefetch for no particular
// outstanding get.
#[is_variant]
pub enum LoadingState {
    LoadingPending,  // set status bit to ExcLock | Loading,
    LoadingPendingCounted{bucket: Option<BucketId>},  // inc refcount
    LoadingObtained{bucket: Option<BucketId>},         // clear ExcLock bit
}

pub struct WritebackState {
    pub value: StoredType
}

} // verus!

tokenized_state_machine!{

RwLock {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<StoredType>,

        #[sharding(variable)]
        pub flag: Flag,

        #[sharding(map)]
        pub ref_counts: Map<BucketId, nat>,

        #[sharding(multiset)]
        pub shared_state: Multiset<SharedState>,

        #[sharding(option)]
        pub exc_state: Option<ExcState>,

        #[sharding(option)]
        pub loading_state: Option<LoadingState>,

        #[sharding(option)]
        pub writeback_state: Option<WritebackState>,
    }

    init!{
        initialize(init_value: StoredType) {
            init storage = Some(init_value);
            init flag = Flag::Unmapped;
            init ref_counts = Map::new(|bucket: BucketId| bucket < RC_WIDTH(), |bucket| 0);
            init shared_state = Multiset::empty();
            init exc_state = None;
            init loading_state = None;
            init writeback_state = None;
        }
    }

    transition!{
        take_writeback() {
            require pre.flag === Flag::Available;
            update flag = Flag::Writeback;
            birds_eye let value = pre.storage.get_Some_0();
            add writeback_state += Some(WritebackState{value: value});
        }
    }

    transition!{
        release_writeback() {
            remove writeback_state -= Some(let _);

            // TODO(travis): bug in match pre.flag "not found in this scope"
            let f = pre.flag;
            match f {
                Flag::Writeback => { update flag = Flag::Available; }
                Flag::WritebackAndPendingExcLock => { update flag = Flag::PendingExcLock; }
                Flag::WritebackAndClaimed => { update flag = Flag::Claimed; }
                _ => { assert false; }
            }
        }
    }

    transition!{
        bucketless_claim() {
            let f = pre.flag;
            match f {
                Flag::Available => { update flag = Flag::Claimed; }
                Flag::Writeback => { update flag = Flag::WritebackAndClaimed; }
                _ => { require false; }
            }
            birds_eye let value = pre.storage.get_Some_0();
            add exc_state += Some(ExcState::ExcClaim{bucket: None, value});
        }
    }

    transition!{
        shared_to_claim(shared_state: SharedState) {
            require let SharedState::SharedObtained{bucket, value} = shared_state;

            remove shared_state -= { shared_state };

            let f = pre.flag;
            match f {
                Flag::Available => { update flag = Flag::Claimed; }
                Flag::Writeback => { update flag = Flag::WritebackAndClaimed; }
                _ => { require false; }
            }

            add exc_state += Some(ExcState::ExcClaim{bucket: bucket, value});
        }
    }

    transition!{
        claim_to_pending() {
            remove exc_state -= Some(let ExcState::ExcClaim{bucket, value});
            add exc_state += Some(ExcState::ExcPendingAwaitWriteback{bucket, value});

            let f = pre.flag;
            match f {
                Flag::Claimed => { update flag = Flag::PendingExcLock; }
                Flag::WritebackAndClaimed => { update flag = Flag::WritebackAndPendingExcLock; }
                _ => { assert false; }
            }
        }
    }

    transition!{
        take_exc_lock_finish_writeback(clean: bool) {
            require pre.flag !== Flag::Writeback && pre.flag !== Flag::WritebackAndPendingExcLock;

            remove exc_state -= Some(let ExcState::ExcPendingAwaitWriteback{bucket, value});
            add exc_state += Some(ExcState::ExcPending{bucket, visited_count: 0, clean, value});

            update flag = if clean { Flag::ExcLockClean } else { Flag::ExcLockDirty };

            // TODO: inside a transition!, "assert" means "check against inv, then export as
            // ensures".  Give it a new name?
            assert pre.flag === Flag::PendingExcLock;
        }
    }

    pub open spec fn valid_bucket(bucket: Option<BucketId>) -> bool {
        match bucket {
            Some(bucketId) => bucketId < RC_WIDTH(),
            None => true
        }
    } 

    #[invariant]
    pub spec fn storage_some_invariant(&self) -> bool {
        let withdrawn = {
            ||| self.exc_state.is_Some() && self.exc_state.get_Some_0().is_ExcObtained()
            ||| self.loading_state.is_Some()
        };
        self.storage.is_Some() == !withdrawn
    }

    #[invariant]
    pub spec fn exc_state_invariants(&self) -> bool {
        match self.exc_state {
            Some(ExcState::ExcPendingAwaitWriteback{bucket, value}) => {
                &&& self.loading_state.is_None()
                &&& Self::valid_bucket(bucket)
                &&& Some(value) === self.storage
            }
            Some(ExcState::ExcClaim{bucket, value}) => {
                &&& self.loading_state.is_None()
                &&& Self::valid_bucket(bucket)
                &&& Some(value) === self.storage
            }
            Some(ExcState::ExcPending{bucket, visited_count, clean, value}) => {
                &&& self.loading_state.is_None()
                &&& self.writeback_state.is_None()
                &&& visited_count <= RC_WIDTH()
                &&& Self::valid_bucket(bucket)
                &&& Some(value) === self.storage
            }
            Some(ExcState::ExcObtained{bucket, clean}) => {
                &&& self.loading_state.is_None()
                &&& self.writeback_state.is_None()
                &&& Self::valid_bucket(bucket)
            }
            None => true
        }
    }

    #[invariant]
    pub spec fn writeback_state_invariants(&self) -> bool {
        match self.writeback_state {
            Some(WritebackState{value}) => {
                &&& self.loading_state.is_None()
                &&& Some(value) === self.storage
            }
            None => true
        }
    }

    #[invariant]
    pub spec fn loading_state_invariants(&self) -> bool {
        match self.loading_state {
            Some(LoadingState::LoadingPending) => {
                &&& self.writeback_state.is_None()
            }
            Some(LoadingState::LoadingPendingCounted{bucket}) => {
                match bucket {
                    Some(bucketId) => {
                        &&& self.writeback_state.is_None()
                        &&& bucketId <= RC_WIDTH()
                    }
                    // TODO(travis): In Seagull RwLock Inv, ReadPendingCounted has 0 <= bucket. ?
                    None => false
                }
            }
            Some(LoadingState::LoadingObtained{bucket}) => {
                &&& Self::valid_bucket(bucket)
            }
            None => true
        }
    }

    pub open spec fn count_shared_refs(shared: Multiset<SharedState>, bucket: BucketId) -> nat {
        shared.filter(|shared_state: SharedState| shared_state.get_bucket() === Some(bucket)).len()
    }

    pub open spec fn count_exc_refs(exc_state: Option<ExcState>, bucket: BucketId) -> nat {
        match exc_state {
            Some(e) => if e.get_bucket() === Some(bucket) { 1 } else { 0 },
            None => 0
        }
    }

    pub open spec fn count_loading_refs(loading_state: Option<LoadingState>, bucket: BucketId) -> nat {
        match loading_state {
            Some(LoadingState::LoadingPendingCounted{bucket}) => 1,
            Some(LoadingState::LoadingObtained{bucket}) => 1,
            _ => 0
        }
    }

    pub open spec fn count_all_refs(self, bucket: BucketId) -> nat {
        Self::count_shared_refs(self.shared_state, bucket)
            + Self::count_exc_refs(self.exc_state, bucket)
            + Self::count_loading_refs(self.loading_state, bucket)
    }

    #[invariant]
    pub spec fn ref_count_invariant(&self) -> bool {
        // TODO(travis): suggested resolution
        //     (example: forall|i: int, j: int| #![auto] f(i) && g(i) && h(j))
        // is rejected with:
        //    error: an inner attribute is not permitted in this context
        //    error: cannot find attribute `auto` in this scope
        &&& forall(|bucket: BucketId| bucket < RC_WIDTH()
            ==> #[trigger] self.ref_counts.dom().contains(bucket))
        &&& forall(|bucket: BucketId| bucket < RC_WIDTH()
            ==> self.ref_counts[bucket] === self.count_all_refs(bucket))
    }

    #[invariant]
    pub spec fn flag_invariant(&self) -> bool {
        match self.flag {
            Flag::Unmapped => {
                &&& self.exc_state.is_None()
                &&& self.loading_state.is_None()
                &&& self.writeback_state.is_None()
            }
            Flag::Loading => {
                &&& match self.loading_state {
                    Some(LoadingState::LoadingObtained{bucket: _}) => true,
                    _ => false
                }
                &&& self.writeback_state.is_None()
            }
            Flag::LoadingExcLock => {
                &&& match self.loading_state {
                    Some(LoadingState::LoadingPending) => true,
                    Some(LoadingState::LoadingPendingCounted{bucket: _}) => true,
                    _ => false
                }
                &&& self.writeback_state.is_None()
            }
            Flag::Available => {
                &&& self.exc_state.is_None()
                &&& self.loading_state.is_None()
                &&& self.writeback_state.is_None()
            }
            Flag::Claimed => {
                &&& self.exc_state.is_Some()
                &&& self.exc_state.get_Some_0().is_ExcClaim()
                &&& self.writeback_state.is_None()
            }
            Flag::Writeback => {
                &&& self.exc_state.is_None()
                &&& self.loading_state.is_None()
                &&& self.writeback_state.is_Some()
            }
            Flag::WritebackAndClaimed => {
                &&& self.exc_state.is_Some()
                &&& self.exc_state.get_Some_0().is_ExcClaim()
                &&& self.writeback_state.is_Some()
            }
            Flag::WritebackAndPendingExcLock => {
                &&& self.exc_state.is_Some()
                &&& self.exc_state.get_Some_0().is_ExcPendingAwaitWriteback()
                &&& self.writeback_state.is_Some()
            }
            Flag::PendingExcLock => {
                &&& self.exc_state.is_Some()
                &&& self.exc_state.get_Some_0().is_ExcPendingAwaitWriteback()
                &&& self.writeback_state.is_None()
            }
            Flag::ExcLockClean => {
                &&& match self.exc_state {
                    Some(ExcState::ExcPending{bucket: _, visited_count: _, clean, value: _}) => clean,
                    Some(ExcState::ExcObtained{bucket: _, clean}) => clean,
                    _ => false
                }
                &&& self.writeback_state.is_None()
            }
            Flag::ExcLockDirty => {
                &&& match self.exc_state {
                    Some(ExcState::ExcPending{bucket: _, visited_count: _, clean, value: _}) => !clean,
                    Some(ExcState::ExcObtained{bucket: _, clean}) => !clean,
                    _ => false
                }
                &&& self.writeback_state.is_None()
            }
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, init_value: StoredType) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH()
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {

            let filtered = post.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === Some(bucket));
            assert_multisets_equal!(filtered, Multiset::empty());
        }
    }
   
    #[inductive(take_writeback)]
    fn take_writeback_inductive(pre: Self, post: Self) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH()
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
    }
   
    #[inductive(release_writeback)]
    fn release_writeback_inductive(pre: Self, post: Self) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH()
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
    }
   
    #[inductive(bucketless_claim)]
    fn bucketless_claim_inductive(pre: Self, post: Self) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH()
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
    }
   
    #[inductive(shared_to_claim)]
    fn shared_to_claim_inductive(pre: Self, post: Self, shared_state: SharedState) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH()
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if Some(bucket) === shared_state.get_bucket() {
                let pre_filtered = pre.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === Some(bucket));
                let post_filtered = post.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === Some(bucket));

//                assert_multisets_equal!(post_filtered.insert(shared_state), pre_filtered);

                assert_multisets_equal!(pre_filtered.remove(shared_state), post_filtered);
                
//                assert(pre_filtered === post_filtered.insert(shared_state));
                        
                assert(Self::count_shared_refs(post.shared_state, bucket)
                        == Self::count_shared_refs(pre.shared_state, bucket) - 1);
                assert(Self::count_exc_refs(post.exc_state, bucket)
                        == Self::count_exc_refs(pre.exc_state, bucket) + 1);
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
            } else {
                assume(false);
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
            }
        }
        assume(post.exc_state_invariants());
    }
   
    #[inductive(claim_to_pending)]
    fn claim_to_pending_inductive(pre: Self, post: Self) { }
   
    #[inductive(take_exc_lock_finish_writeback)]
    fn take_exc_lock_finish_writeback_inductive(pre: Self, post: Self, clean: bool) { }

}

} //tokenized_state_machine

fn main() { }
