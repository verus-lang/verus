// rust_verify/tests/example.rs ignore
#![allow(unused_imports)]
use vstd::atomic_ghost::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::option::*;
use vstd::seq::*;
use vstd::vec::*;
use vstd::{pervasive::*, prelude::*, *};

use option::Option::{None, Some};
use state_machines_macros::tokenized_state_machine;

verus! {

pub struct StoredType {
    placeholder: int,
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
pub spec const RC_WIDTH: BucketId = 4;
  // How many refcounting buckets we use.
#[is_variant]
pub enum SharedState {
    Pending { bucket: BucketId },  // inc refcount
    // None means the shared lock is being acquired for
    // writeback.
    Pending2 { bucket: BucketId },  // !free & !writelocked
    Obtained { bucket: BucketId, value: StoredType },  // !reading
}

impl SharedState {
    pub open spec fn get_bucket(self) -> BucketId {
        match self {
            SharedState::Pending { bucket } => bucket,
            SharedState::Pending2 { bucket } => bucket,
            SharedState::Obtained { bucket, value: _ } => bucket,
        }
    }
}

#[is_variant]
pub enum ExcState {
    Claim { bucket: Option<BucketId>, value: StoredType },
    PendingAwaitWriteback { bucket: Option<BucketId>, value: StoredType },
    Pending { bucket: Option<BucketId>, visited_count: BucketId, clean: bool, value: StoredType },
    Obtained { bucket: Option<BucketId>, clean: bool },
}

impl ExcState {
    // TODO: Ugh I hate this boilerplate stuff that would be free in Dafny.
    // verus! or is_variant should throw us a bone here.
    pub open spec fn get_bucket(self) -> Option<BucketId> {
        match self {
            ExcState::Claim { bucket, value: _ } => bucket,
            ExcState::PendingAwaitWriteback { bucket, value: _ } => bucket,
            ExcState::Pending { bucket, visited_count: _, clean: _, value: _ } => bucket,
            ExcState::Obtained { bucket, clean: _ } => bucket,
        }
    }
    //    pub open spec fn get_clean(self) -> bool
    //        recommends self.is_Pending() || self.is_Obtained()
    //    {
    //        match self {
    //            ExcState::Pending{bucket: _, visited_count: _, clean, value: _} => clean,
    //            ExcState::Obtained{bucket: _, clean} => clean,
    //            _ => false  // nonsense; recommends violated
    //        }
    //    }

}

// bucket is associated with the thread trying to acquire
// the shared lock, or None if it's just a prefetch for no particular
// outstanding get.
#[is_variant]
pub enum LoadingState {
    Pending,  // set status bit to ExcLock | Loading,
    PendingCounted { bucket: Option<BucketId> },  // inc refcount
    Obtained { bucket: Option<BucketId> },  // clear ExcLock bit
}

pub struct WritebackState {
    pub value: StoredType,
}

} // verus!
tokenized_state_machine! {

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
            init ref_counts = Map::new(|bucket: BucketId| bucket < RC_WIDTH, |bucket| 0);
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
            add exc_state += Some(ExcState::Claim{bucket: None, value});
        }
    }

    transition!{
        shared_to_claim(shared_state: SharedState) {
            require let SharedState::Obtained{bucket, value} = shared_state;

            remove shared_state -= { shared_state };

            let f = pre.flag;
            match f {
                Flag::Available => { update flag = Flag::Claimed; }
                Flag::Writeback => { update flag = Flag::WritebackAndClaimed; }
                _ => { require false; }
            }

            add exc_state += Some(ExcState::Claim{bucket: Some(bucket), value});
        }
    }

    transition!{
        claim_to_pending() {
            remove exc_state -= Some(let ExcState::Claim{bucket, value});
            add exc_state += Some(ExcState::PendingAwaitWriteback{bucket, value});

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

            remove exc_state -= Some(let ExcState::PendingAwaitWriteback{bucket, value});
            add exc_state += Some(ExcState::Pending{bucket, visited_count: 0, clean, value});

            update flag = if clean { Flag::ExcLockClean } else { Flag::ExcLockDirty };

            // TODO: inside a transition!, "assert" means "check against inv, then export as
            // ensures".  Give it a new name?
            assert pre.flag === Flag::PendingExcLock;
        }
    }

    transition!{
        take_exc_lock_check_ref_count() {
            remove exc_state -= Some(let ExcState::Pending{bucket, visited_count, clean, value});
            require visited_count < RC_WIDTH;
            add exc_state += Some(ExcState::Pending{bucket, visited_count: visited_count+1, clean, value});
            // Expect a single reference--mine--at my bucket.
            let expected_rc = if Some(visited_count) === bucket { 1 } else { 0 };

            // TODO(travis): change have syntax? have ref_counts[visited_count] == expected_rc;
            have ref_counts >= [visited_count => expected_rc];
        }
    }

    transition!{
        withdraw_take_exc_lock_finish() {
            remove exc_state -= Some(let ExcState::Pending{bucket, visited_count, clean, value});
            require visited_count == RC_WIDTH;
            add exc_state += Some(ExcState::Obtained{bucket, clean});
            withdraw storage -= Some(value);
        }
    }

    // This step is probably useless; could downgrade to claim, then discard the claim.
    transition!{
        deposit_downgrade_exc_lock(value: StoredType) {
            remove exc_state -= Some(let ExcState::Obtained{bucket, clean});
            require bucket.is_Some();    // shared requires a real bucket to represent ref_count
            update flag = Flag::Available;
            deposit storage += Some(value);
            add shared_state += { SharedState::Obtained{bucket: bucket.get_Some_0(), value} };
        }
    }

    transition!{
        deposit_downgrade_exc_lock_to_claim(value: StoredType) {
            remove exc_state -= Some(let ExcState::Obtained{bucket, clean});
            require bucket.is_Some();    // TODO(travis): maybe unecessary? ExcState::Claim allows a None bucket
            update flag = Flag::Claimed;
            deposit storage += Some(value);
            add exc_state += Some(ExcState::Claim{bucket, value});
        }
    }

    transition!{
        withdraw_alloc() {
            require pre.flag === Flag::Unmapped;
            update flag = Flag::LoadingExcLock;
            add loading_state += Some(LoadingState::Pending);
            withdraw storage -= Some(let _);    // SOME data came out from behind the lock, but who knows what
        }
    }

    transition!{
        withdraw_alloc_no_refcount() {
            require pre.flag === Flag::Unmapped;
            update flag = Flag::Loading;
            add loading_state += Some(LoadingState::Obtained{bucket: None});
            withdraw storage -= Some(let _);    // SOME data came out from behind the lock, but who knows what
        }
    }

    transition!{
        loading_inc_count(bucket: BucketId) {
            require bucket < RC_WIDTH;
            remove loading_state -= Some(LoadingState::Pending{});
            remove ref_counts -= [ bucket => let pre_count ];

            add loading_state += Some(LoadingState::PendingCounted{bucket: Some(bucket)});
            add ref_counts += [ bucket => pre_count + 1 ];
        }
    }

    transition!{
        obtain_loading() {
            remove loading_state -= Some(let LoadingState::PendingCounted{bucket});
            add loading_state += Some(LoadingState::Obtained{bucket});
            update flag = Flag::Loading;
        }
    }

    // TODO(travis): error: unable to prove inherent safety condition: the given value to be withdrawn must be stored before the withdraw
//    transition!{
//        load_pending_to_exc(clean: bool, stored_garbage: StoredType) {
//            remove loading_state -= Some(let LoadingState::PendingCounted{bucket});
//            add exc_state += Some(ExcState::Obtained{bucket, clean});
//            update flag = if clean { Flag::ExcLockClean } else { Flag::ExcLockDirty };
//            // disk load routine will replace stored garbage with disk contents, but that's what's
//            // there now, so we have to maintain the lock invariant connecting ghost value to real.
//            withdraw storage -= Some(stored_garbage);
//        }
//    }

    // a read-only transition that explains that having a shared references functions as a guard to
    // read the storage.
//    property!{
//        borrow_shared_obtained(ss: SharedState) {
//            require ss.is_Obtained();
//            have shared_state >= { ss };
//            // TODO(travis): error: unable to prove inherent safety condition: the value being guarded must be stored
//            guard storage >= Some(ss.get_Obtained_value());
//        }
//    }

//    property!{
//        borrow_writeback() {
//            // TODO(travis): "unreachable pattern"
//            have writeback_state >= Some(let WritebackState{value});
//            guard storage >= Some(value);
//        }
//    }

    transition!{
        obtain_loading_no_refcount() {
            remove loading_state -= Some(LoadingState::Pending{});
            add loading_state += Some(LoadingState::Obtained{bucket: None});
            update flag = Flag::Loading;
        }
    }

    transition!{
        deposit_loading_to_shared(value: StoredType) {
            remove loading_state -= Some(let LoadingState::Obtained{bucket});
            require bucket.is_Some();
            update flag = Flag::Available;
            deposit storage += Some(value);
            add shared_state += { SharedState::Obtained{bucket: bucket.get_Some_0(), value} };
        }
    }

    transition!{
        deposit_loading_to_done(value: StoredType) {
            remove loading_state -= Some(let LoadingState::Obtained{bucket});
            require bucket.is_Some();
            update flag = Flag::Available;
            deposit storage += Some(value);
        }
    }

    transition!{
        exc_inc_count(bucket: BucketId) {
            require bucket < RC_WIDTH;
            remove exc_state -= Some(let ExcState::Obtained{bucket: none_bucket, clean});
            require none_bucket === None;
            remove ref_counts -= [ bucket => let pre_count ];

            add exc_state += Some(ExcState::Obtained{bucket: Some(bucket), clean});
            add ref_counts += [ bucket => pre_count + 1 ];

        }
    }

    transition!{
        shared_inc_count(bucket: BucketId) {
            require bucket < RC_WIDTH;
            remove ref_counts -= [ bucket => let pre_count ];
            add ref_counts += [ bucket => pre_count + 1 ];
            add shared_state += { SharedState::Pending{bucket} };
        }
    }

    transition!{
        shared_dec_count_pending(bucket: BucketId) {
            require bucket < RC_WIDTH;
            remove ref_counts -= [ bucket => let pre_count ];
            remove shared_state -= { SharedState::Pending{bucket} };
            add ref_counts += [ bucket => (pre_count - 1) as nat ];
        }
    }

    transition!{
        shared_dec_count_pending2(bucket: BucketId) {
            require bucket < RC_WIDTH;
            remove ref_counts -= [ bucket => let pre_count ];
            remove shared_state -= { SharedState::Pending2{bucket} };
            add ref_counts += [ bucket => (pre_count - 1) as nat ];
        }
    }

    transition!{
        shared_dec_count_obtained(bucket: BucketId, value: StoredType) {
            require bucket < RC_WIDTH;
            remove ref_counts -= [ bucket => let pre_count ];
            remove shared_state -= { SharedState::Obtained{bucket, value} };
            add ref_counts += [ bucket => (pre_count - 1) as nat ];
        }
    }

    transition!{
        shared_check_exc(bucket: BucketId, value: StoredType) {
            // TODO(travis): Pretty weird that we need 'pre.' here, but not in other directives.
            require {
                ||| pre.flag === Flag::Available
                ||| pre.flag === Flag::Writeback
                ||| pre.flag === Flag::Claimed
                ||| pre.flag === Flag::WritebackAndClaimed
                ||| pre.flag === Flag::Loading};
            remove shared_state -= { SharedState::Pending{bucket} };
            add shared_state += { SharedState::Pending2{bucket} };
        }
    }

    transition!{
        shared_check_loading(bucket: BucketId) {
            require bucket < RC_WIDTH;
            require pre.flag !== Flag::Loading;

            remove shared_state -= { SharedState::Pending2{bucket} };
            birds_eye let value = pre.storage.get_Some_0();
            add shared_state += { SharedState::Obtained{bucket, value} };
        }
    }

    //////////////////////////////////////////////////////////////////////////////
    // invariants
    //////////////////////////////////////////////////////////////////////////////

    pub open spec fn valid_bucket(bucket: Option<BucketId>) -> bool {
        match bucket {
            Some(bucketId) => bucketId < RC_WIDTH,
            None => true
        }
    }

    #[invariant]
    pub spec fn storage_some_invariant(&self) -> bool {
        let withdrawn = {
            ||| self.exc_state.is_Some() && self.exc_state.get_Some_0().is_Obtained()
            ||| self.loading_state.is_Some()
        };
        self.storage.is_Some() == !withdrawn
    }

    #[invariant]
    pub spec fn exc_state_invariants(&self) -> bool {
        match self.exc_state {
            Some(ExcState::PendingAwaitWriteback{bucket, value}) => {
                &&& self.loading_state.is_None()
                &&& Self::valid_bucket(bucket)
                &&& Some(value) === self.storage
            }
            Some(ExcState::Claim{bucket, value}) => {
                &&& self.loading_state.is_None()
                &&& Self::valid_bucket(bucket)
                &&& Some(value) === self.storage
            }
            Some(ExcState::Pending{bucket, visited_count, clean, value}) => {
                &&& self.loading_state.is_None()
                &&& self.writeback_state.is_None()
                &&& visited_count <= RC_WIDTH
                &&& Self::valid_bucket(bucket)
                &&& Some(value) === self.storage
            }
            Some(ExcState::Obtained{bucket, clean}) => {
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
            Some(LoadingState::Pending) => {
                &&& self.writeback_state.is_None()
            }
            Some(LoadingState::PendingCounted{bucket}) => {
                match bucket {
                    Some(bucketId) => {
                        &&& self.writeback_state.is_None()
                        &&& bucketId < RC_WIDTH
                    }
                    // TODO(travis): In Seagull RwLock Inv, ReadPendingCounted has 0 <= bucket. ?
                    None => false
                }
            }
            Some(LoadingState::Obtained{bucket}) => {
                &&& Self::valid_bucket(bucket)
            }
            None => true
        }
    }

    pub open spec fn filter_shared_refs(shared: Multiset<SharedState>, bucket: BucketId) -> Multiset<SharedState> {

        shared.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket)
    }

    pub open spec fn count_shared_refs(shared: Multiset<SharedState>, bucket: BucketId) -> nat {
        Self::filter_shared_refs(shared, bucket).len()
    }

    pub open spec fn count_exc_refs(exc_state: Option<ExcState>, bucket: BucketId) -> nat {
        match exc_state {
            Some(e) => if e.get_bucket() === Some(bucket) { 1 } else { 0 },
            None => 0
        }
    }

    pub open spec fn count_loading_refs(loading_state: Option<LoadingState>, match_bucket: BucketId) -> nat {
        match loading_state {
            Some(LoadingState::PendingCounted{bucket}) => if bucket===Some(match_bucket) { 1 } else { 0 },
            Some(LoadingState::Obtained{bucket}) => if bucket===Some(match_bucket) { 1 } else { 0 },
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
        &&& forall(|bucket: BucketId| bucket < RC_WIDTH
            ==> #[trigger] self.ref_counts.dom().contains(bucket))
        &&& forall(|bucket: BucketId| bucket < RC_WIDTH
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
                    Some(LoadingState::Obtained{bucket: _}) => true,
                    _ => false
                }
                &&& self.writeback_state.is_None()
            }
            Flag::LoadingExcLock => {
                &&& match self.loading_state {
                    Some(LoadingState::Pending) => true,
                    Some(LoadingState::PendingCounted{bucket: _}) => true,
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
                &&& self.exc_state.get_Some_0().is_Claim()
                &&& self.writeback_state.is_None()
            }
            Flag::Writeback => {
                &&& self.exc_state.is_None()
                &&& self.loading_state.is_None()
                &&& self.writeback_state.is_Some()
            }
            Flag::WritebackAndClaimed => {
                &&& self.exc_state.is_Some()
                &&& self.exc_state.get_Some_0().is_Claim()
                &&& self.writeback_state.is_Some()
            }
            Flag::WritebackAndPendingExcLock => {
                &&& self.exc_state.is_Some()
                &&& self.exc_state.get_Some_0().is_PendingAwaitWriteback()
                &&& self.writeback_state.is_Some()
            }
            Flag::PendingExcLock => {
                &&& self.exc_state.is_Some()
                &&& self.exc_state.get_Some_0().is_PendingAwaitWriteback()
                &&& self.writeback_state.is_None()
            }
            Flag::ExcLockClean => {
                &&& match self.exc_state {
                    Some(ExcState::Pending{bucket: _, visited_count: _, clean, value: _}) => clean,
                    Some(ExcState::Obtained{bucket: _, clean}) => clean,
                    _ => false
                }
                &&& self.writeback_state.is_None()
            }
            Flag::ExcLockDirty => {
                &&& match self.exc_state {
                    Some(ExcState::Pending{bucket: _, visited_count: _, clean, value: _}) => !clean,
                    Some(ExcState::Obtained{bucket: _, clean}) => !clean,
                    _ => false
                }
                &&& self.writeback_state.is_None()
            }
        }
    }

    pub open spec fn shared_state_valid(&self, shared_state: SharedState) -> bool {
        &&& shared_state.get_bucket() < RC_WIDTH
        &&& match shared_state {
            SharedState::Pending{bucket} => true,
            SharedState::Pending2{bucket} => {
                &&& match self.exc_state {
                    Some(ExcState::Obtained{..}) => false,
                    Some(ExcState::Pending{visited_count, ..}) => visited_count <= bucket,
                    _ => true
                }
                &&& match self.loading_state {
                    Some(LoadingState::Pending) => false,
                    Some(LoadingState::PendingCounted{..}) => false,
                    _ => true
                }
                &&& self.flag !== Flag::Unmapped
            }
            SharedState::Obtained{bucket, value} => {
                &&& Some(value) === self.storage
                &&& match self.exc_state {
                    Some(ExcState::Obtained{..}) => false,
                    Some(ExcState::Pending{visited_count, ..}) => visited_count <= bucket,
                    _ => true
                }
                &&& self.loading_state.is_None()
                &&& self.flag !== Flag::Unmapped
            }
        }
    }

    #[invariant]
    pub spec fn shared_storage_invariant(&self) -> bool {
        forall(|ss| self.shared_state.count(ss) > 0 ==> {
            self.shared_state_valid(ss)
        })
    }

    //////////////////////////////////////////////////////////////////////
    // Helpers
    //////////////////////////////////////////////////////////////////////

    proof fn ref_count_invariant_lemma(pre: Self, post: Self)
        requires
            pre.ref_count_invariant(),
            forall(|bucket: BucketId| bucket < RC_WIDTH ==> pre.count_all_refs(bucket) === post.count_all_refs(bucket)),
            post.ref_counts === pre.ref_counts,
        ensures
            post.ref_count_invariant(),
    {
//        assert forall |bucket: BucketId| bucket < RC_WIDTH
//            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
//            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
//        }
    }


// TODO(jonh): figure out how to set up this helper
//    proof fn shared_storage_invariant_lemma(pre: Self, post: Self)
//        requires
//            pre.shared_storage_invariant(),
//            forall(|ss| post.shared_state.count(ss) > 0 ==> {
//                ||| post.shared_state.count(ss) === pre.shared_state.count(ss)
//                ||| post.shared_state_valid(ss)
//            }),
//            post.shared_state === pre.shared_state,
//            post.storage === pre.storage,
//        ensures
//            post.shared_storage_invariant()
//    {
//        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
//            assert(pre.shared_state_valid(ss));
//        }
//    }

    //////////////////////////////////////////////////////////////////////
    // init
    //////////////////////////////////////////////////////////////////////

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, init_value: StoredType) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {

            let filtered = post.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket);
            assert_multisets_equal!(filtered, Multiset::empty());
        }
    }

    #[inductive(take_writeback)]
    fn take_writeback_inductive(pre: Self, post: Self) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss)); // triggertown
        }
    }

    #[inductive(release_writeback)]
    fn release_writeback_inductive(pre: Self, post: Self) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss)); // triggertown
        }
    }

    #[inductive(bucketless_claim)]
    fn bucketless_claim_inductive(pre: Self, post: Self) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss)); // triggertown
        }
    }

    #[inductive(shared_to_claim)]
    fn shared_to_claim_inductive(pre: Self, post: Self, shared_state: SharedState) {
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {

            let pre_filtered = pre.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket);
            let post_filtered = post.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket);

            if bucket === shared_state.get_bucket() {

                assert_multisets_equal!(pre_filtered.remove(shared_state), post_filtered);
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
            } else {
                assert_multisets_equal!(pre_filtered, post_filtered);
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
            }
        }
        assert(pre.shared_state_valid(shared_state));

        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(claim_to_pending)]
    fn claim_to_pending_inductive(pre: Self, post: Self) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(take_exc_lock_finish_writeback)]
    fn take_exc_lock_finish_writeback_inductive(pre: Self, post: Self, clean: bool) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(take_exc_lock_check_ref_count)]
    fn take_exc_lock_check_ref_count_inductive(pre: Self, post: Self) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
            let pre_exc = pre.exc_state.get_Some_0();
            let pre_visited_count = pre_exc.get_Pending_visited_count();
            let post_exc = post.exc_state.get_Some_0();
            let post_visited_count = post_exc.get_Pending_visited_count();

            // This proof is a little clunky; it wants to be a match with a complex (|) pattern.
            let bucket = ss.get_bucket();
            if ss.is_Pending2() || ss.is_Obtained() {
                if bucket == pre_visited_count {
                    let expected_rc:nat = if Some(pre_visited_count) === pre_exc.get_Pending_bucket() { 1 } else { 0 };
                    assert(post.count_all_refs(bucket) == expected_rc); // trigger
                    let post_counted_refs = post.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket);
                    assert(Multiset::singleton(ss).le(post_counted_refs));
                    assert(false);
                }
            }
            assert(post.shared_state_valid(ss));
        }
    }

    #[inductive(withdraw_take_exc_lock_finish)]
    fn withdraw_take_exc_lock_finish_inductive(pre: Self, post: Self) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(deposit_downgrade_exc_lock)]
    fn deposit_downgrade_exc_lock_inductive(pre: Self, post: Self, value: StoredType) {
        let pre_exc = pre.exc_state.get_Some_0();
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            let new_ss = SharedState::Obtained{bucket: pre_exc.get_bucket().get_Some_0(), value};
            if Some(bucket) === pre_exc.get_Obtained_bucket() {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket).insert(new_ss));
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
            }
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        // shared_storage_invariant
        let new_ss = SharedState::Obtained{bucket: pre_exc.get_Obtained_bucket().get_Some_0(), value};
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            if ss !== new_ss {
                assert(pre.shared_state_valid(ss));
            }
        }
    }

    #[inductive(deposit_downgrade_exc_lock_to_claim)]
    fn deposit_downgrade_exc_lock_to_claim_inductive(pre: Self, post: Self, value: StoredType) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(withdraw_alloc)]
    fn withdraw_alloc_inductive(pre: Self, post: Self) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    // TODO(jonh): getting pretty sad that we have to copy/paste the same proof fifty times
    #[inductive(withdraw_alloc_no_refcount)]
    fn withdraw_alloc_no_refcount_inductive(pre: Self, post: Self) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(loading_inc_count)]
    fn loading_inc_count_inductive(pre: Self, post: Self, bucket: BucketId) {
        // ref_count_invariant
        let loading_bucket = bucket;
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket == loading_bucket {
                assert(post.ref_counts[bucket] === pre.count_all_refs(bucket)+1);   // trigger
            } else {
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            }
        }
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(obtain_loading)]
    fn obtain_loading_inductive(pre: Self, post: Self) {
        Self::ref_count_invariant_lemma(pre, post);
        // shared_storage_invariant
        // Self::shared_storage_invariant_lemma(pre, post);
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

//    #[inductive(load_pending_to_exc)]
//    fn load_pending_to_exc_inductive(pre: Self, post: Self, clean: bool, stored_garbage: StoredType) {
//        Self::ref_count_invariant_lemma(pre, post);
//        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
//            assert(pre.shared_state_valid(ss));
//        }
////        let withdrawn = {
////            ||| (post.exc_state.is_Some() && post.exc_state.get_Some_0().is_Obtained())
////            ||| post.loading_state.is_Some()
////        };
////        assert(post.exc_state.is_Some() && post.exc_state.get_Some_0().is_Obtained());
//////        assert(!withdrawn);
//////        assert(post.storage === Some(stored_garbage));
//////        assert(post.storage.is_Some());
//////        assert(post.storage.is_Some() == !withdrawn);
////        assert(post.storage_some_invariant());
//    }

    #[inductive(obtain_loading_no_refcount)]
    fn obtain_loading_no_refcount_inductive(pre: Self, post: Self) {
        Self::ref_count_invariant_lemma(pre, post);
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(deposit_loading_to_shared)]
    fn deposit_loading_to_shared_inductive(pre: Self, post: Self, value: StoredType) {
        let pre_loading = pre.loading_state.get_Some_0();
        let loading_bucket = pre_loading.get_Obtained_bucket();
        let new_ss = SharedState::Obtained{bucket: loading_bucket.get_Some_0(), value};

        // This proof of ref_count_invariant_lemma is nearly copy-pasted from the one in
        // loading_inc_count_inductive. :v/ My attempt to factor it out failed.
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if Some(bucket) === loading_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket).insert(new_ss));
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
            }
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }

        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            if ss === new_ss {
                assert(post.shared_state_valid(ss));
            } else {
                assert(pre.shared_state_valid(ss));
            }
        }
    }

    #[inductive(deposit_loading_to_done)]
    fn deposit_loading_to_done_inductive(pre: Self, post: Self, value: StoredType) {
        // This proof of ref_count_invariant_lemma is nearly copy-pasted from the one in
        // loading_inc_count_inductive. :v/ My attempt to factor it out failed.
        let pre_loading = pre.loading_state.get_Some_0();
        let loading_bucket = pre_loading.get_Obtained_bucket();
        let new_ss = SharedState::Obtained{bucket: loading_bucket.get_Some_0(), value};
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if Some(bucket) === loading_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(post.count_all_refs(bucket) + 1 === pre.count_all_refs(bucket));
                assume(false);
                assert(post.count_all_refs(bucket) === post.ref_counts[bucket]);
                // TODO(travis): Mystery: the count_all_refs really DOES change! And the ref_count
                // doesn't! And yet your seagull .dfy transition passes!?
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(post.count_all_refs(bucket) === pre.count_all_refs(bucket));
            }
        }

        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(exc_inc_count)]
    fn exc_inc_count_inductive(pre: Self, post: Self, bucket: BucketId) {
        let new_bucket = bucket;
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket === new_bucket {
                assert(pre.count_all_refs(bucket) + 1 === post.count_all_refs(bucket));
            } else {
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
            }
        }

        // boilerplate shared_storage_invariant proof
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(shared_inc_count)]
    fn shared_inc_count_inductive(pre: Self, post: Self, bucket: BucketId) {
        let new_bucket = bucket;
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket === new_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket).insert(SharedState::Pending{bucket}));
                assert(pre.count_all_refs(bucket) + 1 === post.count_all_refs(bucket)); // trigger
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            }
        }

        // boilerplate shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(shared_dec_count_pending)]
    fn shared_dec_count_pending_inductive(pre: Self, post: Self, bucket: BucketId) {
        let new_ss = SharedState::Pending{bucket};
        let dec_bucket = bucket;
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket === dec_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket).insert(new_ss),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket) + 1); // trigger
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            }
        }

        // boilerplate shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(shared_dec_count_pending2)]
    fn shared_dec_count_pending2_inductive(pre: Self, post: Self, bucket: BucketId) {
        let new_ss = SharedState::Pending2{bucket};
        // proof identical to shared_dec_count_pending_inductive
        let dec_bucket = bucket;
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket === dec_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket).insert(new_ss),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket) + 1); // trigger
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            }
        }

        // boilerplate shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(shared_dec_count_obtained)]
    fn shared_dec_count_obtained_inductive(pre: Self, post: Self, bucket: BucketId, value: StoredType) {
        let new_ss = SharedState::Obtained{bucket, value};
        // proof identical to shared_dec_count_pending_inductive
        let dec_bucket = bucket;
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket === dec_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket).insert(new_ss),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket) + 1); // trigger
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            }
        }

        // boilerplate shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(shared_check_exc)]
    fn shared_check_exc_inductive(pre: Self, post: Self, bucket: BucketId, value: StoredType) {
        let checked_bucket = bucket;
        let old_ss = SharedState::Pending{bucket};
        let new_ss = SharedState::Pending2{bucket};
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket === checked_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket).remove(old_ss).insert(new_ss));
                // TODO(chris): weird that I need this trigger twice, once in each branch.
                // Daaaaaafny wouldn't have made me do that.
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            }
        }

        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            if (ss === new_ss) {
                assert(pre.shared_state.count(old_ss) > 0);    // trigger shared_storage_invariant
                assert(pre.shared_state_valid(old_ss));
            } else {
                assert(pre.shared_state_valid(ss));   // trigger
            }
        }
    }

    #[inductive(shared_check_loading)]
    fn shared_check_loading_inductive(pre: Self, post: Self, bucket: BucketId) {
        // TODO refactor -- a LOT of commonality with shared_check_exc_inductive
        let checked_bucket = bucket;
        let old_ss = SharedState::Pending2{bucket};
        let new_ss = SharedState::Obtained{bucket, value: pre.storage.get_Some_0()};
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            if bucket === checked_bucket {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket).remove(old_ss).insert(new_ss));
                // TODO(chris): weird that I need this trigger twice, once in each branch.
                // Daaaaaafny wouldn't have made me do that.
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            } else {
                assert_multisets_equal!(Self::filter_shared_refs(post.shared_state, bucket),
                    Self::filter_shared_refs(pre.shared_state, bucket));
                assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket)); // trigger
            }
        }

        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            if (ss === new_ss) {
                assert(pre.shared_state.count(old_ss) > 0);    // trigger shared_storage_invariant
                assert(pre.shared_state_valid(old_ss));
            } else {
                assert(pre.shared_state_valid(ss));   // trigger
            }
        }
    }

}

} //tokenized_state_machine

fn main() {}
