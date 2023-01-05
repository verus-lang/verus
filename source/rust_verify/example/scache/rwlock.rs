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
pub spec const RC_WIDTH: BucketId = 4;  // How many refcounting buckets we use.

#[is_variant]
pub enum SharedState {
   Pending{bucket: BucketId},   // inc refcount
                                         // None means the shared lock is being acquired for
                                         // writeback.

   Pending2{bucket: BucketId},  // !free & !writelocked

   Obtained{bucket: BucketId, value: StoredType}, // !reading
}

impl SharedState {
    pub open spec fn get_bucket(self) -> BucketId {
        match self {
            SharedState::Pending{bucket} => bucket,
            SharedState::Pending2{bucket} => bucket,
            SharedState::Obtained{bucket, value: _} => bucket,
        }
    }
}

#[is_variant]
pub enum ExcState {
    Claim{bucket: Option<BucketId>, value: StoredType},
    PendingAwaitWriteback{bucket: Option<BucketId>, value: StoredType},
    Pending{bucket: Option<BucketId>, visited_count: BucketId, clean: bool, value: StoredType},
    Obtained{bucket: Option<BucketId>, clean: bool},
}

impl ExcState {
    // TODO: Ugh I hate this boilerplate stuff that would be free in Dafny.
    // verus! or is_variant should throw us a bone here.
    pub open spec fn get_bucket(self) -> Option<BucketId> {
        match self {
            ExcState::Claim{bucket, value: _} => bucket,
            ExcState::PendingAwaitWriteback{bucket, value: _} => bucket,
            ExcState::Pending{bucket, visited_count: _, clean: _, value: _} => bucket,
            ExcState::Obtained{bucket, clean: _} => bucket
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
    PendingCounted{bucket: Option<BucketId>},  // inc refcount
    Obtained{bucket: Option<BucketId>},         // clear ExcLock bit
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

    pub open spec fn count_shared_refs(shared: Multiset<SharedState>, bucket: BucketId) -> nat {
        shared.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket).len()
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
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }
   
    #[inductive(take_exc_lock_finish_writeback)]
    fn take_exc_lock_finish_writeback_inductive(pre: Self, post: Self, clean: bool) {
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(take_exc_lock_check_ref_count)]
    fn take_exc_lock_check_ref_count_inductive(pre: Self, post: Self) {
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
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
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
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
            let pre_counted_refs = pre.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket);
            let post_counted_refs = post.shared_state.filter(|shared_state: SharedState| shared_state.get_bucket() === bucket);
                
            if Some(bucket) === pre_exc.get_Obtained_bucket() {
                let new_ss = SharedState::Obtained{bucket: pre_exc.get_bucket().get_Some_0(), value};
                assert_multisets_equal!(post_counted_refs, pre_counted_refs.insert(new_ss));
            } else {
                assert_multisets_equal!(post_counted_refs, pre_counted_refs);
            }
            // TODO shouldn't need next line to trigger the assert by conclusion:
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
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    #[inductive(withdraw_alloc)]
    fn withdraw_alloc_inductive(pre: Self, post: Self) {
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
        // shared_storage_invariant
        assert forall |ss| post.shared_state.count(ss) > 0 implies post.shared_state_valid(ss) by {
            assert(pre.shared_state_valid(ss));
        }
    }

    // TODO(jonh): getting pretty sad that we have to copy/paste the same proof fifty times
    #[inductive(withdraw_alloc_no_refcount)]
    fn withdraw_alloc_no_refcount_inductive(pre: Self, post: Self) {
        // ref_count_invariant
        assert forall |bucket: BucketId| bucket < RC_WIDTH
            implies post.ref_counts[bucket] === post.count_all_refs(bucket) by {
            assert(pre.count_all_refs(bucket) === post.count_all_refs(bucket));
        }
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
}

} //tokenized_state_machine

fn main() { }
