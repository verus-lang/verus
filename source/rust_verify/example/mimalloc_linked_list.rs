#![feature(allocator_api)]
#![allow(unused_imports)]

mod pervasive;
use state_machines_macros::*;
use pervasive::prelude::*;
use pervasive::ptr::*;
use pervasive::*;
use pervasive::thread::*;

// OVERALL ARCHITECTURE
//
// The hierarchy of objects in this allocator goes:
//
//    Heap > Page > Block
//
// Each Page is associated to a particular 'block size'. So to allocate memory of size N,
// the allocator first finds a page of the appropriate size, then allocates a block from
// that page.
//
// There is also a structure called a 'Segment'. Pages are allocated from the segments,
// and segments are shared between the pages.
//
// All of these (heap, segment, page, block) are assigned to a particular thread.
// So we might have like:
//
// - Thread T has Heaps H1 and H2
// - Thread T has Segments S1, S2, and S3
// - H1 has pages {P1, P2, P3, P4} allocated out of T's segments
// - H2 has pages {P5, P6, P7, P8, P9} allocated out of T's segments
// - Each page has a bunch of blocks.
//
// Now, even though this is all thread local, the 'free' might be called from any thread -
// therefore, there could be concurrent access to any of these things, though there are
// only a few fields that need to worry about atomic accesses.
//
// SEGMENT LAYOUT
//
// The Segment has: a SegmentHeader, an array of N PageHeaders, and finally an array of
// N "slices". Each slice contains the blocks for the corresponding PageHeader.
// (TODO figure out: Is it possible for a page to comprise more than one slice?
// How does that work?)
//
//  |-----------------|----|----|----|------------|------------|------------|
//
//  | SegmentHeader   |  PageHeaders |                Slices                |
//
// Again, each slice is broken up into individual blocks, some of which will
// be allocated to the user. The un-allocated blocks, that is, the "free" blocks,
// are organized into a few "free lists". Each free list is a (singly) linked list
// owned by the page.
//
// Furthermore, the PageHeaders are organized into a DOUBLY-linked list which is
// owned by a Heap. (Each PageHeader has a `next` and `prev` field.)
// Also, each PageHeader contains a pointer back to the Heap that owns it.
// 
// Therefore, the pointer structure between heaps and pages is very cyclic.
// Furthermore, the exact layout of a segment is very important for a few reasons:
//
//   (1) `free` needs to be able to take a pointer to a block and determine
//        what segment and page it is in (and our proof needs to be able to prove
//        that said page is valid simply from the fact that its block was allocated).
//
//   (2) The segment is broken into chunks of size `COMMIT_SIZE`, the granularity
//       at which memory is 'committed' from the OS.
//
// PROOF NOTES
// 
// Our top-level tokensized system is going to maintain the heaps, segments, and pages,
// keeping track of which thread owns what, all the doubly-linked lists, and so on.
// (The singly-linked lists will primarily be handled in the implementation)

// Logical identifiers for the various objects, which are based on the hierarcy outlined
// above. Note that the implementation just uses pointers.

pub struct HeapId { pub id: int }
pub struct SegmentId { pub id: int }
pub struct PageId { pub segment_id: SegmentId, pub idx: int }
pub struct BlockId { pub page_id: PageId, pub idx: int }

// States

pub enum DelayedState {
    UseDelayedFree,
    Freeing,
    NoDelayedFree,
    NeverDelayedFree
}

pub struct PageThreadListState {
    pub delayed: DelayedState,
    pub len: nat,
}

pub struct PageState {
    // For the doubly-linked list of Pages
    pub prev: Option<PageId>,
    pub next: Option<PageId>,

    // Sum total of free list and local free list (but excluding thread free list)
    pub len: nat,

    pub block_size: nat,
}

pub struct BlockState {
    pub allocated: bool,
    pub block_size: nat,
    pub segment_shared_access: SegmentSharedAccess,
}

pub struct HeapState {
    // For the doubly-linked list of Pages
    pub first: Option<PageId>,
    pub last: Option<PageId>,
}

pub struct ThreadState { } // TODO
pub struct SegmentState { } // TODO

// Shared States

pub struct SegmentSharedAccess { i: int }
pub struct SegmentLocalAccess { i: int }
pub struct HeapSharedAccess { i: int }
pub struct HeapLocalAccess { i: int }

// Actor lets us track what a single thread is doing.
// The idea is that when the thread checks the 'thread id' of a page,
// it needs to then be sure that the page will remain valid for the duration
// of the period the thread is accessing it.
// That means we need to prevent the thread from modifying the page state
// while the 'AccessingMySegment' is in progress.

// TODO I think we need some kind of 'AtomicActor' as well to do the same thing
// for atomic accesses

pub enum Actor {
    Idle,
    AccessingMySegment(SegmentId, SegmentLocalAccess),
    Abandoned,
}

tokenized_state_machine!{ Mim {
    fields {
        // Thread-local state to each entity

        #[sharding(map)] pub heap: Map<HeapId, HeapState>,
        #[sharding(map)] pub tld: Map<ThreadId, ThreadState>,
        #[sharding(map)] pub segment: Map<SegmentId, SegmentState>,
        #[sharding(map)] pub page: Map<PageId, PageState>,

        // Blocks that are allocated (these ghost shards are handed to the user
        // to give them the right to 'deallocate')

        #[sharding(map)] pub block: Map<BlockId, BlockState>,

        // Atomics (accessed concurrently)

        #[sharding(map)] pub segment_owning_thread: Map<SegmentId, ThreadId>,
        #[sharding(map)] pub page_thread_list_state: Map<PageId, PageThreadListState>,
        #[sharding(map)] pub page_owning_heap: Map<PageId, HeapId>,

        // Thread actors

        #[sharding(map)] pub actor: Map<ThreadId, Actor>,

        // Access to stuff

        #[sharding(storage_map)] pub segment_local_access: Map<SegmentId, SegmentLocalAccess>,
        #[sharding(storage_map)] pub segment_shared_access: Map<SegmentId, SegmentSharedAccess>,

        #[sharding(storage_map)] pub heap_local_access: Map<HeapId, HeapLocalAccess>,
        #[sharding(storage_map)] pub heap_shared_access: Map<HeapId, HeapSharedAccess>,

        // Extra state that doesn't form tokens but helps writing invariants

        #[sharding(not_tokenized)] pub thread_segments: Map<ThreadId, Seq<SegmentId>>,
    }

    transition!{
        alloc_block(block_id: BlockId) {
            remove block -= [block_id => let block_state];
            remove page -= [block_id.page_id => let page_state];

            require(!block_state.allocated);
            require(page_state.len >= 1);

            let new_block_state = BlockState {
                allocated: true,
                .. block_state
            };
            let new_page_state = PageState {
                len: (page_state.len - 1) as nat,
                .. page_state
            };

            add block += [block_id => new_block_state];
            add page += [block_id.page_id => new_page_state];
        }
    }

    transition!{
        free_block_local(block_id: BlockId) {
            remove block -= [block_id => let block_state];
            remove page -= [block_id.page_id => let page_state];

            require(block_state.allocated);

            let new_block_state = BlockState {
                allocated: false,
                .. block_state
            };
            let new_page_state = PageState { len: page_state.len + 1, .. page_state };

            add block += [block_id => new_block_state];
            add page += [block_id.page_id => new_page_state];
        }
    }

    transition!{
        free_block_from_other_thread(block_id: BlockId) {
            remove block -= [block_id => let block_state];
            remove page_thread_list_state -= [block_id.page_id => let ptls];

            require(block_state.allocated);
            // TODO need some additional requirement on the 'delay' state

            let new_block_state = BlockState {
                allocated: false,
                .. block_state
            };
            let new_ptls = PageThreadListState { len: ptls.len + 1, .. ptls };

            add block += [block_id => new_block_state];
            add page_thread_list_state += [block_id.page_id => new_ptls];
        }
    }

    //// Actors and accessing stuff

    property!{
        alloc_guards_shared_access(block_id: BlockId) {
            have block >= [ block_id => let block_state ];
            let segment_id = block_id.page_id.segment_id;
            guard segment_shared_access >= [ segment_id => block_state.segment_shared_access ];
        }
    }

    transition!{
        actor_access_segment(segment_id: SegmentId) {
            have segment_owning_thread >= [segment_id => let thread_id];
            remove actor -= [thread_id => let actor];

            require(actor != Actor::Abandoned);

            birds_eye let ssa = pre.segment_local_access.index(segment_id);

            add actor += [thread_id => Actor::AccessingMySegment(segment_id, ssa)];
        }
    }

    property!{
        actor_guards_segment(thread_id: ThreadId) {
            have actor >= [thread_id => let Actor::AccessingMySegment(segment_id, ssa)];
            guard segment_local_access >= [segment_id => ssa];
        }
    }
}}

verus_old_todo_no_ghost_blocks!{

// Log of the (pointer-size in bytes)
const INTPTR_SHIFT: u64 = 4;

// Log of the size of a 'slice'
const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

// Size of a slice
const SLICE_SIZE: u64 = (1 << SLICE_SHIFT);

// Log of the size of a 'segment'
const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

// Log of the size of a 'segment'
const SEGMENT_SIZE: u64 = 9 + SEGMENT_SHIFT;

// Size of a 'segment'
const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

/*
struct SegmentHeader {
    // Thread owner
    thread_id: ThreadId,

    slice_entries: usize, // Number of slices
}

#[repr(C)]
struct Page {
    slice_count: u32,
    slice_offset: u32,

    // uint8_t is_reset : 1;      // `true` if the page memory was reset
    // uint8_t is_committed : 1;  // `true` if the page virtual memory is committed
    // uint8_t is_zero_init : 1;  // `true` if the page was zero initialized

    capacity: u16, // TODO what do these do?
    reserved: u16,

    flags: u8, // bit 0: in_full
               // bit 1: has_aligned // TODO what do these do?

    // TODO what do these do?
    //uint8_t  is_zero : 1;       // `true` if the blocks in the free list are zero initialized
    //uint8_t  retire_expire : 7; // expiration count for retired blocks

    free: LL,
    used: u32,
    xblock_size: u32,
    local_free: LL,

    xthread_free: ThreadLL,
    xheap: usize, // TODO what's this for, why is it atomic?

    next: *mut Page,
    prev: *mut Page,
}
*/


// I'd prefer to have some kind of Wide<T> that adds padding to T
// to make it block-sized, and then define something like:
//
//    struct LL { ll: OptBox<Wide<LL>> }
//
// This would make the whole thing a bit more modular.
// But since the size of a block is dynamic, it would
// need to be a dynamically-sized type (DST). Unfortunately,
// DSTs are already a little hard to use in Rust, and then on
// top of that, we would need to add support in Verus for DSTs.
//
// So what we do instead is just include the padding in the OptBox type.
// We have a block sized allocation at ptr, with
// the first `size_of::<V>()` bytes allocated for V,
// and then the PointsToRaw gives the uninitialized memory after that making up the rest of
// the block.

struct OptBox<V> {
    p: PPtr<V>,

    #[spec] block_size: nat,
    #[proof] perm: Option<(PointsTo<V>, PointsToRaw)>,
}

impl<V: SizeOf> OptBox<V> {
    spec fn view(&self) -> Option<V> {
        match self.perm {
            Some((p, _)) => p@.value,
            None => None,
        }
    }

    spec fn wf(&self) -> bool {
        match self.perm {
            Some((p, padding)) => {
                &&& p@.pptr == self.p.id()
                &&& p@.value.is_Some()
                &&& self.p.id() != 0
                &&& padding@.pptr == self.p.id() + size_of::<V>()
                &&& self.block_size == size_of::<V>() + padding@.pptr
            }
            None => self.p.id() == 0,
        }
    }
}

// Linked List

struct LL {
    l: OptBox<LL>,
}

impl SizeOf for LL {
    spec fn size_of() -> nat { 8 }
    spec fn align_of() -> nat { 8 }
}

impl LL {
    spec fn len(&self) -> nat
        decreases self,
    {
        match self.l@ {
            None => 0,
            Some(sub_ll) => sub_ll.len() + 1,
        }
    }

    spec fn block_size(&self) -> nat {
        self.l.block_size
    }

    spec fn wf(&self) -> bool
        decreases self,
    {
        &&& self.block_size() >= size_of::<LL>()
        &&& match self.l@ {
            None => true,
            Some(sub_ll) => sub_ll.wf() && sub_ll.l.block_size == self.l.block_size
        }
    }

    spec fn is_valid_page_address(&self, ptr: int) -> bool {
        // TODO this probably needs more conditions
        ptr as int % size_of::<LL>() as int == 0
    }

    fn insert_block(&mut self, ptr: PPtr<u8>, points_to_raw: PointsToRaw)
        requires old(self).wf(),
            ptr.id() == points_to_raw@.pptr,
            points_to_raw@.size == old(self).block_size(),
            old(self).is_valid_page_address(points_to_raw@.pptr),
        ensures
            self.wf(),
            self.block_size() == old(self).block_size(),
            self.len() == old(self).len() + 1,
    {
        #[proof] let mem1;
        #[proof] let mem2;
        proof {
            #[proof] let (m1, m2) = points_to_raw.split(size_of::<LL>() as int);
            mem1 = m1.into_typed::<LL>();
            mem2 = m2;
        }

        let ptr = PPtr::<LL>::from_usize(ptr.to_usize());

        // Swap this into 'self', then set 'perm' down below
        let mut tmp_ll = LL {
            l: OptBox::<LL> {
                p: ptr.clone(),
                block_size: self.block_size(),
                perm: None,
            },
        };
        swap(&mut tmp_ll, self);
        let sub_ll = tmp_ll;

        let mut mem1 = tracked(mem1);
        ptr.put(&mut mem1, sub_ll);

        proof {
            self.l.perm = Some((mem1.get(), mem2));
        }
    }
}

fn main() { }

}
