#![feature(allocator_api)]
#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::option::*;
use pervasive::modes::*;
use pervasive::map::*;
use pervasive::seq::*;
use pervasive::prelude::*;
use pervasive::ptr::*;

verus_old_todo_no_ghost_blocks!{

// I'd prefer to have some kind of Wide<T> that adds padding to T
// to make it block-sized, and then do OptBox<Wide<T>>.
// This would make the whole thing a bit more modular.
// But since the size of a block is dynamic, it would
// need to be a dynamically-sized type (DST). Unfortunately,
// DSTs are already a little hard to use in Rust, and then on
// top of that, we would need to add support in Verus

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
}

impl LL {
    spec fn len(&self) -> nat
        decreases(self)
    {
        match self.l@ {
            None => 0,
            Some(sub_ll) => sub_ll.len() + 1,
        }
    }

    spec fn block_size(&self) -> nat {
        self.l.block_size
    }

    spec fn wf(&self) -> bool {
        &&& self.block_size() >= size_of::<LL>()
        &&& match self.l@ {
            None => true,
            Some(sub_ll) => sub_ll.wf() && sub_ll.l.block_size == self.l.block_size
        }
    }

    fn insert_block(&mut self, ptr: PPtr<u8>, points_to_raw: PointsToRaw)
        requires old(self).wf(),
            ptr.id() == points_to_raw@.pptr,
            points_to_raw@.size == old(self).block_size(),
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
