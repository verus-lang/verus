// rust_verify/tests/example.rs ignore --- intending to deprecate PPtr, should update this to raw_ptr
#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use vstd::layout::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::*;

verus! {

struct Vector<V> {
    pub ptr: PPtr<V>,
    pub len: usize,
    pub capacity: usize,
    pub elems: Tracked<Map<nat, PointsTo<V>>>,
    pub rest: Tracked<PointsToRaw>,
    pub dealloc: Tracked<DeallocRaw>,
}

impl<V> Vector<V> {
    pub closed spec fn well_formed(&self) -> bool {
        &&& self.len <= self.capacity
        &&& (forall|i: nat| 0 <= i < self.len ==> self.elems@.dom().contains(i))
        &&& (forall|i: nat|
            0 <= i < self.len ==> (#[trigger] self.elems@.index(i))@.pptr == self.ptr.id()
                + i as int * size_of::<V>())
        &&& (forall|i: nat|
            0 <= i < self.len ==> (#[trigger] self.elems@.index(i))@.value.is_Some())
        &&& self.rest@.is_range(
            self.ptr.id() + self.len * size_of::<V>(),
            (self.capacity - self.len) * size_of::<V>(),
        )
        &&& self.dealloc@@.pptr == self.ptr.id()
        &&& self.dealloc@@.size == self.capacity * size_of::<V>()
        &&& self.dealloc@@.align == align_of::<V>()
        &&& is_sized::<V>()
    }

    pub closed spec fn view(&self) -> Seq<V> {
        Seq::new(self.len as nat, |i: int| self.elems@.index(i as nat)@.value.get_Some_0())
    }

    pub fn empty() -> (vec: Self)
        requires
            is_sized::<V>(),
        ensures
            vec.well_formed(),
    {
        layout_for_type_is_valid::<V>();
        let (p, Tracked(points_to), Tracked(dealloc)) = PPtr::<V>::alloc(
            0,
            std::mem::align_of::<V>(),
        );
        Vector {
            ptr: p,
            len: 0,
            capacity: 0,
            elems: Tracked(Map::tracked_empty()),
            rest: Tracked(points_to),
            dealloc: Tracked(dealloc),
        }
    }

    pub fn index(&self, i: usize) -> (elem: &V)
        requires
            self.well_formed(),
            0 <= i < self@.len(),
        ensures
            *elem === self@.index(i as int),
    {
        let ptr_usize = self.ptr.to_usize();
        assume((i as int * size_of::<V>()) as usize as int == (i as int * size_of::<V>()));
        assume((ptr_usize as int + i as int * size_of::<V>()) as usize as int == (ptr_usize as int
            + i as int * size_of::<V>()));
        let elem_ptr_usize = ptr_usize + i * std::mem::size_of::<V>();
        let elem_ptr = PPtr::<V>::from_usize(elem_ptr_usize);
        let tracked perm = self.elems.borrow().tracked_borrow(i as nat);
        elem_ptr.borrow(Tracked(perm))
    }

    pub fn resize(&mut self, new_capacity: usize)
        requires
            old(self).well_formed(),
            old(self).len <= new_capacity,
        ensures
            self.well_formed(),
            old(self)@ === self@,
            self.capacity === new_capacity,
    {
        // TODO implement
        assume(false);
    }

    pub fn push(&mut self, v: V)
        requires
            old(self).well_formed(),
        ensures
            self@ === old(self)@.push(v),
    {
        if self.len == self.capacity {
            assume((self.capacity as int * 2) as usize as int == (self.capacity as int * 2));
            let new_cap = if self.capacity == 0 {
                2
            } else {
                self.capacity * 2
            };
            self.resize(new_cap);
            assert((if self.capacity == 0 {
                2
            } else {
                self.capacity * 2
            }) > self.capacity) by (nonlinear_arith);
            assert(new_cap > old(self).capacity);
            assert(self@.len() == old(self)@.len());
            assert(self.len == old(self).len);
            assert(self.len < self.capacity);
        }
        assert(self.len < self.capacity);
        let tracked mut points_to;
        proof {
            let tracked mut rest = PointsToRaw::empty();
            tracked_swap(&mut rest, self.rest.borrow_mut());
            assert(size_of::<V>() as int <= (self.capacity - self.len) * size_of::<V>()) by {
                assert((self.capacity - self.len) >= 1 ==> size_of::<V>() as int <= (self.capacity
                    - self.len) * size_of::<V>()) by (nonlinear_arith);
            }
            assert(rest.is_range(
                self.ptr.id() + self.len * size_of::<V>(),
                (self.capacity - self.len) * size_of::<V>(),
            ));
            assert(rest@.dom() == crate::set_lib::set_int_range(
                self.ptr.id() + self.len * size_of::<V>(),
                self.ptr.id() + self.len * size_of::<V>() + (self.capacity - self.len) * size_of::<
                    V,
                >(),
            ));
            let item_range = crate::set_lib::set_int_range(
                self.ptr.id() + self.len * size_of::<V>(),
                self.ptr.id() + self.len * size_of::<V>() + size_of::<V>() as int,
            );
            assert(item_range.subset_of(rest@.dom()));
            let tracked (points_to_raw, mut rest) = rest.split(item_range);
            assume((self.ptr.id() + self.len * size_of::<V>()) % align_of::<V>() as int == 0);
            points_to = points_to_raw.into_typed::<V>(self.ptr.id() + self.len * size_of::<V>());
            tracked_swap(&mut rest, self.rest.borrow_mut());
        }
        let i = self.len;
        let ptr_usize = self.ptr.to_usize();
        assume((i as int * size_of::<V>()) as usize as int == (i as int * size_of::<V>()));
        assume((ptr_usize as int + i as int * size_of::<V>()) as usize as int == (ptr_usize as int
            + i as int * size_of::<V>()));
        let elem_ptr_usize = ptr_usize + i * std::mem::size_of::<V>();
        let elem_ptr = PPtr::<V>::from_usize(elem_ptr_usize);
        elem_ptr.put(Tracked(&mut points_to), v);
        proof {
            self.elems.borrow_mut().tracked_insert(self.len as nat, points_to);
        }
        self.len = self.len + 1;
        proof {
            assert_seqs_equal!(self@, old(self)@.push(v));
        }
    }
}

fn main() {
}

} // verus!
