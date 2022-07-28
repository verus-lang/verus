#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{ptr::*};
use crate::pervasive::{seq::*};
use crate::pervasive::{seq_lib::*};
use crate::pervasive::{map::*};
use crate::pervasive::{modes::*};

// "XOR Linked List". This is a sorta-cute (if not usually practical) folk data structure:
// A doubly-linked list which saves memory by having each node store the XOR of the two
// pointers to its two neighbors.
//
// This example uses the XOR Linked List to build a deque.
//
// TODO should really use usize, bit-vector operations aren't supported right now, so we
// use u64 and assume it's equivalent to usize.

verus! {

#[verifier(external_body)]
proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
{
    unimplemented!();
}

// Single node in the list

struct Node<V> {
    xored: u64,
    v: V,
}

// Doubly-linked list
// Contains head pointer, tail pointer
// and in ghost code, tracks all the pointers and all the permissions to access the nodes

struct DListXor<V> {
    ptrs: Ghost<Seq<PPtr<Node<V>>>>,
    perms: Tracked<Map<nat, Permission<Node<V>>>>,

    head: u64,
    tail: u64,
}

impl<V> DListXor<V> {
    spec fn wf_perms(&self) -> bool {
        forall|i: nat| 0 <= i < self.ptrs@.len() ==> self.wf_perm(i)
    }

    spec fn prev_of(&self, i: nat) -> u64
        recommends i < self.ptrs@.len()
    {
        if i == 0 {
            0
        } else {
            self.ptrs@[i - 1].id() as u64
        }
    }

    spec fn next_of(&self, i: nat) -> u64
        recommends i < self.ptrs@.len()
    {
        if i + 1 == self.ptrs@.len() {
            0
        } else {
            self.ptrs@[i + 1int].id() as u64
        }
    }

    spec fn wf_perm(&self, i: nat) -> bool
        recommends i < self.ptrs@.len()
    {
        &&& self.perms@.dom().contains(i)
        &&& self.perms@[i].pptr === self.ptrs@[i as int].id()
        &&& 0 < self.ptrs@[i as int].id()
        &&& self.ptrs@[i as int].id() < 0x10000000000000000
        &&& self.perms@[i].value.is_Some()
        &&& self.perms@[i].value.get_Some_0().xored == (
            self.prev_of(i) ^ self.next_of(i)
        )
    }

    spec fn wf_head(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.head == 0
        } else {
            self.head == self.ptrs@[0].id()
        }
    }

    spec fn wf_tail(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.tail == 0
        } else {
            self.tail == self.ptrs@[self.ptrs@.len() - 1].id()
        }
    }


    spec fn wf(&self) -> bool {
        self.wf_perms() && self.wf_head() && self.wf_tail()
    }

    spec fn view(&self) -> Seq<V>
        recommends self.wf()
    {

        Seq::<V>::new(self.ptrs@.len(), |i: int| {
            self.perms@[i as nat].value.get_Some_0().v
        })
    }

    fn new() -> (s: Self)
        ensures
            s.wf(),
            s@.len() == 0,
    {
        DListXor {
            ptrs: ghost(Seq::empty()),
            perms: tracked(Map::tracked_empty()),
            head: 0,
            tail: 0,
        }
    }

    fn push_first(&mut self, v: V)
        requires
            old(self).wf(),
            old(self).ptrs@.len() == 0,
        ensures
            self.wf(),
            self@ === old(self)@.push(v),
    {
        let (ptr, perm) = PPtr::new(
            Node::<V> { xored: 0, v }
        );
        proof {
            self.ptrs@ = self.ptrs@.push(ptr);
            let tracked perm = (tracked perm).get();
            (tracked &perm).is_nonnull();
            (tracked self.perms.borrow_mut())
                .tracked_insert((self.ptrs@.len() - 1) as nat, tracked perm);
        }

        self.tail = ptr.to_usize() as u64;
        self.head = self.tail;

        assert(0u64 ^ 0u64 == 0u64) by(bit_vector);
        assert(self@.ext_equal(old(self)@.push(v)));
    }

    fn push_back(&mut self, v: V)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ === old(self)@.push(v),
    {
        if self.tail == 0 {
            // Special case: list is empty

            proof {
                assert_by_contradiction!(self.ptrs@.len() == 0, {
                    assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                });
            }

            self.push_first(v);
        } else {
            assert(self.ptrs@.len() > 0);
            assert(self.wf_perm((self.ptrs@.len() - 1) as nat));

            let tail_ptr_u64 = self.tail;
            proof { lemma_usize_u64(tail_ptr_u64); }
            let tail_ptr = PPtr::<Node<V>>::from_usize(tail_ptr_u64 as usize);
            let mut tail_perm: Tracked<Permission<Node<V>>> = tracked(
                (tracked self.perms.borrow_mut()).tracked_remove((self.ptrs@.len() - 1) as nat)
            );
            let mut tail_node = tail_ptr.take(&mut tail_perm);
            let second_to_last_ptr = tail_node.xored;

            let (ptr, perm) = PPtr::new(
                Node::<V> { xored: tail_ptr_u64, v }
            );

            proof {
                (tracked perm.borrow()).is_nonnull();
            }

            let new_ptr_u64 = ptr.to_usize() as u64;

            tail_node.xored = second_to_last_ptr ^ new_ptr_u64;
            tail_ptr.put(&mut tail_perm, tail_node);
            proof {
                (tracked self.perms.borrow_mut())
                    .tracked_insert((self.ptrs@.len() - 1) as nat, (tracked tail_perm).get());
                (tracked self.perms.borrow_mut())
                    .tracked_insert(self.ptrs@.len(), (tracked perm).get());
                self.ptrs@ = self.ptrs@.push(ptr);
            }
            self.tail = new_ptr_u64;

            proof {
                assert(tail_ptr_u64 ^ 0 == tail_ptr_u64) by(bit_vector);

                let i = (self.ptrs@.len() - 2) as nat;
                //assert(self.perms@.dom().contains(i));
                //assert(self.perms@[i].pptr === self.ptrs@[i]@);
                //assert(self.perms@[i].value.is_Some());
                let prev_of_i = self.prev_of(i);
                assert_bit_vector(prev_of_i ^ 0 == prev_of_i);
                //assert(self.prev_of(i) == second_to_last_ptr);
                //assert(self.next_of(i) == new_ptr_int);
                //assert(self.perms@[i].value.get_Some_0().xored == (
                //    self.prev_of(i) ^ self.next_of(i)
                //));

                assert(self.wf_perm((self.ptrs@.len() - 2) as nat));
                assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                assert(forall|i: nat| i < self.ptrs@.len() ==>
                    old(self).wf_perm(i) ==> self.wf_perm(i));
                assert(self.wf_perms());
                assert(self.wf_tail());

                assert(self@[self.ptrs@.len() - 1] === v);
                assert forall|i: int| 0 <= i < self.ptrs@.len() - 1 implies old(self)@[i] === self@[i] by {
                    assert(old(self).wf_perm(i as nat)); // trigger
                };
                assert(self@.ext_equal(old(self)@.push(v)));
            }
        }
    }

    fn pop_back(&mut self) -> (v: V)
        requires
            old(self).wf(),
            old(self)@.len() > 0,
        ensures
            self.wf(),
            self@ === old(self)@.drop_last(),
            v === old(self)@[old(self)@.len() - 1],
    {
        assert(self.wf_perm((self.ptrs@.len() - 1) as nat));

        let last_u64 = self.tail;
        proof { lemma_usize_u64(last_u64); }
        let last_ptr = PPtr::<Node<V>>::from_usize(last_u64 as usize);
        let last_perm: Tracked<Permission<Node<V>>> = tracked(
            (tracked self.perms.borrow_mut()).tracked_remove((self.ptrs@.len() - 1) as nat)
        );
        let last_node = last_ptr.into_inner(last_perm);

        let penult_u64 = last_node.xored;
        let v = last_node.v;

        proof {
            let self_head = self.head;
            assert(self_head ^ 0 == self_head) by(bit_vector);
            assert(0u64 ^ 0 == 0) by(bit_vector);
        }

        if penult_u64 == 0 {
            self.tail = 0;
            self.head = 0;

            proof {
                assert_by_contradiction!(self.ptrs@.len() == 1, {
                    assert(old(self).wf_perm((self.ptrs@.len() - 2) as nat));
                    #[spec] let actual_penult_u64 = self.prev_of((self.ptrs@.len() - 1) as nat);
                    assert_bit_vector(actual_penult_u64 ^ 0 == actual_penult_u64);
                });
            }
        } else {
            self.tail = penult_u64;

            assert(old(self)@.len() != 1);
            assert(old(self)@.len() >= 2);
            assert(old(self).wf_perm((self.ptrs@.len() - 2) as nat));

            proof {
                let actual_penult_u64 = self.prev_of((self.ptrs@.len() - 1) as nat);
                assert(actual_penult_u64 ^ 0 == actual_penult_u64) by(bit_vector);

                lemma_usize_u64(penult_u64);
            }
            let penult_ptr = PPtr::<Node<V>>::from_usize(penult_u64 as usize);
            let mut penult_perm = tracked(
                (tracked self.perms.borrow_mut()).tracked_remove((self.ptrs@.len() - 2) as nat)
            );
            let mut penult_node = penult_ptr.take(&mut penult_perm);
            let t: Ghost<u64> = ghost(self.prev_of((self.ptrs@.len() - 2) as nat));
            assert((t@ ^ last_u64) ^ last_u64 == t@ ^ 0) by(bit_vector);

            penult_node.xored = penult_node.xored ^ last_u64;

            assert(penult_node.xored == t@ ^ 0);

            penult_ptr.put(&mut penult_perm, penult_node);
            proof {
                (tracked self.perms.borrow_mut())
                    .tracked_insert((self.ptrs@.len() - 2) as nat, (tracked penult_perm).get());
            }
        }

        proof {
            self.ptrs@ = self.ptrs@.drop_last();
        }

        proof {
            assert(self.wf_head());
            assert(self.wf_tail());

            if self.ptrs@.len() > 0 {
                /*#[spec] let i = self.ptrs@.len() - 1;
                assert(self.ptrs@.len() == old(self).ptrs@.len() - 1);
                assert(self.perms@.dom().contains(i));
                assert(self.perms@[i].pptr === self.ptrs@[i]@);
                assert(0 < self.ptrs@[i]@);
                assert(self.ptrs@[i]@ < 0x10000000000000000);
                assert(self.perms@[i].value.is_Some());
                assert(self.perms@[i].value.get_Some_0().xored == (
                    self.prev_of(i) ^ self.next_of(i)
                ));*/
                assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
            }

            assert(forall|i: nat| i < self@.len() ==>
                old(self).wf_perm(i) ==> self.wf_perm(i));
            assert(self.wf_perms());

            assert forall|i: int|
                0 <= i < self@.len() implies
                #[trigger] self@[i] === old(self)@.drop_last()[i] by
            {
                assert(old(self).wf_perm(i as nat)); // trigger
            }

            assert(self@.ext_equal(old(self)@.drop_last()));
        }

        v
    }

    // TODO push_front, pop_front
}

fn main() {
    let mut t = DListXor::<u32>::new();
    t.push_back(5);
    t.push_back(7);

    let x = t.pop_back();
    let y = t.pop_back();

    assert(x == 7);
    assert(y == 5);
}

} // verus!
