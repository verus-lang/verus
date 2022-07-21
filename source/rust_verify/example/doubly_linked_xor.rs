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

#[verifier(external_body)]
#[proof]
fn lemma_usize_u64(x: u64) {
    ensures(x as usize as u64 == x);
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
    #[spec] ptrs: Seq<PPtr<Node<V>>>,
    #[proof] perms: Map<nat, Permission<Node<V>>>,

    head: u64,
    tail: u64,
}

impl<V> DListXor<V> {
    #[spec]
    fn wf_perms(&self) -> bool {
        forall(|i: nat| (0 <= i && i < self.ptrs.len()) >>= self.wf_perm(i))
    }

    #[spec]
    fn prev_of(&self, i: nat) -> u64 {
        recommends(i < self.ptrs.len());

        if i == 0 {
            0
        } else {
            self.ptrs.index(i as int - 1).id() as u64
        }
    }

    #[spec]
    fn next_of(&self, i: nat) -> u64 {
        recommends(i < self.ptrs.len());

        if i + 1 == self.ptrs.len() {
            0
        } else {
            self.ptrs.index(i as int + 1).id() as u64
        }
    }


    #[spec]
    fn wf_perm(&self, i: nat) -> bool {
        recommends(i < self.ptrs.len());

        self.perms.dom().contains(i)
        &&
        equal(self.perms.index(i).pptr, self.ptrs.index(i).id())
        &&
        0 < self.ptrs.index(i).id()
        &&
        self.ptrs.index(i).id() < 0x10000000000000000
        &&
        self.perms.index(i).value.is_Some()
        &&
        self.perms.index(i).value.get_Some_0().xored == (
            self.prev_of(i) ^ self.next_of(i)
        )
    }

    #[spec]
    fn wf_head(&self) -> bool {
        if self.ptrs.len() == 0 {
            self.head == 0
        } else {
            self.head as int == self.ptrs.index(0).id()
        }
    }

    #[spec]
    fn wf_tail(&self) -> bool {
        if self.ptrs.len() == 0 {
            self.tail == 0
        } else {
            self.tail as int == self.ptrs.index(self.ptrs.len() as int - 1).id()
        }
    }


    #[spec]
    fn wf(&self) -> bool {
        self.wf_perms() && self.wf_head() && self.wf_tail()
    }

    #[spec]
    fn view(&self) -> Seq<V> {
        recommends(self.wf());

        Seq::<V>::new(self.ptrs.len(), |i: int| {
            self.perms.index(i as nat).value.get_Some_0().v
        })
    }

    #[exec]
    fn new() -> Self {
        ensures(|s: Self| [
            s.wf() && s.view().len() == 0
        ]);

        DListXor {
            ptrs: Seq::empty(),
            perms: Map::tracked_empty(),
            head: 0,
            tail: 0,
        }
    }

    #[exec]
    fn push_first(&mut self, v: V) {
        requires([
            old(self).wf(),
            old(self).ptrs.len() == 0,
        ]);
        ensures([
            self.wf(),
            equal(self.view(), old(self).view().push(v)),
        ]);

        let (ptr, perm) = PPtr::new(
            Node::<V> { xored: 0, v }
        );
        #[proof] let perm = perm.get();
        perm.is_nonnull();
        let perm = Tracked::exec(perm);

        self.ptrs = self.ptrs.push(ptr);
        self.perms.tracked_insert(self.ptrs.len() - 1, perm.get());

        self.tail = ptr.to_usize() as u64;
        self.head = self.tail;

        assert_bit_vector(0 as u64 ^ 0 as u64 == 0 as u64);
        assert(self.view().ext_equal(old(self).view().push(v)));
    }

    #[exec]
    fn push_back(&mut self, v: V) {
        requires(old(self).wf());
        ensures([
            self.wf(),
            equal(self.view(), old(self).view().push(v)),
        ]);

        if self.tail == 0 {
            // Special case: list is empty

            assert_by_contradiction!(self.ptrs.len() == 0, {
                assert(self.wf_perm(self.ptrs.len() - 1));
            });

            self.push_first(v);
        } else {
            assert(self.ptrs.len() > 0);
            assert(self.wf_perm(self.ptrs.len() - 1));

            let tail_ptr_u64 = self.tail;
            lemma_usize_u64(tail_ptr_u64);
            let tail_ptr = PPtr::<Node<V>>::from_usize(tail_ptr_u64 as usize);
            #[proof] let tail_perm = self.perms.tracked_remove(self.ptrs.len() - 1);
            let mut tail_perm = Tracked::exec(tail_perm);
            let mut tail_node = tail_ptr.take(&mut tail_perm);
            let second_to_last_ptr = tail_node.xored;

            let (ptr, perm) = PPtr::new(
                Node::<V> { xored: tail_ptr_u64, v }
            );

            #[proof] let perm = perm.get();
            perm.is_nonnull();
            let perm = Tracked::exec(perm);

            let new_ptr_u64 = ptr.to_usize() as u64;

            tail_node.xored = second_to_last_ptr ^ new_ptr_u64;
            tail_ptr.put(&mut tail_perm, tail_node);
            self.perms.tracked_insert(self.ptrs.len() - 1, tail_perm.get());
            self.perms.tracked_insert(self.ptrs.len(), perm.get());
            self.ptrs = self.ptrs.push(ptr);
            self.tail = new_ptr_u64;

            assert_bit_vector(tail_ptr_u64 ^ 0 == tail_ptr_u64);

            #[spec] let i = self.ptrs.len() - 2;
            //assert(self.perms.dom().contains(i));
            //assert(equal(self.perms.index(i).pptr, self.ptrs.index(i).view()));
            //assert(self.perms.index(i).value.is_Some());
            #[spec] let prev_of_i = self.prev_of(i);
            assert_bit_vector(prev_of_i ^ 0 == prev_of_i);
            //assert(self.prev_of(i) == second_to_last_ptr);
            //assert(self.next_of(i) == new_ptr_int);
            //assert(self.perms.index(i).value.get_Some_0().xored == (
            //    self.prev_of(i) ^ self.next_of(i)
            //));

            assert(self.wf_perm(self.ptrs.len() - 2));
            assert(self.wf_perm(self.ptrs.len() - 1));
            assert(forall(|i: nat| i < self.ptrs.len() >>=
                old(self).wf_perm(i) >>= self.wf_perm(i)));
            assert(self.wf_perms());
            assert(self.wf_tail());

            assert(equal(self.view().index(self.ptrs.len() as int - 1), v));
            assert_forall_by(|i: nat| {
                requires(i < self.ptrs.len() - 1);
                ensures(equal(
                    old(self).view().index(i),
                    self.view().index(i)
                ));
                assert(old(self).wf_perm(i)); // trigger
            });
            assert(self.view().ext_equal(old(self).view().push(v)));
        }
    }

    #[exec]
    fn pop_back(&mut self) -> V {
        requires([
            old(self).wf(),
            old(self).view().len() > 0,
        ]);
        ensures(|v: V| [
            self.wf(),
            equal(self.view(), old(self).view().drop_last()),
            equal(v, old(self).view().index(old(self).view().len() as int - 1)),
        ]);

        assert(self.wf_perm(self.ptrs.len() - 1));

        let last_u64 = self.tail;
        lemma_usize_u64(last_u64);
        let last_ptr = PPtr::<Node<V>>::from_usize(last_u64 as usize);
        #[proof] let last_perm = self.perms.tracked_remove(self.ptrs.len() - 1);
        let last_node = last_ptr.into_inner(Tracked::exec(last_perm));

        let penult_u64 = last_node.xored;
        let v = last_node.v;

        #[spec] let self_head = self.head;
        assert_bit_vector(self_head ^ 0 == self_head);
        assert_bit_vector(0 as u64 ^ 0 == 0);

        if penult_u64 == 0 {
            self.tail = 0;
            self.head = 0;

            assert_by_contradiction!(self.ptrs.len() == 1, {
                assert(old(self).wf_perm(self.ptrs.len() - 2));
                #[spec] let actual_penult_u64 = self.prev_of(self.ptrs.len() - 1);
                assert_bit_vector(actual_penult_u64 ^ 0 == actual_penult_u64);
            });
        } else {
            self.tail = penult_u64;

            assert(old(self).view().len() != 1);
            assert(old(self).view().len() >= 2);
            assert(old(self).wf_perm(self.ptrs.len() - 2));

            #[spec] let actual_penult_u64 = self.prev_of(self.ptrs.len() - 1);
            assert_bit_vector(actual_penult_u64 ^ 0 == actual_penult_u64);

            lemma_usize_u64(penult_u64);
            let penult_ptr = PPtr::<Node<V>>::from_usize(penult_u64 as usize);
            #[proof] let penult_perm = self.perms.tracked_remove(self.ptrs.len() - 2);
            let mut penult_perm = Tracked::exec(penult_perm);
            let mut penult_node = penult_ptr.take(&mut penult_perm);

            #[spec] let t = self.prev_of(self.ptrs.len() - 2);
            assert_bit_vector((t ^ last_u64) ^ last_u64 == t ^ 0);

            penult_node.xored = penult_node.xored ^ last_u64;

            assert(penult_node.xored == t ^ 0);

            penult_ptr.put(&mut penult_perm, penult_node);
            self.perms.tracked_insert(self.ptrs.len() - 2, penult_perm.get());
        }

        self.ptrs = self.ptrs.drop_last();

        assert(self.wf_head());
        assert(self.wf_tail());

        if self.ptrs.len() > 0 {
            /*#[spec] let i = self.ptrs.len() - 1;
            assert(self.ptrs.len() == old(self).ptrs.len() - 1);
            assert(self.perms.dom().contains(i));
            assert(equal(self.perms.index(i).pptr, self.ptrs.index(i).view()));
            assert(0 < self.ptrs.index(i).view());
            assert(self.ptrs.index(i).view() < 0x10000000000000000);
            assert(self.perms.index(i).value.is_Some());
            assert(self.perms.index(i).value.get_Some_0().xored == (
                self.prev_of(i) ^ self.next_of(i)
            ));*/
            assert(self.wf_perm(self.ptrs.len() - 1));
        }

        assert(forall(|i| 0 <= i && i < self.view().len() >>=
            old(self).wf_perm(i) >>= self.wf_perm(i)));
        assert(self.wf_perms());

        assert_forall_by(|i: int| {
            requires(0 <= i && i < self.view().len());
            ensures(equal(
                self.view().index(i),
                old(self).view().drop_last().index(i),
            ));
            assert(old(self).wf_perm(i as nat)); // trigger
        });

        assert(self.view().ext_equal(old(self).view().drop_last()));

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
