use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::string::*;
use vstd::*;

// "XOR Linked List". This is a sorta-cute (if not usually practical) folk data structure:
// A doubly-linked list which saves memory by having each node store the XOR of the two
// pointers to its two neighbors.
//
// This example uses the XOR Linked List to build a deque.
//
// TODO should really use usize, but bit-vector operations on usize aren't supported right now,
// so we use u64 and assume it's equivalent to usize.

verus! {

#[verifier::external_body]
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
type MemPerms<V> = PointsTo<Node<V>>;

// The xor-doubly-linked list requires us to treat pointers as integer addresses.
// This is somewhat tricky because it forces us to think a bit about pointer provenance.
// The simple_pptr library abstracts this away (and verifies it) and thus lets us treat pointers
// as isomoprhic to usize values.

struct DListXor<V> {
    ptrs: Ghost<Seq<PPtr<Node<V>>>>,
    perms: Tracked<Map<nat, MemPerms<V>>>,
    head: u64,
    tail: u64,
}

impl<V> DListXor<V> {
    spec fn wf_perms(&self) -> bool {
        forall|i: nat| 0 <= i < self.ptrs@.len() ==> self.wf_perm(i)
    }

    spec fn prev_of(&self, i: nat) -> u64
        recommends
            i < self.ptrs@.len(),
    {
        if i == 0 {
            0
        } else {
            self.ptrs@[i - 1].addr() as u64
        }
    }

    spec fn next_of(&self, i: nat) -> u64
        recommends
            i < self.ptrs@.len(),
    {
        if i + 1 == self.ptrs@.len() {
            0
        } else {
            self.ptrs@[i + 1int].addr() as u64
        }
    }

    spec fn wf_perm(&self, i: nat) -> bool
        recommends
            i < self.ptrs@.len(),
    {
        &&& self.perms@.dom().contains(i)
        &&& self.perms@[i].pptr() == self.ptrs@[i as int]
        &&& self.perms@[i].pptr() == self.ptrs@[i as int]
        &&& 0 < self.ptrs@[i as int].addr()
        &&& self.ptrs@[i as int].addr() < 0x10000000000000000
        &&& self.perms@[i].is_init()
        &&& self.perms@[i].value().xored == (self.prev_of(i) ^ self.next_of(i))
    }

    spec fn wf_head(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.head == 0
        } else {
            self.head == self.ptrs@[0].addr()
        }
    }

    spec fn wf_tail(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.tail == 0
        } else {
            self.tail == self.ptrs@[self.ptrs@.len() - 1].addr()
        }
    }

    spec fn wf(&self) -> bool {
        self.wf_perms() && self.wf_head() && self.wf_tail()
    }

    spec fn view(&self) -> Seq<V>
        recommends
            self.wf(),
    {
        Seq::<V>::new(self.ptrs@.len(), |i: int| { self.perms@[i as nat].value().v })
    }

    fn new() -> (s: Self)
        ensures
            s.wf(),
            s@.len() == 0,
    {
        DListXor {
            ptrs: Ghost(Seq::empty()),
            perms: Tracked(Map::tracked_empty()),
            head: 0,
            tail: 0,
        }
    }

    fn push_empty_case(&mut self, v: V)
        requires
            old(self).wf(),
            old(self).ptrs@.len() == 0,
        ensures
            self.wf(),
            self@ == old(self)@.push(v),
    {
        let (ptr, Tracked(perm)) = PPtr::new(Node::<V> { xored: 0, v });
        proof {
            self.ptrs@ = self.ptrs@.push(ptr);
            (&perm).is_nonnull();
            self.perms.borrow_mut().tracked_insert((self.ptrs@.len() - 1) as nat, perm);
        }
        self.tail = ptr.addr() as u64;
        self.head = self.tail;
        assert(0u64 ^ 0u64 == 0u64) by (bit_vector);
        assert(self@ =~= old(self)@.push(v));
    }

    fn push_back(&mut self, v: V)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == old(self)@.push(v),
    {
        if self.tail == 0 {
            // Special case: list is empty
            proof {
                assert_by_contradiction!(self.ptrs@.len() == 0, {
                    assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                });
            }
            self.push_empty_case(v);
        } else {
            assert(self.ptrs@.len() > 0);
            assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
            let tail_ptr_u64 = self.tail;
            proof {
                lemma_usize_u64(tail_ptr_u64);
            }
            let tail_ptr = PPtr::<Node<V>>::from_usize(tail_ptr_u64 as usize);
            let tracked mut tail_perm: MemPerms<V> = self.perms.borrow_mut().tracked_remove(
                (self.ptrs@.len() - 1) as nat,
            );
            let mut tail_node = tail_ptr.take(Tracked(&mut tail_perm));
            let second_to_last_ptr = tail_node.xored;
            let (ptr, Tracked(perm)) = PPtr::new(
                Node::<V> { xored: tail_ptr_u64, v },
            );
            proof {
                perm.is_nonnull();
            }
            let new_ptr_u64 = ptr.addr() as u64;
            tail_node.xored = second_to_last_ptr ^ new_ptr_u64;
            tail_ptr.put(Tracked(&mut tail_perm), tail_node);
            proof {
                self.perms.borrow_mut().tracked_insert(
                    (self.ptrs@.len() - 1) as nat,
                    tail_perm,
                );
                self.perms.borrow_mut().tracked_insert(self.ptrs@.len(), perm);
                self.ptrs@ = self.ptrs@.push(ptr);
            }
            self.tail = new_ptr_u64;
            proof {
                assert(tail_ptr_u64 ^ 0 == tail_ptr_u64) by (bit_vector);
                let i = (self.ptrs@.len() - 2) as nat;
                //assert(self.perms@.dom().contains(i));
                //assert(self.perms@[i]@.pptr == self.ptrs@[i]@);
                //assert(self.perms@[i].value.is_Some());
                let prev_of_i = self.prev_of(i);
                assert(prev_of_i ^ 0 == prev_of_i) by (bit_vector);
                //assert(self.prev_of(i) == second_to_last_ptr);
                //assert(self.next_of(i) == new_ptr_int);
                //assert(self.perms@[i].value.get_Some_0().xored == (
                //    self.prev_of(i) ^ self.next_of(i)
                //));
                assert(self.wf_perm((self.ptrs@.len() - 2) as nat));
                assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                assert(forall|i: nat|
                    i < self.ptrs@.len() ==> old(self).wf_perm(i) ==> self.wf_perm(i));
                assert(self.wf_perms());
                assert(self.wf_tail());
                assert(self@[self.ptrs@.len() - 1] == v);
                assert forall|i: int| 0 <= i < self.ptrs@.len() - 1 implies old(self)@[i]
                    == self@[i] by {
                    assert(old(self).wf_perm(i as nat));  // trigger
                };
                assert(self@ =~= old(self)@.push(v));
            }
        }
    }

    fn pop_back(&mut self) -> (v: V)
        requires
            old(self).wf(),
            old(self)@.len() > 0,
        ensures
            self.wf(),
            self@ == old(self)@.drop_last(),
            v == old(self)@[old(self)@.len() - 1],
    {
        assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
        let last_u64 = self.tail;
        proof {
            lemma_usize_u64(last_u64);
        }
        let last_ptr = PPtr::<Node<V>>::from_usize(last_u64 as usize);
        let tracked last_perm: MemPerms<V> = self.perms.borrow_mut().tracked_remove(
            (self.ptrs@.len() - 1) as nat,
        );
        let last_node = last_ptr.into_inner(Tracked(last_perm));
        let penult_u64 = last_node.xored;
        let v = last_node.v;
        proof {
            let self_head = self.head;
            assert(self_head ^ 0 == self_head) by (bit_vector);
            assert(0u64 ^ 0 == 0) by (bit_vector);
        }
        if penult_u64 == 0 {
            self.tail = 0;
            self.head = 0;
            proof {
                assert_by_contradiction!(self.ptrs@.len() == 1, {
                    assert(old(self).wf_perm((self.ptrs@.len() - 2) as nat));
                    #[verifier::spec] let actual_penult_u64 = self.prev_of((self.ptrs@.len() - 1) as nat);
                    assert(actual_penult_u64 ^ 0 == actual_penult_u64) by(bit_vector);
                });
            }
        } else {
            self.tail = penult_u64;
            assert(old(self)@.len() != 1);
            assert(old(self)@.len() >= 2);
            assert(old(self).wf_perm((self.ptrs@.len() - 2) as nat));
            proof {
                let actual_penult_u64 = self.prev_of((self.ptrs@.len() - 1) as nat);
                assert(actual_penult_u64 ^ 0 == actual_penult_u64) by (bit_vector);
                lemma_usize_u64(penult_u64);
            }
            let penult_ptr = PPtr::<Node<V>>::from_usize(penult_u64 as usize);
            let tracked mut penult_perm = self.perms.borrow_mut().tracked_remove(
                (self.ptrs@.len() - 2) as nat,
            );
            let mut penult_node = penult_ptr.take(Tracked(&mut penult_perm));
            let t: Ghost<u64> = Ghost(self.prev_of((self.ptrs@.len() - 2) as nat));
            assert((t@ ^ last_u64) ^ last_u64 == t@ ^ 0) by (bit_vector);
            penult_node.xored = penult_node.xored ^ last_u64;
            assert(penult_node.xored == t@ ^ 0);
            penult_ptr.put(Tracked(&mut penult_perm), penult_node);
            proof {
                self.perms.borrow_mut().tracked_insert(
                    (self.ptrs@.len() - 2) as nat,
                    penult_perm,
                );
            }
        }
        proof {
            self.ptrs@ = self.ptrs@.drop_last();
        }
        proof {
            assert(self.wf_head());
            assert(self.wf_tail());
            if self.ptrs@.len() > 0 {
                /*#[verifier::spec] let i = self.ptrs@.len() - 1;
                assert(self.ptrs@.len() == old(self).ptrs@.len() - 1);
                assert(self.perms@.dom().contains(i));
                assert(self.perms@[i]@.pptr == self.ptrs@[i]@);
                assert(0 < self.ptrs@[i]@);
                assert(self.ptrs@[i]@ < 0x10000000000000000);
                assert(self.perms@[i].value.is_Some());
                assert(self.perms@[i].value.get_Some_0().xored == (
                    self.prev_of(i) ^ self.next_of(i)
                ));*/
                assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
            }
            assert(forall|i: nat| i < self@.len() ==> old(self).wf_perm(i) ==> self.wf_perm(i));
            assert(self.wf_perms());
            assert forall|i: int| 0 <= i < self@.len() implies #[trigger] self@[i] == old(
                self,
            )@.drop_last()[i] by {
                assert(old(self).wf_perm(i as nat));  // trigger
            }
            assert(self@ =~= old(self)@.drop_last());
        }
        v
    }

    fn pop_front(&mut self) -> (v: V)
        requires
            old(self).wf(),
            old(self)@.len() > 0,
        ensures
            self.wf(),
            self@ == old(self)@.subrange(1, old(self)@.len() as int),
            v == old(self)@[0],
    {
        assert(self.wf_perm(0));
        let first_u64 = self.head;
        proof {
            lemma_usize_u64(first_u64);
        }
        let first_ptr = PPtr::<Node<V>>::from_usize(first_u64 as usize);
        let tracked first_perm: MemPerms<V> = self.perms.borrow_mut().tracked_remove(0);
        let first_node = first_ptr.into_inner(Tracked(first_perm));
        let second_u64 = first_node.xored;
        let v = first_node.v;
        proof {
            let self_tail = self.tail;
            assert(self_tail ^ 0 == self_tail) by (bit_vector);
            assert(0u64 ^ 0 == 0) by (bit_vector);
        }
        if second_u64 == 0 {
            self.tail = 0;
            self.head = 0;
            proof {
                assert_by_contradiction!(self.ptrs@.len() == 1, {
                    assert(old(self).wf_perm(1));
                    #[verifier::spec] let actual_second_u64 = self.next_of(0);
                    assert(0 ^ actual_second_u64 == actual_second_u64) by(bit_vector);
                });
            }
        } else {
            self.head = second_u64;
            assert(old(self)@.len() != 1);
            assert(old(self)@.len() >= 2);
            assert(old(self).wf_perm(1));
            proof {
                let actual_second_u64 = self.next_of(0);
                assert(0 ^ actual_second_u64 == actual_second_u64) by (bit_vector);
                lemma_usize_u64(second_u64);
            }
            let second_ptr = PPtr::<Node<V>>::from_usize(second_u64 as usize);
            let tracked mut second_perm = (self.perms.borrow_mut()).tracked_remove(1);
            let mut second_node = second_ptr.take(Tracked(&mut second_perm));
            let t: Ghost<u64> = Ghost(self.next_of(1));
            assert((first_u64 ^ t@) ^ first_u64 == 0 ^ t@) by (bit_vector);
            second_node.xored = second_node.xored ^ first_u64;
            assert(second_node.xored == 0 ^ t@);
            second_ptr.put(Tracked(&mut second_perm), second_node);
            proof {
                self.perms.borrow_mut().tracked_insert(1, second_perm);
                assert forall|j: nat| 1 <= j < old(self)@.len() implies self.perms@.dom().contains(
                    j,
                ) by {
                    assert(old(self).wf_perm(j));
                }
                (self.perms.borrow_mut()).tracked_map_keys_in_place(
                    Map::<nat, nat>::new(
                        |j: nat| 0 <= j < old(self)@.len() - 1,
                        |j: nat| (j + 1) as nat,
                    ),
                );
            }
        }
        proof {
            self.ptrs@ = self.ptrs@.subrange(1, self.ptrs@.len() as int);
        }
        proof {
            assert(self.wf_tail());
            assert(self.wf_head());
            if self.ptrs@.len() > 0 {
                assert(self.wf_perm(0));
            }
            assert(forall|i: nat| i < self@.len() ==> old(self).wf_perm(i + 1) ==> self.wf_perm(i));
            assert(self.wf_perms());
            assert forall|i: int| 0 <= i < self@.len() implies #[trigger] self@[i] == old(
                self,
            )@.subrange(1, old(self)@.len() as int)[i] by {
                assert(old(self).wf_perm(i as nat + 1));  // trigger
            }
            assert(self@ =~= old(self)@.subrange(1, old(self)@.len() as int));
        }
        v
    }

    fn push_front(&mut self, v: V)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == seq![v].add(old(self)@),
    {
        if self.tail == 0 {
            // Special case: list is empty
            proof {
                assert_by_contradiction!(self.ptrs@.len() == 0, {
                    assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                });
            }
            self.push_empty_case(v);
            assert(self@ =~= seq![v].add(old(self)@));
        } else {
            assert(self.ptrs@.len() > 0);
            assert(self.wf_perm(0));
            let head_ptr_u64 = self.head;
            proof {
                lemma_usize_u64(head_ptr_u64);
            }
            let head_ptr = PPtr::<Node<V>>::from_usize(head_ptr_u64 as usize);
            let tracked mut head_perm: MemPerms<V> = (self.perms.borrow_mut()).tracked_remove(
                0,
            );
            let mut head_node = head_ptr.take(Tracked(&mut head_perm));
            let second_ptr = head_node.xored;
            let (ptr, Tracked(perm)) = PPtr::new(
                Node::<V> { xored: head_ptr_u64, v },
            );
            proof {
                perm.is_nonnull();
            }
            let new_ptr_u64 = ptr.addr() as u64;
            head_node.xored = new_ptr_u64 ^ second_ptr;
            head_ptr.put(Tracked(&mut head_perm), head_node);
            proof {
                self.perms.borrow_mut().tracked_insert(0, head_perm);
                assert forall|j: nat| 0 <= j < old(self)@.len() implies self.perms@.dom().contains(
                    j,
                ) by {
                    assert(old(self).wf_perm(j));
                }
                self.perms.borrow_mut().tracked_map_keys_in_place(
                    Map::<nat, nat>::new(
                        |j: nat| 1 <= j <= old(self)@.len(),
                        |j: nat| (j - 1) as nat,
                    ),
                );
                self.perms.borrow_mut().tracked_insert(0, perm);
                self.ptrs@ = seq![ptr].add(self.ptrs@);
            }
            self.head = new_ptr_u64;
            proof {
                assert(0 ^ head_ptr_u64 == head_ptr_u64) by (bit_vector);
                let i = 1;
                //assert(self.perms@.dom().contains(i));
                //assert(self.perms@[i]@.pptr == self.ptrs@[i]@);
                //assert(self.perms@[i].value.is_Some());
                let next_of_i = self.next_of(i);
                assert(0 ^ next_of_i == next_of_i) by (bit_vector);
                //assert(self.prev_of(i) == second_to_last_ptr);
                //assert(self.next_of(i) == new_ptr_int);
                //assert(self.perms@[i].value.get_Some_0().xored == (
                //    self.prev_of(i) ^ self.next_of(i)
                //));
                assert(self.perms@.index(1).value().xored == new_ptr_u64
                    ^ second_ptr);
                assert(self.perms@.index(0).value().xored == head_ptr_u64);
                assert(self.perms@.index(1).pptr().addr() == head_ptr_u64);
                assert(self.wf_perm(1));
                assert(self.wf_perm(0));
                assert(forall|i: nat|
                    1 <= i <= old(self).ptrs@.len() ==> old(self).wf_perm((i - 1) as nat)
                        ==> #[trigger] self.wf_perm(i));
                assert(self.wf_perms());
                assert(self.wf_tail());
                assert(self@[0] == v);
                assert forall|i: int| 1 <= i <= self.ptrs@.len() - 1 implies old(self)@[i - 1]
                    == self@[i] by {
                    assert(old(self).wf_perm((i - 1) as nat));  // trigger
                };
                assert(self@ =~= seq![v].add(old(self)@));
            }
        }
    }
}

#[verifier::external_body]
fn print_result(msg: StrSlice<'static>, value: u32) {
    println!("{}: {value}", msg);
}

fn main() {
    let mut t = DListXor::<u32>::new();
    t.push_back(2);
    t.push_back(3);
    t.push_front(1);  // 1, 2, 3
    print_result(new_strlit("pushed"), 2);
    print_result(new_strlit("pushed"), 3);
    print_result(new_strlit("pushed"), 1);
    let x = t.pop_back();  // 3
    let y = t.pop_front();  // 1
    let z = t.pop_front();  // 2
    assert(x == 3);
    assert(y == 1);
    assert(z == 2);
    print_result(new_strlit("popped"), x);
    print_result(new_strlit("popped"), y);
    print_result(new_strlit("popped"), z);
}

} // verus!
