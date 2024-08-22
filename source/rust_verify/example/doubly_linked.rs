use vstd::prelude::*;

verus! {

mod doubly_linked_list {
    use vstd::prelude::*;
    use vstd::simple_pptr::*;
    use vstd::raw_ptr::MemContents;
    use vstd::assert_by_contradiction;

    // Single node in the list
    struct Node<V> {
        prev: Option<PPtr<Node<V>>>,
        next: Option<PPtr<Node<V>>>,
        value: V,
    }

    type MemPerms<V> = PointsTo<Node<V>>;

    // Doubly-linked list
    // Contains head pointer, tail pointer
    // and in ghost code, tracks all the pointers and all the permissions to access the nodes
    pub struct DoublyLinkedList<V> {
        ptrs: Ghost<Seq<PPtr<Node<V>>>>,
        perms: Tracked<Map<nat, MemPerms<V>>>,
        head: Option<PPtr<Node<V>>>,
        tail: Option<PPtr<Node<V>>>,
    }

    impl<V> DoublyLinkedList<V> {
        spec fn prev_of(&self, i: nat) -> Option<PPtr<Node<V>>> {
            if i == 0 {
                None
            } else {
                Some(self.ptrs@[i as int - 1])
            }
        }

        spec fn next_of(&self, i: nat) -> Option<PPtr<Node<V>>> {
            if i + 1 == self.ptrs@.len() {
                None
            } else {
                Some(self.ptrs@[i as int + 1])
            }
        }

        spec fn wf_perm(&self, i: nat) -> bool {
            &&& self.perms@.dom().contains(i)
            &&& self.perms@[i].pptr() == self.ptrs@[i as int]
            &&& match self.perms@[i].opt_value() {
                MemContents::Init(node) => node.prev == self.prev_of(i) && node.next == self.next_of(i),
                MemContents::Uninit => false,
            }
        }

        pub closed spec fn well_formed(&self) -> bool {
            &&& forall|i: nat| 0 <= i && i < self.ptrs@.len() ==> self.wf_perm(i)
            &&& if self.ptrs@.len() == 0 {
                self.head == None::<PPtr<Node<V>>> && self.tail == None::<PPtr<Node<V>>>
            } else {
                &&& self.head == Some(self.ptrs@[0])
                &&& self.tail == Some(self.ptrs@[self.ptrs@.len() as int - 1])
            }
        }

        pub closed spec fn view(&self) -> Seq<
            V,
        >
        // recommends self.well_formed(),
         {
            Seq::<V>::new(
                self.ptrs@.len(),
                |i: int| { self.perms@[i as nat].value().value },
            )
        }

        pub fn new() -> (s: Self)
            ensures
                s.well_formed(),
                s@.len() == 0,
        {
            DoublyLinkedList {
                ptrs: Ghost(Seq::empty()),
                perms: Tracked(Map::tracked_empty()),
                head: None,
                tail: None,
            }
        }

        fn push_empty_case(&mut self, v: V)
            requires
                old(self).well_formed(),
                old(self).ptrs@.len() == 0,
            ensures
                self.well_formed(),
                self@ == old(self)@.push(v),
        {
            let (ptr, Tracked(perm)) = PPtr::<Node<V>>::new(
                Node::<V> { prev: None, next: None, value: v },
            );
            proof {
                self.ptrs@ = self.ptrs@.push(ptr);
                self.perms.borrow_mut().tracked_insert(
                    (self.ptrs@.len() - 1) as nat,
                    perm,
                );
            }
            self.tail = Some(ptr.clone());
            self.head = Some(ptr);
            assert(self.view() =~= old(self).view().push(v));
        }

        pub fn push_back(&mut self, v: V)
            requires
                old(self).well_formed(),
            ensures
                self.well_formed(),
                self@ == old(self)@.push(v),
        {
            match &self.tail {
                None => {
                    // Special case: list is empty
                    proof {
                        assert_by_contradiction!(self.ptrs@.len() == 0, {
                        assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                    });
                    }
                    self.push_empty_case(v);
                },
                Some(tail_ptr) => {
                    assert(self.ptrs@.len() > 0);
                    assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                    let tracked mut tail_perm: PointsTo<Node<V>> =
                        self.perms.borrow_mut().tracked_remove((self.ptrs@.len() - 1) as nat);
                    let mut tail_node = tail_ptr.take(Tracked(&mut tail_perm));
                    let second_to_last_ptr = tail_node.prev;
                    let (ptr, Tracked(perm)) = PPtr::<Node<V>>::new(
                        Node::<V> { prev: Some(tail_ptr.clone()), next: None, value: v },
                    );
                    tail_node.prev = second_to_last_ptr;
                    tail_node.next = Some(ptr.clone());
                    tail_ptr.put(Tracked(&mut tail_perm), tail_node);
                    proof {
                        self.perms.borrow_mut().tracked_insert(
                            (self.ptrs@.len() - 1) as nat,
                            tail_perm,
                        );
                        self.perms.borrow_mut().tracked_insert(self.ptrs@.len(), perm);
                        self.ptrs@ = self.ptrs@.push(ptr);
                    }
                    self.tail = Some(ptr);
                    let ghost i = (self.ptrs@.len() - 2) as nat;
                    let ghost prev_of_i = self.prev_of(i);
                    assert(self.wf_perm((self.ptrs@.len() - 2) as nat));
                    assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                    assert(forall|i: nat|
                        i < self.ptrs@.len() && old(self).wf_perm(i) ==> self.wf_perm(i));
                    assert(self.view().index(self.ptrs@.len() as int - 1) == v);
                    assert forall|i: int| 0 <= i && i < self.ptrs@.len() as int - 1 implies old(
                        self,
                    )@[i] == self@[i] by {
                        assert(old(self).wf_perm(i as nat));  // trigger
                    }
                    assert(self@ =~= old(self)@.push(v));
                },
            }
        }

        pub fn pop_back(&mut self) -> (v: V)
            requires
                old(self).well_formed(),
                old(self)@.len() > 0,
            ensures
                self.well_formed(),
                self@ == old(self)@.drop_last(),
                v == old(self)@[old(self)@.len() as int - 1],
        {
            assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
            let last_ptr = self.tail.unwrap().clone();
            let tracked last_perm = self.perms.borrow_mut().tracked_remove(
                (self.ptrs@.len() - 1) as nat,
            );
            let last_node = last_ptr.into_inner(Tracked(last_perm));
            let v = last_node.value;
            match &last_node.prev {
                None => {
                    self.tail = None;
                    self.head = None;
                    proof {
                        assert_by_contradiction!(self.ptrs@.len() == 1, {
                        assert(old(self).wf_perm((self.ptrs@.len() - 2) as nat));
                        let actual_penult_u64 = self.prev_of((self.ptrs@.len() - 1) as nat);
                    });
                    }
                },
                Some(penult_ptr) => {
                    self.tail = Some(penult_ptr.clone());
                    assert(old(self)@.len() != 1);
                    assert(old(self)@.len() >= 2);
                    assert(old(self).wf_perm((self.ptrs@.len() - 2) as nat));
                    let ghost actual_penult_u64 = self.prev_of((self.ptrs@.len() - 1) as nat);
                    let tracked mut penult_perm =
                        self.perms.borrow_mut().tracked_remove((self.ptrs@.len() - 2) as nat);
                    let mut penult_node = penult_ptr.take(Tracked(&mut penult_perm));
                    penult_node.next = None;
                    penult_ptr.put(Tracked(&mut penult_perm), penult_node);
                    proof {
                        self.perms.borrow_mut().tracked_insert(
                            (self.ptrs@.len() - 2) as nat,
                            penult_perm,
                        );
                    }
                },
            }
            proof {
                self.ptrs@ = self.ptrs@.drop_last();
                if self.ptrs@.len() > 0 {
                    assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                }
            }
            assert(forall|i: nat| i < self@.len() && old(self).wf_perm(i) ==> self.wf_perm(i));
            assert forall|i: int| 0 <= i && i < self@.len() implies #[trigger] self@[i] == old(
                self,
            )@.drop_last()[i] by {
                assert(old(self).wf_perm(i as nat));  // trigger
            }
            assert(self@ =~= old(self)@.drop_last());
            v
        }

        pub fn pop_front(&mut self) -> (v: V)
            requires
                old(self).well_formed(),
                old(self).view().len() > 0,
            ensures
                self.well_formed(),
                self@ == old(self)@.subrange(1, old(self)@.len() as int),
                v == old(self)@[0],
        {
            assert(self.wf_perm(0));
            let first_ptr = self.head.unwrap().clone();
            let tracked first_perm = self.perms.borrow_mut().tracked_remove(0);
            let first_node = first_ptr.into_inner(Tracked(first_perm));
            let v = first_node.value;
            match &first_node.next {
                None => {
                    self.tail = None;
                    self.head = None;
                    proof {
                        assert_by_contradiction!(self.ptrs@.len() == 1, {
                        assert(old(self).wf_perm(1));
                        let actual_second_u64 = self.next_of(0);
                    });
                    }
                },
                Some(second_ptr) => {
                    self.head = Some(second_ptr.clone());
                    assert(old(self)@.len() != 1);
                    assert(old(self)@.len() >= 2);
                    assert(old(self).wf_perm(1));
                    let ghost actual_second_u64 = self.next_of(0);
                    let tracked mut second_perm = self.perms.borrow_mut().tracked_remove(1);
                    let mut second_node = second_ptr.take(Tracked(&mut second_perm));
                    second_node.prev = None;
                    second_ptr.put(Tracked(&mut second_perm), second_node);
                    proof {
                        self.perms.borrow_mut().tracked_insert(1, second_perm);
                        assert forall|j: nat|
                            1 <= j && j < old(self)@.len() implies self.perms@.dom().contains(
                            j,
                        ) by {
                            assert(old(self).wf_perm(j));
                        };
                        self.perms.borrow_mut().tracked_map_keys_in_place(
                            Map::<nat, nat>::new(
                                |j: nat| 0 <= j && j < old(self).view().len() - 1,
                                |j: nat| (j + 1) as nat,
                            ),
                        );
                    }
                },
            }
            proof {
                self.ptrs@ = self.ptrs@.subrange(1, self.ptrs@.len() as int);
                if self.ptrs@.len() > 0 {
                    assert(self.wf_perm(0));
                }
                assert(forall|i: nat|
                    i < self.view().len() && old(self).wf_perm(i + 1) ==> self.wf_perm(i));
                assert forall|i: int| 0 <= i && i < self@.len() implies #[trigger] self@[i] == old(
                    self,
                )@.subrange(1, old(self)@.len() as int)[i] by {
                    assert(old(self).wf_perm(i as nat + 1));  // trigger
                }
                assert(self@ =~= old(self)@.subrange(1, old(self)@.len() as int));
            }
            v
        }

        pub fn push_front(&mut self, v: V)
            requires
                old(self).well_formed(),
            ensures
                self.well_formed(),
                self@ == seq![v].add(old(self)@),
        {
            match &self.head {
                None => {
                    // Special case: list is empty
                    proof {
                        assert_by_contradiction!(self.ptrs@.len() == 0, {
                        assert(self.wf_perm((self.ptrs@.len() - 1) as nat));
                    });
                    }
                    self.push_empty_case(v);
                    assert(self@ =~= seq![v].add(old(self)@));
                },
                Some(head_ptr) => {
                    assert(self.ptrs@.len() > 0);
                    assert(self.wf_perm(0));
                    let tracked mut head_perm =
                        self.perms.borrow_mut().tracked_remove(0);
                    let mut head_node = head_ptr.take(Tracked(&mut head_perm));
                    let second_ptr = head_node.next;
                    let (ptr, Tracked(perm)) = PPtr::new(
                        Node::<V> { prev: None, next: Some(head_ptr.clone()), value: v },
                    );
                    head_node.prev = Some(ptr.clone());
                    head_node.next = second_ptr;
                    head_ptr.put(Tracked(&mut head_perm), head_node);
                    proof {
                        self.perms.borrow_mut().tracked_insert(0, head_perm);
                        assert forall|j: nat|
                            0 <= j && j < old(self)@.len() implies self.perms@.dom().contains(
                            j,
                        ) by {
                            assert(old(self).wf_perm(j));
                        }
                        self.perms.borrow_mut().tracked_map_keys_in_place(
                            Map::<nat, nat>::new(
                                |j: nat| 1 <= j && j <= old(self).view().len(),
                                |j: nat| (j - 1) as nat,
                            ),
                        );
                        self.perms.borrow_mut().tracked_insert(0, perm);
                        self.ptrs@ = seq![ptr].add(self.ptrs@);
                    }
                    self.head = Some(ptr);
                    let ghost i = 1;
                    let ghost next_of_i = self.next_of(i);
                    assert(self.wf_perm(1));
                    assert(self.wf_perm(0));
                    assert(forall|i: nat|
                        1 <= i && i <= old(self).ptrs@.len() && old(self).wf_perm((i - 1) as nat)
                            ==> #[trigger] self.wf_perm(i));
                    assert(self@[0] == v);
                    assert forall|i: int| 1 <= i && i <= self.ptrs@.len() as int - 1 implies old(
                        self,
                    )@[i - 1] == self@[i] by {
                        assert(old(self).wf_perm((i - 1) as nat));  // trigger
                    }
                    assert(self@ =~= seq![v].add(old(self)@));
                },
            }
        }
    }

    pub struct Iterator<'a, V> {
        l: &'a DoublyLinkedList<V>,
        cur: Option<PPtr<Node<V>>>,
        index: Ghost<nat>,
    }

    impl<'a, V> Iterator<'a, V> {
        pub closed spec fn list(&self) -> &'a DoublyLinkedList<V> {
            self.l
        }

        pub closed spec fn index(&self) -> nat {
            self.index@
        }

        pub closed spec fn valid(&self) -> bool {
            &&& self.list().well_formed()
            &&& self.index@ < self.list()@.len()
            &&& self.cur.is_some() && self.cur.unwrap() =~= self.l.ptrs@[self.index@ as int]
        }

        pub fn new(l: &'a DoublyLinkedList<V>) -> (it: Self)
            requires
                l.well_formed(),
                l@.len() > 0,
            ensures
                it.valid(),
                it.index() == 0,
                it.list() == l,
        {
            Iterator { l, cur: l.head, index: Ghost(0) }
        }

        pub fn value(&self) -> (v: &V)
            requires
                self.valid(),
            ensures
                v == self.list()@[self.index() as int],
        {
            let cur = self.cur.unwrap();
            assert(self.l.wf_perm(self.index()));
            let tracked perm = self.l.perms.borrow().tracked_borrow(self.index());
            let node = cur.borrow(Tracked(perm));
            &node.value
        }

        pub fn move_next(&mut self) -> (good: bool)
            requires
                old(self).valid(),
            ensures
                old(self).list() == self.list(),
                good == (old(self).index() < old(self).list()@.len() - 1),
                good ==> (self.valid() && self.index() == old(self).index() + 1),
        {
            assert(self.l.wf_perm(self.index()));
            let cur = self.cur.unwrap();
            let tracked perm = self.l.perms.borrow().tracked_borrow(self.index());
            let node = cur.borrow(Tracked(perm));
            proof {
                self.index@ = self.index@ + 1;
            }
            match &node.next {
                None => {
                    self.cur = None;
                    false
                },
                Some(next_ptr) => {
                    self.cur = Some(next_ptr.clone());
                    true
                },
            }
        }
    }

}

mod main {
    use super::doubly_linked_list::{DoublyLinkedList, Iterator};

    pub fn run() {
        let mut t = DoublyLinkedList::<u32>::new();
        t.push_back(2);
        t.push_back(3);
        t.push_front(1);  // 1, 2, 3
        let mut it = Iterator::new(&t);
        let v1 = it.value();
        assert(*v1 == 1);
        let g = it.move_next();
        let v2 = it.value();
        assert(*v2 == 2);
        let _ = it.move_next();
        let v3 = it.value();
        assert(*v3 == 3);
        let g = it.move_next();
        assert(!g);
        let x = t.pop_back();  // 3
        let y = t.pop_front();  // 1
        let z = t.pop_front();  // 2
        assert(x == 3);
        assert(y == 1);
        assert(z == 2);
    }

}

fn main() {
    main::run();
}

} // verus!
