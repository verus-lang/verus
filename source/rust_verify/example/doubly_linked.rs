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
        payload: V,
    }

    // Doubly-linked list
    // Contains head pointer, tail pointer
    // and in ghost code, tracks all the pointers and all the PointsTo permissions
    // to access the nodes
    pub struct DoublyLinkedList<V> {
        // physical data:
        head: Option<PPtr<Node<V>>>,
        tail: Option<PPtr<Node<V>>>,

        // ghost and tracked data:
        ghost_state: Tracked<GhostState<V>>,
    }

    pub tracked struct GhostState<V> {
        ghost ptrs: Seq<PPtr<Node<V>>>,
        tracked points_to_map: Map<nat, PointsTo<Node<V>>>,
    }

    impl<V> DoublyLinkedList<V> {
        /// Pointer to the node of index (i-1), or None if i is 0.
        spec fn prev_of(&self, i: nat) -> Option<PPtr<Node<V>>> {
            if i == 0 {
                None
            } else {
                Some(self.ghost_state@.ptrs[i as int - 1])
            }
        }

        /// Pointer to the node of index (i+1), or None if i is the last index.
        spec fn next_of(&self, i: nat) -> Option<PPtr<Node<V>>> {
            if i + 1 == self.ghost_state@.ptrs.len() {
                None
            } else {
                Some(self.ghost_state@.ptrs[i as int + 1])
            }
        }

        /// Node at index `i` is well-formed
        spec fn well_formed_node(&self, i: nat) -> bool {
            &&& self.ghost_state@.points_to_map.dom().contains(i)
            &&& self.ghost_state@.points_to_map[i].pptr() == self.ghost_state@.ptrs[i as int]
            &&& self.ghost_state@.points_to_map[i].mem_contents() matches MemContents::Init(node)
                  && node.prev == self.prev_of(i) && node.next == self.next_of(i)
        }

        /// Linked list is well-formed
        pub closed spec fn well_formed(&self) -> bool {
            // Every node from 0 .. len - 1 is well-formed
            &&& forall|i: nat| 0 <= i && i < self.ghost_state@.ptrs.len() ==> self.well_formed_node(i)
            &&& if self.ghost_state@.ptrs.len() == 0 {
                // If the list is empty, then the `head` and `tail` pointers are both None
                self.head.is_none() && self.tail.is_none()
            } else {
                // If the list is non-empty, then `head` and `tail` pointers point to the
                // the first and last nodes.
                &&& self.head == Some(self.ghost_state@.ptrs[0])
                &&& self.tail == Some(self.ghost_state@.ptrs[self.ghost_state@.ptrs.len() as int - 1])
            }
        }

        /// Representation of this list as a sequence
        pub closed spec fn view(&self) -> Seq<V> {
            Seq::<V>::new(
                self.ghost_state@.ptrs.len(),
                |i: int| { self.ghost_state@.points_to_map[i as nat].value().payload },
            )
        }

        //// Interface of executable functions

        /// Construct a new, empty, doubly-linked list.
        pub fn new() -> (s: Self)
            ensures
                s.well_formed(),
                s@.len() == 0,
        {
            DoublyLinkedList {
                ghost_state: Tracked(GhostState {
                    ptrs: Seq::empty(),
                    points_to_map: Map::tracked_empty(),
                }),
                head: None,
                tail: None,
            }
        }

        /// Insert one node, assuming the linked list is empty.
        fn push_empty_case(&mut self, v: V)
            requires
                old(self).well_formed(),
                old(self).ghost_state@.ptrs.len() == 0,
            ensures
                self.well_formed(),
                self@ =~= old(self)@.push(v),
        {
            // Allocate a node to contain the payload
            let (ptr, Tracked(points_to)) = PPtr::<Node<V>>::new(
                Node::<V> { prev: None, next: None, payload: v },
            );

            // Update head and tail pointers
            self.tail = Some(ptr);
            self.head = Some(ptr);

            // Update proof state
            proof {
                self.ghost_state.borrow_mut().ptrs = self.ghost_state@.ptrs.push(ptr);
                self.ghost_state.borrow_mut().points_to_map.tracked_insert(
                    (self.ghost_state@.ptrs.len() - 1) as nat,
                    points_to,
                );
            }
        }

        /// Insert a value to the end of the list
        pub fn push_back(&mut self, v: V)
            requires
                old(self).well_formed(),
            ensures
                self.well_formed(),
                self@ == old(self)@.push(v),
        {
            match self.tail {
                None => {
                    // Special case: list is empty
                    proof {
                        // Show that the `self.tail == None` implies the list is empty
                        assert_by_contradiction!(self.ghost_state@.ptrs.len() == 0,
                        {
                            assert(self.well_formed_node((self.ghost_state@.ptrs.len() - 1) as nat)); // trigger
                        });
                    }
                    self.push_empty_case(v);
                }
                Some(old_tail_ptr) => {
                    proof {
                        assert(self.well_formed_node((self.ghost_state@.ptrs.len() - 1) as nat)); // trigger
                    }

                    // Allocate a new node to go on the end. It's 'prev' field points
                    // to the old tail pointer.
                    let (new_tail_ptr, Tracked(new_tail_pointsto)) = PPtr::<Node<V>>::new(
                        Node::<V> { prev: Some(old_tail_ptr), next: None, payload: v },
                    );

                    // Update the 'next' pointer of the previous tail node
                    // This is all equivalent to `(*old_tail_ptr).next = new_tail_ptr;`
                    let tracked mut old_tail_pointsto: PointsTo<Node<V>> =
                        self.ghost_state.borrow_mut().points_to_map.tracked_remove((self.ghost_state@.ptrs.len() - 1) as nat);
                    let mut old_tail_node = old_tail_ptr.take(Tracked(&mut old_tail_pointsto));
                    old_tail_node.next = Some(new_tail_ptr);
                    old_tail_ptr.put(Tracked(&mut old_tail_pointsto), old_tail_node);
                    proof {
                        self.ghost_state.borrow_mut().points_to_map.tracked_insert(
                            (self.ghost_state@.ptrs.len() - 1) as nat,
                            old_tail_pointsto,
                        );
                    }

                    // Update `self.tail`
                    self.tail = Some(new_tail_ptr);

                    proof {
                        // Put the new tail's PointsTo into the map
                        self.ghost_state.borrow_mut().points_to_map.tracked_insert(self.ghost_state@.ptrs.len(), new_tail_pointsto);
                        self.ghost_state@.ptrs = self.ghost_state@.ptrs.push(new_tail_ptr);

                        // Additional proof work to help the solver show that
                        // `self.well_formed()` has been restored.
                        assert(self.well_formed_node((self.ghost_state@.ptrs.len() - 2) as nat));
                        assert(self.well_formed_node((self.ghost_state@.ptrs.len() - 1) as nat));
                        assert(forall|i: nat| i < self.ghost_state@.ptrs.len() && old(self).well_formed_node(i)
                            ==> self.well_formed_node(i));
                        assert forall|i: int| 0 <= i && i < self.ghost_state@.ptrs.len() as int - 1
                            implies old(self)@[i] == self@[i]
                        by {
                            assert(old(self).well_formed_node(i as nat));  // trigger
                        }
                        assert(self@ =~= old(self)@.push(v));

                        assert(self.well_formed());
                    }
                }
            }
        }

        /// Take a value from the end of the list. Requires the list to be non-empty.
        pub fn pop_back(&mut self) -> (v: V)
            requires
                old(self).well_formed(),
                old(self)@.len() > 0,
            ensures
                self.well_formed(),
                self@ == old(self)@.drop_last(),
                v == old(self)@[old(self)@.len() as int - 1],
        {
            assert(self.well_formed_node((self.ghost_state@.ptrs.len() - 1) as nat));

            // Deallocate the last node in the list and get the payload.
            // Note self.tail.unwrap() will always succeed because of the precondition `len > 0`
            let last_ptr = self.tail.unwrap();
            let tracked last_pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove(
                (self.ghost_state@.ptrs.len() - 1) as nat,
            );
            let last_node = last_ptr.into_inner(Tracked(last_pointsto));
            let v = last_node.payload;

            match last_node.prev {
                None => {
                    // If this was the *only* node in the list,
                    // we set both `head` and `tail` to None
                    self.tail = None;
                    self.head = None;
                    proof {
                        assert_by_contradiction!(self.ghost_state@.ptrs.len() == 1,
                        {
                            assert(old(self).well_formed_node((self.ghost_state@.ptrs.len() - 2) as nat)); // trigger
                        });
                    }
                },
                Some(penultimate_ptr) => {
                    assert(old(self)@.len() >= 2);
                    assert(old(self).well_formed_node((self.ghost_state@.ptrs.len() - 2) as nat));

                    // Otherwise, we need to set the 'tail' pointer to the (new) tail pointer,
                    // i.e., the pointer that was previously the second-to-last pointer.
                    self.tail = Some(penultimate_ptr);

                    // And we need to set the 'next' pointer of the new tail node to None.
                    let tracked mut penultimate_pointsto =
                        self.ghost_state.borrow_mut().points_to_map.tracked_remove((self.ghost_state@.ptrs.len() - 2) as nat);
                    let mut penultimate_node = penultimate_ptr.take(Tracked(&mut penultimate_pointsto));
                    penultimate_node.next = None;
                    penultimate_ptr.put(Tracked(&mut penultimate_pointsto), penultimate_node);
                    proof {
                        self.ghost_state.borrow_mut().points_to_map.tracked_insert(
                            (self.ghost_state@.ptrs.len() - 2) as nat,
                            penultimate_pointsto,
                        );
                    }
                },
            }

            // Additional proof work to help the solver show that
            // `self.well_formed()` has been restored.
            proof {
                self.ghost_state@.ptrs = self.ghost_state@.ptrs.drop_last();
                if self.ghost_state@.ptrs.len() > 0 {
                    assert(self.well_formed_node((self.ghost_state@.ptrs.len() - 1) as nat));
                }
                assert(forall|i: nat| i < self@.len() && old(self).well_formed_node(i) ==> self.well_formed_node(i));
                assert forall|i: int| 0 <= i && i < self@.len() implies #[trigger] self@[i] == old(
                    self,
                )@.drop_last()[i] by {
                    assert(old(self).well_formed_node(i as nat));  // trigger
                }
                assert(self@ =~= old(self)@.drop_last());

                assert(self.well_formed());
            }

            return v;
        }

        /// Insert a value to the front of the list
        pub fn push_front(&mut self, v: V)
            requires
                old(self).well_formed(),
            ensures
                self.well_formed(),
                self@ == seq![v].add(old(self)@),
        {
            match self.head {
                None => {
                    // Special case: list is empty
                    proof {
                        // Show that the `self.head == None` implies the list is empty
                        assert_by_contradiction!(self.ghost_state@.ptrs.len() == 0, {
                            assert(self.well_formed_node((self.ghost_state@.ptrs.len() - 1) as nat));
                        });
                    }
                    self.push_empty_case(v);
                    assert(self@ =~= seq![v].add(old(self)@));
                }
                Some(old_head_ptr) => {
                    proof {
                        assert(self.ghost_state@.ptrs.len() > 0);
                        assert(self.well_formed_node(0));
                    }

                    // Allocate a new node to go at the front. It's 'next' field points
                    // to the old head pointer.
                    let (new_head_ptr, Tracked(new_head_pointsto)) = PPtr::new(
                        Node::<V> { prev: None, next: Some(old_head_ptr), payload: v },
                    );

                    // Update the 'tail' pointer of the previous head node
                    // This is all equivalent to `(*old_head_ptr).next = new_head_ptr;`
                    let tracked mut old_head_pointsto =
                        self.ghost_state.borrow_mut().points_to_map.tracked_remove(0);
                    let mut old_head_node = old_head_ptr.take(Tracked(&mut old_head_pointsto));
                    old_head_node.prev = Some(new_head_ptr);
                    old_head_ptr.put(Tracked(&mut old_head_pointsto), old_head_node);
                    proof {
                        self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, old_head_pointsto);
                    }

                    // Update `self.head`
                    self.head = Some(new_head_ptr);

                    proof {
                        // Put the new head's PointsTo into the map.
                        // This goes in at index 0, so we have to shift all the keys up by 1.
                        assert forall|j: nat|
                            0 <= j && j < old(self)@.len() implies self.ghost_state@.points_to_map.dom().contains(
                            j,
                        ) by {
                            assert(old(self).well_formed_node(j));
                        }
                        self.ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                            Map::<nat, nat>::new(
                                |j: nat| 1 <= j && j <= old(self).view().len(),
                                |j: nat| (j - 1) as nat,
                            ),
                        );
                        self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, new_head_pointsto);
                        self.ghost_state@.ptrs = seq![new_head_ptr].add(self.ghost_state@.ptrs);

                        // Additional proof work to help the solver show that
                        // `self.well_formed()` has been restored.
                        assert(self.well_formed_node(0));
                        assert(self.well_formed_node(1));
                        assert(forall|i: nat|
                            1 <= i && i <= old(self).ghost_state@.ptrs.len() && old(self).well_formed_node((i - 1) as nat)
                                ==> #[trigger] self.well_formed_node(i));
                        assert forall|i: int| 1 <= i && i <= self.ghost_state@.ptrs.len() as int - 1
                            implies old(self)@[i - 1] == self@[i]
                        by {
                            assert(old(self).well_formed_node((i - 1) as nat));  // trigger
                        }
                        assert(self@ =~= seq![v].add(old(self)@));

                        assert(self.well_formed());
                    }
                }
            }
        }

        /// Take a value from the front of the list. Requires the list to be non-empty.
        pub fn pop_front(&mut self) -> (v: V)
            requires
                old(self).well_formed(),
                old(self).view().len() > 0,
            ensures
                self.well_formed(),
                self@ == old(self)@.subrange(1, old(self)@.len() as int),
                v == old(self)@[0],
        {
            assert(self.well_formed_node(0));

            // Deallocate the first node in the list and get the payload.
            // Note self.head.unwrap() will always succeed because of the precondition `len > 0`
            let first_ptr = self.head.unwrap();
            let tracked first_pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove(0);
            let first_node = first_ptr.into_inner(Tracked(first_pointsto));
            let v = first_node.payload;

            match first_node.next {
                None => {
                    // If this was the *only* node in the list,
                    // we set both `head` and `tail` to None
                    self.tail = None;
                    self.head = None;
                    proof {
                        assert_by_contradiction!(self.ghost_state@.ptrs.len() == 1,
                        {
                            assert(old(self).well_formed_node(1)); // trigger
                        });
                    }
                }
                Some(second_ptr) => {
                    assert(old(self)@.len() >= 2);
                    assert(old(self).well_formed_node(1));

                    // Otherwise, we need to set the 'head' pointer to the (new) head pointer,
                    // i.e., the pointer that was previously the second pointer.
                    self.head = Some(second_ptr);

                    // And we need to set the 'tail' pointer of the new head node to None
                    let tracked mut second_pointsto = self.ghost_state.borrow_mut().points_to_map.tracked_remove(1);
                    let mut second_node = second_ptr.take(Tracked(&mut second_pointsto));
                    second_node.prev = None;
                    second_ptr.put(Tracked(&mut second_pointsto), second_node);
                    proof {
                        self.ghost_state.borrow_mut().points_to_map.tracked_insert(1, second_pointsto);

                        // Since we removed index 0, we need to shift all the keys down,
                        // 1 -> 0, 2 -> 1, etc.
                        assert forall|j: nat|
                            1 <= j && j < old(self)@.len() implies self.ghost_state@.points_to_map.dom().contains(
                            j,
                        ) by {
                            assert(old(self).well_formed_node(j));
                        };
                        self.ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                            Map::<nat, nat>::new(
                                |j: nat| 0 <= j && j < old(self).view().len() - 1,
                                |j: nat| (j + 1) as nat,
                            ),
                        );
                    }
                }
            }

            // Additional proof work to help the solver show that
            // `self.well_formed()` has been restored.
            proof {
                self.ghost_state@.ptrs = self.ghost_state@.ptrs.subrange(1, self.ghost_state@.ptrs.len() as int);
                if self.ghost_state@.ptrs.len() > 0 {
                    assert(self.well_formed_node(0));
                }
                assert(forall|i: nat|
                    i < self.view().len() && old(self).well_formed_node(i + 1) ==> self.well_formed_node(i));
                assert forall|i: int| 0 <= i && i < self@.len() implies #[trigger] self@[i] == old(
                    self,
                )@.subrange(1, old(self)@.len() as int)[i] by {
                    assert(old(self).well_formed_node(i as nat + 1));  // trigger
                }
                assert(self@ =~= old(self)@.subrange(1, old(self)@.len() as int));

                assert(self.well_formed());
            }

            return v;
        }

        /// Get a reference to the i^th value in the list
        fn get<'a>(&'a self, i: usize) -> (v: &'a V)
            requires
                self.well_formed(),
                0 <= i < self@.len(),
            ensures
                *v == self@[i as int]
        {
            // Iterate the nodes from 0 to j, starting at the head node
            let mut j = 0;
            let mut ptr = self.head.unwrap();
            while j < i
                invariant
                    self.well_formed(),
                    0 <= j <= i < self@.len(),
                    ptr == self.ghost_state@.ptrs[j as int],
            {
                proof {
                    assert(self.well_formed_node(j as nat)); // trigger
                }

                // Get the next node from the 'next' field
                let tracked pointsto_ref: &PointsTo<Node<V>> =
                    self.ghost_state.borrow().points_to_map.tracked_borrow(j as nat);
                let node_ref: &Node<V> = ptr.borrow(Tracked(pointsto_ref));
                let next_ptr = node_ref.next.unwrap();

                j += 1;
                ptr = next_ptr;
            }

            proof {
                assert(self.well_formed_node(j as nat)); // trigger
            }

            // Get a reference to this node's payload and return it
            let tracked pointsto_ref: &PointsTo<Node<V>> =
                self.ghost_state.borrow().points_to_map.tracked_borrow(j as nat);
            let node_ref: &Node<V> = ptr.borrow(Tracked(pointsto_ref));
            return &node_ref.payload;
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
            &&& self.cur.is_some() && self.cur.unwrap() =~= self.l.ghost_state@.ptrs[self.index@ as int]
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
            assert(self.l.well_formed_node(self.index()));
            let tracked pointsto = self.l.ghost_state.borrow().points_to_map.tracked_borrow(self.index());
            let node = cur.borrow(Tracked(pointsto));
            &node.payload
        }

        pub fn move_next(&mut self) -> (good: bool)
            requires
                old(self).valid(),
            ensures
                old(self).list() == self.list(),
                good == (old(self).index() < old(self).list()@.len() - 1),
                good ==> (self.valid() && self.index() == old(self).index() + 1),
        {
            assert(self.l.well_formed_node(self.index()));
            let cur = self.cur.unwrap();
            let tracked pointsto = self.l.ghost_state.borrow().points_to_map.tracked_borrow(self.index());
            let node = cur.borrow(Tracked(pointsto));
            proof {
                self.index@ = self.index@ + 1;
            }
            match node.next {
                None => {
                    self.cur = None;
                    false
                },
                Some(next_ptr) => {
                    self.cur = Some(next_ptr);
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
