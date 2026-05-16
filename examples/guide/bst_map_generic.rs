// ANCHOR: all
use vstd::prelude::*;

verus!{

// ANCHOR: trait
pub enum Cmp { Less, Equal, Greater }

pub trait TotalOrdered : Sized {
    spec fn le(self, other: Self) -> bool;

    proof fn reflexive(x: Self)
        ensures Self::le(x, x);

    proof fn transitive(x: Self, y: Self, z: Self)
        requires Self::le(x, y), Self::le(y, z),
        ensures Self::le(x, z);

    proof fn antisymmetric(x: Self, y: Self)
        requires Self::le(x, y), Self::le(y, x),
        ensures x == y;

    proof fn total(x: Self, y: Self)
        ensures Self::le(x, y) || Self::le(y, x);

    fn compare(&self, other: &Self) -> (c: Cmp)
        ensures (match c {
            Cmp::Less => self.le(*other) && self != other,
            Cmp::Equal => self == other,
            Cmp::Greater => other.le(*self) && self != other,
        }),
        no_unwind;
}
// ANCHOR_END: trait

// ANCHOR: structs
struct Node<K: TotalOrdered, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
}

// ANCHOR: tree_map_struct
pub struct TreeMap<K: TotalOrdered, V> {
    root: Option<Box<Node<K, V>>>,
}
// ANCHOR_END: tree_map_struct
// ANCHOR_END: structs

impl<K: TotalOrdered, V> Node<K, V> {
    spec fn optional_as_map(node_opt: Option<Box<Node<K, V>>>) -> Map<K, V>
        decreases node_opt,
    {
        match node_opt {
            None => Map::empty(),
            Some(node) => node.as_map(),
        }
    }

    pub closed spec fn as_map(self) -> Map<K, V>
        decreases self,
    {
        Node::<K, V>::optional_as_map(self.left)
          .union_prefer_right(Node::<K, V>::optional_as_map(self.right))
          .insert(self.key, self.value)
    }
}

impl<K: TotalOrdered, V> TreeMap<K, V> {
    pub closed spec fn as_map(self) -> Map<K, V> {
        Node::<K, V>::optional_as_map(self.root)
    }
}

impl<K: TotalOrdered, V> View for TreeMap<K, V> {
    type V = Map<K, V>;

    open spec fn view(&self) -> Map<K, V> {
        self.as_map()
    }
}

// ANCHOR: well_formed
impl<K: TotalOrdered, V> Node<K, V> {
    pub closed spec fn well_formed(self) -> bool
        decreases self
    {
        &&& (forall |elem| #[trigger] Node::<K, V>::optional_as_map(self.left).dom().contains(elem) ==> elem.le(self.key) && elem != self.key)
        &&& (forall |elem| #[trigger] Node::<K, V>::optional_as_map(self.right).dom().contains(elem) ==> self.key.le(elem) && elem != self.key)
        &&& (match self.left {
            Some(left_node) => left_node.well_formed(),
            None => true,
        })
        &&& (match self.right {
            Some(right_node) => right_node.well_formed(),
            None => true,
        })
    }
}

impl<K: TotalOrdered, V> TreeMap<K, V> {
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        match self.root {
            Some(node) => node.well_formed(),
            None => true, // empty tree always well-formed
        }
    }
}
// ANCHOR_END: well_formed

impl<K: TotalOrdered, V> TreeMap<K, V> {
    pub fn new() -> (s: Self)
        ensures
            s@ == Map::<K, V>::empty(),
    {
        TreeMap::<K, V> { root: None }
    }
}

impl<K: TotalOrdered, V> Node<K, V> {
    fn insert_into_optional(node: &mut Option<Box<Node<K, V>>>, key: K, value: V)
        requires
            old(node).is_some() ==> old(node).unwrap().well_formed(),
        ensures
            final(node).is_some() ==> final(node).unwrap().well_formed(),
            Node::<K, V>::optional_as_map(*final(node)) =~= Node::<K, V>::optional_as_map(*old(node)).insert(key, value),
        decreases *old(node),
    {
        if node.is_none() {
            *node = Some(Box::new(Node::<K, V> {
                key: key,
                value: value,
                left: None,
                right: None,
            }));
        } else {
            let mut tmp = None;
            std::mem::swap(&mut tmp, node);
            let mut boxed_node = tmp.unwrap();

            (&mut *boxed_node).insert(key, value);

            *node = Some(boxed_node);
        }
    }

    fn insert(&mut self, key: K, value: V)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).as_map() =~= old(self).as_map().insert(key, value),
        decreases *old(self),
    {
        match key.compare(&self.key) {
            Cmp::Equal => {
                self.value = value;

                assert(!Node::<K, V>::optional_as_map(self.left).dom().contains(key));
                assert(!Node::<K, V>::optional_as_map(self.right).dom().contains(key));
            }
            Cmp::Less => {
                Self::insert_into_optional(&mut self.left, key, value);

                proof {
                    if self.key.le(key) {
                        TotalOrdered::antisymmetric(self.key, key);
                    }
                    assert(!Node::<K, V>::optional_as_map(self.right).dom().contains(key));
                }
            }
            Cmp::Greater => {
                Self::insert_into_optional(&mut self.right, key, value);

                proof {
                    if key.le(self.key) {
                        TotalOrdered::antisymmetric(self.key, key);
                    }
                    assert(!Node::<K, V>::optional_as_map(self.left).dom().contains(key));
                }
            }
        }
    }
}

impl<K: TotalOrdered, V> TreeMap<K, V> {
    pub fn insert(&mut self, key: K, value: V)
        ensures
            final(self)@ == old(self)@.insert(key, value)
    {
        proof { use_type_invariant(&*self); }
        let mut root = None;
        std::mem::swap(&mut root, &mut self.root);
        Node::<K, V>::insert_into_optional(&mut root, key, value);
        self.root = root;
    }
}

impl<K: TotalOrdered, V> Node<K, V> {
    fn delete_from_optional(node: &mut Option<Box<Node<K, V>>>, key: K)
        requires
            old(node).is_some() ==> old(node).unwrap().well_formed(),
        ensures
            final(node).is_some() ==> final(node).unwrap().well_formed(),
            Node::<K, V>::optional_as_map(*final(node)) =~= Node::<K, V>::optional_as_map(*old(node)).remove(key),
        decreases *old(node),
    {
        if node.is_some() {
            let mut tmp = None;
            std::mem::swap(&mut tmp, node);
            let mut boxed_node = tmp.unwrap();

            match key.compare(&boxed_node.key) {
                Cmp::Equal => {
                    assert(!Node::<K, V>::optional_as_map(boxed_node.left).dom().contains(key));
                    assert(!Node::<K, V>::optional_as_map(boxed_node.right).dom().contains(key));
                    assert(boxed_node.right.is_some() ==> boxed_node.right.unwrap().well_formed());
                    assert(boxed_node.left.is_some() ==> boxed_node.left.unwrap().well_formed());

                    if boxed_node.left.is_none() {
                        *node = boxed_node.right;
                    } else {
                        if boxed_node.right.is_none() {
                            *node = boxed_node.left;
                        } else {
                            let (popped_key, popped_value) = Node::<K, V>::delete_rightmost(&mut boxed_node.left);
                            boxed_node.key = popped_key;
                            boxed_node.value = popped_value;
                            *node = Some(boxed_node);

                            proof {
                                assert forall |elem| #[trigger] Node::<K, V>::optional_as_map(node.unwrap().right).dom().contains(elem) implies node.unwrap().key.le(elem) && elem != node.unwrap().key
                                by {
                                    TotalOrdered::transitive(node.unwrap().key, key, elem);
                                    if elem == node.unwrap().key {
                                        TotalOrdered::antisymmetric(elem, key);
                                    }
                                }
                            }
                        }
                    }
                }
                Cmp::Less => {
                    proof {
                        if Node::<K, V>::optional_as_map(boxed_node.right).dom().contains(key) {
                            TotalOrdered::antisymmetric(boxed_node.key, key);
                            assert(false);
                        }
                    }
                    Node::<K, V>::delete_from_optional(&mut boxed_node.left, key);
                    *node = Some(boxed_node);
                }
                Cmp::Greater => {
                    proof {
                        if Node::<K, V>::optional_as_map(boxed_node.left).dom().contains(key) {
                            TotalOrdered::antisymmetric(boxed_node.key, key);
                            assert(false);
                        }
                    }
                    Node::<K, V>::delete_from_optional(&mut boxed_node.right, key);
                    *node = Some(boxed_node);
                }
            }
        }
    }

    fn delete_rightmost(node: &mut Option<Box<Node<K, V>>>) -> (popped: (K, V))
        requires
            old(node).is_some(),
            old(node).unwrap().well_formed(),
        ensures
            final(node).is_some() ==> final(node).unwrap().well_formed(),
            Node::<K, V>::optional_as_map(*final(node)) =~= Node::<K, V>::optional_as_map(*old(node)).remove(popped.0),
            Node::<K, V>::optional_as_map(*old(node)).dom().contains(popped.0),
            Node::<K, V>::optional_as_map(*old(node))[popped.0] == popped.1,
            forall |elem| #[trigger] Node::<K, V>::optional_as_map(*old(node)).dom().contains(elem) ==> elem.le(popped.0),
        decreases *old(node),
    {
        let mut tmp = None;
        std::mem::swap(&mut tmp, node);
        let mut boxed_node = tmp.unwrap();

        if boxed_node.right.is_none() {
            *node = boxed_node.left;
            proof {
                assert(Node::<K, V>::optional_as_map(boxed_node.right) =~= Map::empty());
                assert(!Node::<K, V>::optional_as_map(boxed_node.left).dom().contains(boxed_node.key));
                TotalOrdered::reflexive(boxed_node.key);
            }
            return (boxed_node.key, boxed_node.value);
        } else {
            let (popped_key, popped_value) = Node::<K, V>::delete_rightmost(&mut boxed_node.right);
            proof {
                if Node::<K, V>::optional_as_map(boxed_node.left).dom().contains(popped_key) {
                    TotalOrdered::antisymmetric(boxed_node.key, popped_key);
                    assert(false);
                }
                assert forall |elem| #[trigger] Node::<K, V>::optional_as_map(*old(node)).dom().contains(elem) implies elem.le(popped_key)
                by {
                    if elem.le(boxed_node.key) {
                        TotalOrdered::transitive(elem, boxed_node.key, popped_key);
                    }
                }
            }
            *node = Some(boxed_node);
            return (popped_key, popped_value);
        }
    }
}

impl<K: TotalOrdered, V> TreeMap<K, V> {
    pub fn delete(&mut self, key: K)
        ensures
            final(self)@ == old(self)@.remove(key),
    {
        proof { use_type_invariant(&*self); }
        let mut root = None;
        std::mem::swap(&mut root, &mut self.root);
        Node::<K, V>::delete_from_optional(&mut root, key);
        self.root = root;
    }
}

// ANCHOR: node_get
impl<K: TotalOrdered, V> Node<K, V> {
    fn get_from_optional(node: &Option<Box<Node<K, V>>>, key: K) -> Option<&V>
        requires
            node.is_some() ==> node.unwrap().well_formed(),
        returns
            (match node {
                Some(node) => (if node.as_map().dom().contains(key) { Some(&node.as_map()[key]) } else { None }),
                None => None,
            }),
        decreases node,
    {
        match node {
            None => None,
            Some(node) => {
                node.get(key)
            }
        }
    }

    fn get(&self, key: K) -> Option<&V>
        requires
            self.well_formed(),
        returns
            (if self.as_map().dom().contains(key) { Some(&self.as_map()[key]) } else { None }),
        decreases self,
    {
        match key.compare(&self.key) {
            Cmp::Equal => {
                Some(&self.value)
            }
            Cmp::Less => {
                proof {
                    if Node::<K, V>::optional_as_map(self.right).dom().contains(key) {
                        TotalOrdered::antisymmetric(self.key, key);
                        assert(false);
                    }
                    assert(key != self.key);
                    assert((match self.left {
                            Some(node) => (if node.as_map().dom().contains(key) { Some(&node.as_map()[key]) } else { None }),
                            None => None,
                        }) == (if self.as_map().dom().contains(key) { Some(&self.as_map()[key]) } else { None }));
                }
                Self::get_from_optional(&self.left, key)
            }
            Cmp::Greater => {
                proof {
                    if Node::<K, V>::optional_as_map(self.left).dom().contains(key) {
                        TotalOrdered::antisymmetric(self.key, key);
                        assert(false);
                    }
                    assert(key != self.key);
                    assert((match self.right {
                            Some(node) => (if node.as_map().dom().contains(key) { Some(&node.as_map()[key]) } else { None }),
                            None => None,
                        }) == (if self.as_map().dom().contains(key) { Some(&self.as_map()[key]) } else { None }));
                }
                Self::get_from_optional(&self.right, key)
            }
        }
    }
}
// ANCHOR_END: node_get

impl<K: TotalOrdered, V> TreeMap<K, V> {
    pub fn get(&self, key: K) -> Option<&V>
        returns
            (if self@.dom().contains(key) { Some(&self@[key]) } else { None }),
    {
        proof { use_type_invariant(&*self); }
        Node::<K, V>::get_from_optional(&self.root, key)
    }
}

// ANCHOR: node_get_mut
impl<K: TotalOrdered, V> Node<K, V> {
    fn get_mut_from_optional(node: &mut Option<Box<Node<K, V>>>, key: K) -> (ret: Option<&mut V>)
        requires
            node.is_some() ==> node.unwrap().well_formed(),
        ensures
            (match ret {
                Some(r) =>
                    old(node).is_some()
                      && old(node).unwrap().as_map().dom().contains(key)
                      && *r == old(node).unwrap().as_map()[key]
                      && final(node).is_some()
                      && final(node).unwrap().well_formed()
                      && final(node).unwrap().as_map() == old(node).unwrap().as_map().insert(key, *final(r))
                      && Node::optional_as_map(*final(node)).dom() =~= Node::optional_as_map(*old(node)).dom(),
                None =>
                    (old(node).is_some() ==> !old(node).unwrap().as_map().dom().contains(key))
                      && *final(node) == *old(node)
            }),
        decreases *node,
        no_unwind
    {
        match node {
            None => None,
            Some(node) => {
                node.get_mut(key)
            }
        }
    }

    fn get_mut(&mut self, key: K) -> (ret: Option<&mut V>)
        requires
            self.well_formed(),
        ensures
            (match ret {
                Some(r) =>
                    old(self).as_map().dom().contains(key)
                      && *r == old(self).as_map()[key]
                      && final(self).well_formed()
                      && final(self).as_map() == old(self).as_map().insert(key, *final(r))
                      && final(self).as_map().dom() =~= old(self).as_map().dom(),
                None =>
                    !old(self).as_map().dom().contains(key)
                      && *final(self) == *old(self)
            })
        decreases *self,
        no_unwind
    {
        match key.compare(&self.key) {
            Cmp::Equal => {
                Some(&mut self.value)
            }
            Cmp::Less => {
                proof {
                    if Node::<K, V>::optional_as_map(self.right).dom().contains(key) {
                        TotalOrdered::antisymmetric(self.key, key);
                        assert(false);
                    }
                    assert(key != self.key);
                    assert((match self.left {
                            Some(node) => (if node.as_map().dom().contains(key) { Some(&node.as_map()[key]) } else { None }),
                            None => None,
                        }) == (if self.as_map().dom().contains(key) { Some(&self.as_map()[key]) } else { None }));
                }
                Self::get_mut_from_optional(&mut self.left, key)
            }
            Cmp::Greater => {
                proof {
                    if Node::<K, V>::optional_as_map(self.left).dom().contains(key) {
                        TotalOrdered::antisymmetric(self.key, key);
                        assert(false);
                    }
                    assert(key != self.key);
                    assert((match self.right {
                            Some(node) => (if node.as_map().dom().contains(key) { Some(&node.as_map()[key]) } else { None }),
                            None => None,
                        }) == (if self.as_map().dom().contains(key) { Some(&self.as_map()[key]) } else { None }));
                }
                Self::get_mut_from_optional(&mut self.right, key)
            }
        }
    }
}
// ANCHOR_END: node_get_mut

impl<K: TotalOrdered, V> TreeMap<K, V> {
    pub fn get_mut(&mut self, key: K) -> (ret: Option<&mut V>)
        ensures
            (match ret {
                Some(r) =>
                    old(self)@.dom().contains(key)
                      && *r == old(self)@[key]
                      && final(self).as_map() == old(self)@.insert(key, *final(r)),
                None =>
                    !old(self)@.dom().contains(key)
                      && *final(self) == *old(self)
            })
    {
        proof { use_type_invariant(&*self); }
        Node::<K, V>::get_mut_from_optional(&mut self.root, key)
    }
}

// ANCHOR: clone_full_impl
impl<K: Copy + TotalOrdered, V: Clone> Clone for Node<K, V> {
    fn clone(&self) -> (res: Self)
        ensures
            self.well_formed() ==> res.well_formed(),
            self.as_map().dom() =~= res.as_map().dom(),
            forall |key| #[trigger] res.as_map().dom().contains(key) ==>
                cloned::<V>(self.as_map()[key], res.as_map()[key]),
        decreases self,
    {
        let res = Node {
            key: self.key,
            value: self.value.clone(),
            // Ordinarily, we would use Option<Node>::clone rather than inlining
            // the case statement here; we write it this way to work around
            // this issue: https://github.com/verus-lang/verus/issues/1346
            left: (match &self.left {
                Some(node) => Some(Box::new((&**node).clone())),
                None => None,
            }),
            right: (match &self.right {
                Some(node) => Some(Box::new((&**node).clone())),
                None => None,
            }),
        };

        proof {
            assert(Node::optional_as_map(res.left).dom() =~= 
                Node::optional_as_map(self.left).dom());
            assert(Node::optional_as_map(res.right).dom() =~= 
                Node::optional_as_map(self.right).dom());
        }

        return res;
    }
}

// ANCHOR: clone_signature
impl<K: Copy + TotalOrdered, V: Clone> Clone for TreeMap<K, V> {
    fn clone(&self) -> (res: Self)
        ensures self@.dom() =~= res@.dom(),
            forall |key| #[trigger] res@.dom().contains(key) ==>
                cloned::<V>(self@[key], res@[key]),
// ANCHOR_END: clone_signature
    {
        proof {
            use_type_invariant(self);
        }

        TreeMap {
            // This calls Option<Node<K, V>>::Clone
            root: self.root.clone(),
        }
    }
}
// ANCHOR_END: clone_full_impl

impl TotalOrdered for u64 {
    open spec fn le(self, other: Self) -> bool { self <= other }

    proof fn reflexive(x: Self) { }
    proof fn transitive(x: Self, y: Self, z: Self) { }
    proof fn antisymmetric(x: Self, y: Self) { }
    proof fn total(x: Self, y: Self) { }

    fn compare(&self, other: &Self) -> (c: Cmp) {
        if *self == *other {
            Cmp::Equal
        } else if *self < *other {
            Cmp::Less
        } else {
            Cmp::Greater
        }
    }
}

fn test() {
    let mut tree_map = TreeMap::<u64, bool>::new();
    tree_map.insert(17, false);
    tree_map.insert(18, false);
    tree_map.insert(17, true);

    assert(tree_map@ == map![17u64 => true, 18u64 => false]);

    tree_map.delete(17);

    assert(tree_map@ == map![18u64 => false]);

    let elem17 = tree_map.get(17);
    let elem18 = tree_map.get(18);
    assert(elem17.is_none());
    assert(elem18 == Some(&false));

    test2(tree_map);
}

fn test2(tree_map: TreeMap<u64, bool>) {
    let mut tree_map = tree_map;
    tree_map.insert(25, true);
    tree_map.insert(100, true);
}

// ANCHOR: clone_u32
fn test_clone_u32(tree_map: TreeMap<u64, u32>) {
    let tree_map2 = tree_map.clone();
    assert(tree_map2@ =~= tree_map@);
}
// ANCHOR_END: clone_u32

// ANCHOR: clone_int_wrapper
struct IntWrapper {
    pub int_value: u32,
}

impl Clone for IntWrapper {
    fn clone(&self) -> (s: Self)
        ensures s == *self
    {
        IntWrapper { int_value: self.int_value }
    }
}

fn test_clone_int_wrapper(tree_map: TreeMap<u64, IntWrapper>) {
    let tree_map2 = tree_map.clone();
    assert(tree_map2@ =~= tree_map@);
}
// ANCHOR_END: clone_int_wrapper

// ANCHOR: clone_weird_int
pub struct WeirdInt {
    pub int_value: u32,
    pub other: u32,
}

impl Clone for WeirdInt {
    fn clone(&self) -> (s: Self)
        ensures
            s.int_value == self.int_value,
    {
        WeirdInt { int_value: self.int_value, other: 0 }
    }
}

fn test_clone_weird_int(tree_map: TreeMap<u64, WeirdInt>) {
    let tree_map2 = tree_map.clone();

    // assert(tree_map2@ =~= tree_map@); // this would fail

    assert(tree_map2@.dom() == tree_map@.dom());
    assert(forall |k| tree_map@.dom().contains(k) ==>
        tree_map2@[k].int_value == tree_map@[k].int_value);
}
// ANCHOR_END: clone_weird_int

// ANCHOR: resolved_lemmas
proof fn lemma_node_has_resolved<K: TotalOrdered, V>(node: Node<K, V>, k: K)
    requires
        has_resolved(node),
        node.as_map().dom().contains(k),
    ensures
        has_resolved(node.as_map()[k])
    decreases node,
{
    if node.left.is_some() && node.left.unwrap().as_map().dom().contains(k) {
        lemma_node_has_resolved(*node.left.unwrap(), k);
    }
    if node.right.is_some() && node.right.unwrap().as_map().dom().contains(k) {
        lemma_node_has_resolved(*node.right.unwrap(), k);
    }
}

proof fn lemma_tree_map_has_resolved<K: TotalOrdered, V>(map: TreeMap<K, V>, k: K)
    requires
        has_resolved(map),
        map@.dom().contains(k),
    ensures
        has_resolved(map@[k])
{
    match map.root {
        Some(node) => {
            lemma_node_has_resolved(*node, k);
        }
        None => { }
    }
}
// ANCHOR_END: resolved_lemmas

/*
// ANCHOR: vec_with_mut_refs_broken
fn vec_with_mut_refs(i: usize)
    requires 0 <= i < 3
{
    let mut a = 0;
    let mut b = 0;
    let mut c = 0;

    let mut v = vec![&mut a, &mut b, &mut c];

    *v[i] = 1;

    assert(i == 0 ==> (a, b, c) === (1, 0, 0));
    assert(i == 1 ==> (a, b, c) === (0, 1, 0));
    assert(i == 2 ==> (a, b, c) === (0, 0, 1));
}
// ANCHOR_END: vec_with_mut_refs_broken
*/

// ANCHOR: vec_with_mut_refs
fn vec_with_mut_refs(i: usize)
    requires 0 <= i < 3
{
    let mut a = 0;
    let mut b = 0;
    let mut c = 0;

    let mut v = vec![&mut a, &mut b, &mut c];

    *v[i] = 1;

    assert(has_resolved(v[0]));
    assert(has_resolved(v[1]));
    assert(has_resolved(v[2]));

    assert(i == 0 ==> (a, b, c) === (1, 0, 0));
    assert(i == 1 ==> (a, b, c) === (0, 1, 0));
    assert(i == 2 ==> (a, b, c) === (0, 0, 1));
}
// ANCHOR_END: vec_with_mut_refs

// ANCHOR: tree_map_with_mut_refs
fn tree_map_with_mut_refs(i: u64)
    requires 0 <= i < 3
{
    let mut a = 0;
    let mut b = 0;
    let mut c = 0;

    let mut tree_map = TreeMap::<u64, &mut u64>::new();
    tree_map.insert(0, &mut a);
    tree_map.insert(1, &mut b);
    tree_map.insert(2, &mut c);

    **tree_map.get_mut(i).unwrap() = 1;

    proof {
        lemma_tree_map_has_resolved(tree_map, 0);
        lemma_tree_map_has_resolved(tree_map, 1);
        lemma_tree_map_has_resolved(tree_map, 2);
    }

    assert(i == 0 ==> (a, b, c) === (1, 0, 0));
    assert(i == 1 ==> (a, b, c) === (0, 1, 0));
    assert(i == 2 ==> (a, b, c) === (0, 0, 1));
}
// ANCHOR_END: tree_map_with_mut_refs

}
// ANCHOR_END: all

fn main() { }

