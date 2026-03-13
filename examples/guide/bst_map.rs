// ANCHOR: all
use vstd::prelude::*;

verus!{

// ANCHOR: StructsDef
struct Node<V> {
    key: u64,
    value: V,
    left: Option<Box<Node<V>>>,
    right: Option<Box<Node<V>>>,
}

pub struct TreeMap<V> {
    root: Option<Box<Node<V>>>,
}
// ANCHOR_END: StructsDef

// ANCHOR: AsMapDef
impl<V> Node<V> {
    spec fn optional_as_map(node_opt: Option<Box<Node<V>>>) -> Map<u64, V>
        decreases node_opt,
    {
        match node_opt {
            None => Map::empty(),
            Some(node) => node.as_map(),
        }
    }

    spec fn as_map(self) -> Map<u64, V>
        decreases self,
    {
        Node::<V>::optional_as_map(self.left)
          .union_prefer_right(Node::<V>::optional_as_map(self.right))
          .insert(self.key, self.value)
    }
}

impl<V> TreeMap<V> {
    pub closed spec fn as_map(self) -> Map<u64, V> {
        Node::<V>::optional_as_map(self.root)
    }
}
// ANCHOR_END: AsMapDef

// ANCHOR: ViewDef
impl<V> View for TreeMap<V> {
    type V = Map<u64, V>;

    open spec fn view(&self) -> Map<u64, V> {
        self.as_map()
    }
}
// ANCHOR_END: ViewDef

// ANCHOR: WellFormedDef
impl<V> Node<V> {
    spec fn well_formed(self) -> bool
        decreases self,
    {
        &&& (forall |elem| Node::<V>::optional_as_map(self.left).dom().contains(elem) ==> elem < self.key)
        &&& (forall |elem| Node::<V>::optional_as_map(self.right).dom().contains(elem) ==> elem > self.key)
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

impl<V> TreeMap<V> {
    pub closed spec fn well_formed(self) -> bool {
        match self.root {
            Some(node) => node.well_formed(),
            None => true, // empty tree always well-formed
        }
    }
}
// ANCHOR_END: WellFormedDef

// ANCHOR: new
impl<V> TreeMap<V> {
// ANCHOR: new_signature
    pub fn new() -> (tree_map: Self)
        ensures
            tree_map.well_formed(),
            tree_map@ == Map::<u64, V>::empty(),
// ANCHOR_END: new_signature
    {
        TreeMap::<V> { root: None }
    }
}
// ANCHOR_END: new

// ANCHOR: insert
impl<V> Node<V> {
    fn insert_into_optional(node: &mut Option<Box<Node<V>>>, key: u64, value: V)
        requires
            old(node).is_some() ==> old(node).unwrap().well_formed(),
        ensures
            node.is_some() ==> node.unwrap().well_formed(),
            Node::<V>::optional_as_map(*node) =~= Node::<V>::optional_as_map(*old(node)).insert(key, value),
        decreases *old(node),
    {
        match node.take() {
            None => {
                *node = Some(Box::new(Node::<V> {
                    key: key,
                    value: value,
                    left: None,
                    right: None,
                }));
            }
            Some(mut boxed_node) => {
                (&mut *boxed_node).insert(key, value);
                *node = Some(boxed_node);
            }
        }
    }

    fn insert(&mut self, key: u64, value: V)
        requires
            old(self).well_formed(),
        ensures
            self.well_formed(),
            self.as_map() =~= old(self).as_map().insert(key, value),
        decreases *old(self),
    {
        if key == self.key {
            self.value = value;

            assert(!Node::<V>::optional_as_map(self.left).dom().contains(key));
            assert(!Node::<V>::optional_as_map(self.right).dom().contains(key));
        } else if key < self.key {
            Self::insert_into_optional(&mut self.left, key, value);

            assert(!Node::<V>::optional_as_map(self.right).dom().contains(key));
        } else {
            Self::insert_into_optional(&mut self.right, key, value);

            assert(!Node::<V>::optional_as_map(self.left).dom().contains(key));
        }
    }
}

impl<V> TreeMap<V> {
// ANCHOR: insert_signature
    pub fn insert(&mut self, key: u64, value: V)
        requires
            old(self).well_formed(),
        ensures
            self.well_formed(),
            self@ == old(self)@.insert(key, value),
// ANCHOR_END: insert_signature
    {
        Node::<V>::insert_into_optional(&mut self.root, key, value);
    }
}
// ANCHOR_END: insert

// ANCHOR: delete
impl<V> Node<V> {
    fn delete_from_optional(node: &mut Option<Box<Node<V>>>, key: u64)
        requires
            old(node).is_some() ==> old(node).unwrap().well_formed(),
        ensures
            node.is_some() ==> node.unwrap().well_formed(),
            Node::<V>::optional_as_map(*node) =~= Node::<V>::optional_as_map(*old(node)).remove(key),
        decreases *old(node),
    {
        if let Some(mut boxed_node) = node.take() {

            if key == boxed_node.key {
                assert(!Node::<V>::optional_as_map(boxed_node.left).dom().contains(key));
                assert(!Node::<V>::optional_as_map(boxed_node.right).dom().contains(key));

                if boxed_node.left.is_none() {
                    *node = boxed_node.right;
                } else {
                    if boxed_node.right.is_none() {
                        *node = boxed_node.left;
                    } else {
                        let (popped_key, popped_value) = Node::<V>::delete_rightmost(&mut boxed_node.left);
                        boxed_node.key = popped_key;
                        boxed_node.value = popped_value;
                        *node = Some(boxed_node);
                    }
                }
            } else if key < boxed_node.key {
                assert(!Node::<V>::optional_as_map(boxed_node.right).dom().contains(key));
                Node::<V>::delete_from_optional(&mut boxed_node.left, key);
                *node = Some(boxed_node);
            } else {
                assert(!Node::<V>::optional_as_map(boxed_node.left).dom().contains(key));
                Node::<V>::delete_from_optional(&mut boxed_node.right, key);
                *node = Some(boxed_node);
            }
        }
    }

    fn delete_rightmost(node: &mut Option<Box<Node<V>>>) -> (popped: (u64, V))
        requires
            old(node).is_some(),
            old(node).unwrap().well_formed(),
        ensures
            node.is_some() ==> node.unwrap().well_formed(),
            Node::<V>::optional_as_map(*node) =~= Node::<V>::optional_as_map(*old(node)).remove(popped.0),
            Node::<V>::optional_as_map(*old(node)).dom().contains(popped.0),
            Node::<V>::optional_as_map(*old(node))[popped.0] == popped.1,
            forall |elem| Node::<V>::optional_as_map(*old(node)).dom().contains(elem) ==> popped.0 >= elem,
        decreases *old(node),
    {
        let mut boxed_node = node.take().unwrap();

        if boxed_node.right.is_none() {
            *node = boxed_node.left;
            assert(Node::<V>::optional_as_map(boxed_node.right) =~= Map::empty());
            assert(!Node::<V>::optional_as_map(boxed_node.left).dom().contains(boxed_node.key));
            return (boxed_node.key, boxed_node.value);
        } else {
            let (popped_key, popped_value) = Node::<V>::delete_rightmost(&mut boxed_node.right);
            assert(!Node::<V>::optional_as_map(boxed_node.left).dom().contains(popped_key));
            *node = Some(boxed_node);
            return (popped_key, popped_value);
        }
    }
}

impl<V> TreeMap<V> {
// ANCHOR: delete_signature
    pub fn delete(&mut self, key: u64)
        requires
            old(self).well_formed(),
        ensures
            self.well_formed(),
            self@ == old(self)@.remove(key),
// ANCHOR_END: delete_signature
    {
        Node::<V>::delete_from_optional(&mut self.root, key);
    }
}
// ANCHOR_END: delete

// ANCHOR: get
impl<V> Node<V> {
    fn get_from_optional(node: &Option<Box<Node<V>>>, key: u64) -> Option<&V>
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

    fn get(&self, key: u64) -> Option<&V>
        requires
            self.well_formed(),
        returns
            (if self.as_map().dom().contains(key) { Some(&self.as_map()[key]) } else { None }),
        decreases self,
    {
        if key == self.key {
            Some(&self.value)
        } else if key < self.key {
            proof { assert(!Node::<V>::optional_as_map(self.right).dom().contains(key)); }
            Self::get_from_optional(&self.left, key)
        } else {
            proof { assert(!Node::<V>::optional_as_map(self.left).dom().contains(key)); }
            Self::get_from_optional(&self.right, key)
        }
    }
}

impl<V> TreeMap<V> {
// ANCHOR: get_signature
    pub fn get(&self, key: u64) -> Option<&V>
        requires
            self.well_formed(),
        returns
            (if self@.dom().contains(key) { Some(&self@[key]) } else { None }),
// ANCHOR_END: get_signature
    {
        Node::<V>::get_from_optional(&self.root, key)
    }
}
// ANCHOR_END: get

// ANCHOR: test
fn test() {
    let mut tree_map = TreeMap::<bool>::new();
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
}
// ANCHOR_END: test

// ANCHOR: test_callee
fn test2() {
    let mut tree_map = TreeMap::<bool>::new();
    test_callee(tree_map);
}

fn test_callee(tree_map: TreeMap<bool>)
    requires
        tree_map.well_formed(),
{
    let mut tree_map = tree_map;
    tree_map.insert(25, true);
    tree_map.insert(100, true);
}
// ANCHOR_END: test_callee


}
// ANCHOR_END: all

fn main() { }

