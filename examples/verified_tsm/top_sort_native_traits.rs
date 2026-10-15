#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::imap::*;
use vstd::iset::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::slice::*;
use vstd::{pervasive::*, prelude::*, *};

verus! {

#[verifier::reject_recursive_types(V)]
pub struct DirectedGraph<V> {
    pub edges: ISet<(V, V)>,
}

impl<V> DirectedGraph<V> {
    pub open spec fn dest_set(&self, v: V) -> ISet<V> {
        ISet::new(|w: V| self.edges.contains((v, w)))
    }

    pub open spec fn is_sorted(&self, s: Seq<V>) -> bool {
        forall|i, j: int| 0 <= i <= j < s.len() ==> !self.edges.contains((s.index(i), s.index(j)))
    }

    pub open spec fn is_cycle_i(&self, s: Seq<V>, i: int) -> bool {
        self.edges.contains((s[i], s[i + 1]))
    }

    pub open spec fn is_cycle(&self, s: Seq<V>) -> bool {
        s.len() > 0 && (forall|i: int| 0 <= i < s.len() - 1 ==> self.is_cycle_i(s, i))
            && self.edges.contains((s.last(), s[0]))
    }
}

verified_tokenized_state_machine!{

    #[verifier::reject_recursive_types(V)]
    TopSort<V> {
        fields {
            #[sharding(constant)]
            pub graph: DirectedGraph<V>,

            #[sharding(iset)]
            pub unvisited: ISet<V>,

            #[sharding(persistent_iset)]
            pub visited: ISet<V>,

            #[sharding(variable)]
            pub top_sort: Seq<V>,
        }

        init!{
            initialize(graph: DirectedGraph<V>) {
                init graph = graph;
                init unvisited = ISet::full();
                init visited = ISet::empty();
                init top_sort = Seq::empty();
            }
        }

        transition!{
            push_into_top_sort(v: V) {
                have visited >= (pre.graph.dest_set(v));

                remove unvisited -= set { v };
                add visited (union)= set { v };

                update top_sort = pre.top_sort.push(v);
            }
        }

        property!{
            done(s: ISet<V>) {
                have visited >= (s);
                assert(forall |i| s.contains(i) ==> pre.top_sort.contains(i));
                assert(pre.graph.is_sorted(pre.top_sort));
            }
        }

        #[invariant]
        pub fn un_vis(&self) -> bool {
            self.unvisited == self.visited.complement()
        }

        #[invariant]
        pub fn top_sort_is_sort(&self) -> bool {
            self.graph.is_sorted(self.top_sort)
        }

        #[invariant]
        pub fn visited_closed_under_dep(&self) -> bool {
            forall |v, w| #[trigger] self.graph.edges.contains((v, w)) ==>
                self.visited.contains(v) ==>
                self.visited.contains(w)
        }

        #[invariant]
        pub fn top_sort_matches_visited(&self) -> bool {
            forall |v| #[trigger] self.visited.contains(v) <==>
                self.top_sort.contains(v)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, graph: DirectedGraph<V>) { }

        #[inductive(push_into_top_sort)]
        fn push_into_top_sort_inductive(pre: Self, post: Self, v: V) {
            assert_isets_equal!(post.unvisited, post.visited.complement());

            assert forall |a| #[trigger] post.visited.contains(a) implies
                post.top_sort.contains(a)
            by {
                if a == v {
                    assert(post.top_sort.last() == a);
                    assert(post.top_sort.contains(a));
                } else {
                    assert(pre.visited.contains(a));
                    assert(pre.top_sort.contains(a));
                    let i = choose |i| 0 <= i < pre.top_sort.len() && pre.top_sort.index(i) == a;
                    assert(post.top_sort.index(i) == a);
                    assert(post.top_sort.contains(a));
                }
            }

            assert forall |v| #[trigger] post.top_sort.contains(v) implies
                post.visited.contains(v)
            by {
            }
        }

    }
}

fn assert_send_sync<T: Send + Sync>() {
}

fn main() {
    assert_send_sync::<TopSort::Instance<usize>>();
    assert_send_sync::<TopSort::unvisited<usize>>();
    assert_send_sync::<TopSort::visited<usize>>();
    assert_send_sync::<TopSort::unvisited_set<usize>>();
    assert_send_sync::<TopSort::visited_set<usize>>();
    assert_send_sync::<TopSort::top_sort<usize>>();
}

} // verus!
