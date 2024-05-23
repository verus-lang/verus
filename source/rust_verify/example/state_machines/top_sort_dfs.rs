#![allow(unused_imports)]
use state_machines_macros::tokenized_state_machine;
use vstd::map::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::*;
use vstd::slice::*;
use vstd::{pervasive::*, prelude::*, *};

verus! {

#[verifier::reject_recursive_types(V)]
pub struct DirectedGraph<V> {
    pub edges: Set<(V, V)>,
}

impl<V> DirectedGraph<V> {
    pub open spec fn dest_set(&self, v: V) -> Set<V> {
        Set::new(|w: V| self.edges.contains((v, w)))
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

tokenized_state_machine!{
    #[verifier::reject_recursive_types(V)]
    TopSort<V> {
        fields {
            #[sharding(constant)]
            pub graph: DirectedGraph<V>,

            #[sharding(set)]
            pub unvisited: Set<V>,

            #[sharding(persistent_set)]
            pub visited: Set<V>,

            #[sharding(variable)]
            pub top_sort: Seq<V>,
        }

        init!{
            initialize(graph: DirectedGraph<V>) {
                init graph = graph;
                init unvisited = Set::full();
                init visited = Set::empty();
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
            done(s: Set<V>) {
                have visited >= (s);
                assert(forall |i| s.contains(i) ==> pre.top_sort.contains(i));
                assert(pre.graph.is_sorted(pre.top_sort));
            }
        }

        #[invariant]
        pub fn un_vis(&self) -> bool {
            self.unvisited === self.visited.complement()
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
            assert_sets_equal!(post.unvisited, post.visited.complement());

            assert forall |a| #[trigger] post.visited.contains(a) implies
                post.top_sort.contains(a)
            by {
                if a === v {
                    assert(post.top_sort.last() === a);
                    assert(post.top_sort.contains(a));
                } else {
                    assert(pre.visited.contains(a));
                    assert(pre.top_sort.contains(a));
                    let i = choose |i| 0 <= i < pre.top_sort.len() && pre.top_sort.index(i) === a;
                    assert(post.top_sort.index(i) === a);
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

struct ConcreteDirectedGraph {
    edges: Vec<Vec<usize>>,
}

impl ConcreteDirectedGraph {
    spec fn well_formed(&self) -> bool {
        forall|i, j|
            0 <= i < self.edges@.len() && 0 <= j < self.edges@.index(i)@.len() ==> 0 <= (
            #[trigger] self.edges@.index(i)@.index(j)) < self.edges@.len()
    }

    spec fn view(&self) -> DirectedGraph<usize> {
        DirectedGraph {
            edges: Set::<(usize, usize)>::new(
                |p: (usize, usize)|
                    0 <= (p.0 as int) < (self.edges@.len() as int) && self.edges@.index(
                        p.0 as int,
                    )@.contains(p.1),
            ),
        }
    }
}

enum NodeToken {
    Unvisited(TopSort::unvisited<usize>),
    InProgress,
    Visited(TopSort::visited<usize>),
}

struct NodeState {
    visited: bool,
    in_stack: bool,
    token: Tracked<NodeToken>,
}

impl NodeState {
    spec fn well_formed(&self, i: int, inst: TopSort::Instance<usize>) -> bool {
        match self.token@ {
            NodeToken::Unvisited(token) => {
                &&& !self.visited
                &&& !self.in_stack
                &&& token@.instance === inst
                &&& token@.key as int === i
            },
            NodeToken::InProgress => {
                &&& self.visited
                &&& self.in_stack
            },
            NodeToken::Visited(token) => {
                &&& self.visited
                &&& !self.in_stack
                &&& token@.instance === inst
                &&& token@.key as int === i
            },
        }
    }
}

struct DfsState {
    top_sort: Vec<usize>,
    cur_stack: Vec<usize>,
    cycle: Vec<usize>,
    node_states: Vec<NodeState>,
    top_sort_token: Tracked<TopSort::top_sort<usize>>,
    instance: Tracked<TopSort::Instance<usize>>,
}

spec fn valid_stack_i(cur_stack: Seq<usize>, graph: DirectedGraph<usize>, i: int) -> bool {
    graph.edges.contains((cur_stack[i], cur_stack[i + 1]))
}

spec fn valid_stack(cur_stack: Seq<usize>, graph: DirectedGraph<usize>) -> bool {
    forall|i: int| 0 <= i < cur_stack.len() as int - 1 ==> valid_stack_i(cur_stack, graph, i)
}

impl DfsState {
    spec fn well_formed(&self, graph: &ConcreteDirectedGraph) -> bool {
        &&& graph.well_formed()
        &&& self.node_states@.len() == graph.edges@.len()
        &&& forall|i|
            0 <= i < self.node_states@.len() ==> self.node_states@[i].well_formed(i, self.instance@)
        &&& self.top_sort_token@@.instance === self.instance@
        &&& self.top_sort_token@@.value === self.top_sort@
        &&& self.instance@.graph() === graph@
        &&& valid_stack(self.cur_stack@, graph@)
        &&& forall|i: usize|
            0 <= i < self.node_states@.len() ==> (self.node_states@[i as int].in_stack
                <==> self.cur_stack@.contains(i))
    }
}

spec fn is_complete_top_sort(top_sort: &Vec<usize>, graph: &ConcreteDirectedGraph) -> bool {
    graph@.is_sorted(top_sort@) && forall|i: usize|
        0 <= i < graph.edges@.len() ==> top_sort@.contains(i)
}

fn vec_find(v: &Vec<usize>, needle: usize) -> (idx: usize)
    requires
        v@.contains(needle),
    ensures
        0 <= idx < v@.len() && v@[idx as int] == needle,
{
    let mut idx = 0;
    loop
        invariant
            v@.contains(needle),
            0 <= idx < v@.len(),
            forall|j| 0 <= j < idx ==> v@[j] != needle,
    {
        if v[idx] == needle {
            return idx;
        }
        assert(idx + 1 < v.len());
        idx = idx + 1;
    }
}

fn find_cycle(graph: &ConcreteDirectedGraph, dfs_state: &mut DfsState, v: usize)
    requires
        0 <= v && v < graph.edges@.len(),
        old(dfs_state).well_formed(graph),
        old(dfs_state).cur_stack@.len() >= 1 ==> graph@.edges.contains(
            (old(dfs_state).cur_stack@.last(), v),
        ),
        old(dfs_state).node_states@.index(v as int).in_stack,
    ensures
        graph@.is_cycle(dfs_state.cycle@),
        equal(dfs_state.instance, old(dfs_state).instance),
{
    let j = vec_find(&dfs_state.cur_stack, v);
    let len = dfs_state.cur_stack.len();
    let tmp1 = dfs_state.cur_stack.as_slice();
    let tmp2 = slice_subrange(tmp1, j, len);
    let cycle = slice_to_vec(tmp2);
    dfs_state.cycle = cycle;
    assert(tmp1@.len() == dfs_state.cur_stack.len());
    assert(tmp2@.len() + j == len);
    assert(tmp2@ == cycle@);
    assert(cycle.len() + j == len);
    assert(j + dfs_state.cycle@.len() == len);
    assert(graph@.is_cycle(dfs_state.cycle@)) by {
        assert forall|i: int| 0 <= i < dfs_state.cycle@.len() - 1 implies graph@.is_cycle_i(
            dfs_state.cycle@,
            i,
        ) by {
            assert(valid_stack_i(dfs_state.cur_stack@, graph@, i + j));  // trigger
        }
    };
}

fn visit(graph: &ConcreteDirectedGraph, dfs_state: &mut DfsState, v: usize) -> (res: (
    bool,
    Tracked<Option<TopSort::visited<usize>>>,
))
    requires
        0 <= v && v < graph.edges@.len(),
        old(dfs_state).well_formed(graph),
        old(dfs_state).cur_stack@.len() >= 1 ==> graph@.edges.contains(
            (old(dfs_state).cur_stack@.last(), v),
        ),
    ensures
        res.0 ==> dfs_state.well_formed(graph),
        res.0 ==> equal(dfs_state.cur_stack@, old(dfs_state).cur_stack@),
        res.0 ==> res.1@.is_Some() && res.1@.get_Some_0()@.instance == dfs_state.instance@
            && res.1@.get_Some_0()@.key == v,
        !res.0 ==> graph@.is_cycle(dfs_state.cycle@),
        equal(dfs_state.instance, old(dfs_state).instance),
{
    let node_state = &dfs_state.node_states[v as usize];
    if node_state.in_stack {
        find_cycle(graph, dfs_state, v);
        return (false, Tracked(None));
    }
    if node_state.visited {
        let tracked tok = match node_state.token.borrow() {
            NodeToken::Visited(tok) => tok.clone(),
            _ => proof_from_false(),
        };
        return (true, Tracked(Some(tok)));
    }
    let mut node_state_tmp = NodeState {
        in_stack: true,
        visited: true,
        token: Tracked(NodeToken::InProgress),
    };
    dfs_state.node_states.set_and_swap(v as usize, &mut node_state_tmp);
    let tracked unvisited = match node_state_tmp.token.get() {
        NodeToken::Unvisited(unvisited) => unvisited,
        _ => proof_from_false(),
    };
    dfs_state.cur_stack.push(v);
    assert(dfs_state.well_formed(graph)) by {
        assert(forall|i: int|
            0 <= i && i < dfs_state.cur_stack@.len() as int - 2 ==> valid_stack_i(
                old(dfs_state).cur_stack@,
                graph@,
                i,
            ) ==> #[trigger] valid_stack_i(dfs_state.cur_stack@, graph@, i));
        assert(valid_stack(dfs_state.cur_stack@, graph@));
        assert forall|i: usize|
            0 <= i && i < dfs_state.node_states@.len() implies dfs_state.node_states@.index(
            i as int,
        ).in_stack == dfs_state.cur_stack@.contains(i) by {
            if i == v {
                assert(dfs_state.cur_stack@.last() == i);
                assert(dfs_state.cur_stack@.contains(i));
            } else {
                if old(dfs_state).cur_stack@.contains(i) {
                    let j = old(dfs_state).cur_stack@.index_of(i);
                    assert(dfs_state.cur_stack@.index(j) == i);
                }
                if dfs_state.cur_stack@.contains(i) {
                    let j = old(dfs_state).cur_stack@.index_of(i);
                    assert(old(dfs_state).cur_stack@.index(j) == i);
                }
                assert(dfs_state.cur_stack@.contains(i) == old(dfs_state).cur_stack@.contains(i));
            }
        }
    }
    let ghost extended_cur_stack = dfs_state.cur_stack;
    let tracked mut map_visited_deps: Map<usize, TopSort::visited<usize>> = Map::tracked_empty();
    let mut idx: usize = 0;
    while idx < graph.edges[v as usize].len()
        invariant
            equal(dfs_state.instance, old(dfs_state).instance),
            dfs_state.cur_stack@.len() > 0,
            dfs_state.cur_stack@.last() == v,
            0 <= v && v < graph.edges@.len(),
            0 <= idx && idx <= graph.edges@.index(v as int)@.len(),
            dfs_state.well_formed(graph),
            equal(dfs_state.cur_stack@, extended_cur_stack@),
            forall|idx0: int|
                0 <= idx0 && idx0 < idx ==> {
                    let w = #[trigger] graph.edges@.index(v as int)@.index(idx0);
                    map_visited_deps.dom().contains(w) && map_visited_deps.index(w)@.instance
                        == dfs_state.instance@ && map_visited_deps.index(w)@.key == w
                },
    {
        let w = graph.edges[v as usize][idx];
        assert((v as usize) as int == v as int);
        assert(graph.edges@.index(v as int)@.index(idx as int) == w);
        assert(graph.edges@.index(v as int)@.contains(w));
        assert(graph@.edges.contains((v, w)));
        let (b, Tracked(opt_visited)) = visit(graph, dfs_state, w);
        if !b {
            return (false, Tracked(None));
        }
        let ghost old_map_visited_deps = map_visited_deps;
        let ghost old_idx = idx;
        proof {
            let tracked visited = opt_visited.tracked_unwrap();
            map_visited_deps.tracked_insert(w, visited);
        }
        idx = idx + 1;
        assert forall|idx0: int| 0 <= idx0 && idx0 < idx implies ({
            let w = #[trigger] graph.edges@.index(v as int)@.index(idx0);
            map_visited_deps.dom().contains(w) && map_visited_deps.index(w)@.instance
                == dfs_state.instance@ && map_visited_deps.index(w)@.key == w
        }) by {
            assume(false);
        }
    }
    dfs_state.cur_stack.pop();
    assert(equal(unvisited@.instance, dfs_state.instance@));
    let tracked visited = dfs_state.instance.borrow().push_into_top_sort(
        v,
        unvisited,
        &map_visited_deps,
        dfs_state.top_sort_token.borrow_mut(),
    );
    dfs_state.top_sort.push(v);
    let mut node_state_tmp = NodeState {
        in_stack: false,  // TODO don't need to write this field again
        visited: true,
        token: Tracked(NodeToken::Visited(visited.clone())),
    };
    dfs_state.node_states.set_and_swap(v as usize, &mut node_state_tmp);
    proof {
        assert_seqs_equal!(
            dfs_state.cur_stack@,
            old(dfs_state).cur_stack@);
    }
    assert(dfs_state.well_formed(graph)) by {
        assert(valid_stack(dfs_state.cur_stack@, graph@));
        assume(forall|i: usize|
            0 <= i && i < dfs_state.node_states@.len() ==> (dfs_state.node_states@.index(
                i as int,
            ).in_stack == dfs_state.cur_stack@.contains(i)));
    };
    (true, Tracked(Some(visited)))
}

fn init_node_states(
    n: usize,
    Tracked(instance): Tracked<TopSort::Instance<usize>>,
    Tracked(unv): Tracked<Map<usize, TopSort::unvisited<usize>>>,
) -> (node_states: Vec<NodeState>)
    requires
        forall|j: usize| 0 <= j && j < n ==> unv.dom().contains(j),
        forall|j: usize|
            0 <= j && j < n ==> unv.index(j)@.instance == instance && unv.index(j)@.key == j,
    ensures
        node_states@.len() == n as int,
        forall|j: int|
            0 <= j && j < node_states@.len() ==> node_states@.index(j).well_formed(j, instance),
        forall|j: int| 0 <= j && j < node_states@.len() ==> !node_states@.index(j).in_stack,
{
    let mut node_states = Vec::<NodeState>::new();
    let mut i: usize = 0;
    let tracked mut unv = unv;
    while i < n
        invariant
            0 <= i && i <= n,
            node_states@.len() == i as int,
            forall|j: int| 0 <= j && j < i ==> node_states@.index(j).well_formed(j, instance),
            forall|j: int| 0 <= j && j < i ==> !node_states@.index(j).in_stack,
            forall|j: usize| i <= j && j < n ==> #[trigger] unv.dom().contains(j),
            forall|j: usize|
                i <= j && j < n ==> unv.index(j)@.instance == instance && unv.index(j)@.key == j,
    {
        assert(unv.dom().contains(i));
        let tracked unv1 = unv.tracked_remove(i);
        node_states.push(
            NodeState {
                visited: false,
                in_stack: false,
                token: Tracked(NodeToken::Unvisited(unv1)),
            },
        );
        i = i + 1;
        /*let ghost i_spec = i;
        assert_forall_by(|j: int| {
            requires(0 <= j && j < i);
            ensures(node_states@.index(j).well_formed(j, instance));

            if j + 1 < i_spec {
                assert(old_node_states@.index(j).well_formed(j, instance));
            } else {
                assert(node_states@.index(j).well_formed(j, instance));
            }
        });*/
    }
    node_states
}

enum TopSortResult {
    TopSort(Vec<usize>),
    Cycle(Vec<usize>),
}

fn compute_top_sort(graph: &ConcreteDirectedGraph) -> (tsr: TopSortResult)
    requires
        graph.well_formed(),
    ensures
        (match tsr {
            TopSortResult::TopSort(top_sort) => is_complete_top_sort(&top_sort, graph),
            TopSortResult::Cycle(cycle) => graph@.is_cycle(cycle@),
        }),
{
    let tracked (Tracked(instance), Tracked(unv), _, Tracked(top_sort_token)) = TopSort::Instance::<
        usize,
    >::initialize(graph@);
    let mut dfs_state = DfsState {
        top_sort: Vec::new(),
        cur_stack: Vec::new(),
        cycle: Vec::new(),
        node_states: init_node_states(
            graph.edges.len() as usize,
            Tracked(instance.clone()),
            Tracked(unv),
        ),
        top_sort_token: Tracked(top_sort_token),
        instance: Tracked(instance),
    };
    let tracked mut map_visited_deps: Map<usize, TopSort::visited<usize>> = Map::tracked_empty();
    assert(dfs_state.well_formed(graph)) by {
        assert(forall|i: usize|
            0 <= i && i < dfs_state.node_states@.len() ==> (dfs_state.node_states@.index(
                i as int,
            ).in_stack == dfs_state.cur_stack@.contains(i)));
    }
    let mut v: usize = 0;
    while v < graph.edges.len() as usize
        invariant
            graph.well_formed(),
            dfs_state.well_formed(graph),
            forall|w| 0 <= w && (w as int) < (v as int) ==> map_visited_deps.dom().contains(w),
            forall|w|
                0 <= w && (w as int) < (v as int) ==> map_visited_deps.index(w)@.instance
                    == dfs_state.instance@ && map_visited_deps.index(w)@.key == w,
            dfs_state.cur_stack@.len() == 0,
    {
        let (b, Tracked(opt_visited)) = visit(graph, &mut dfs_state, v);
        if !b {
            return TopSortResult::Cycle(dfs_state.cycle);
        }
        proof {
            map_visited_deps.tracked_insert(v, opt_visited.tracked_unwrap());
        }
        v = v + 1;
    }
    let DfsState { top_sort, top_sort_token: Tracked(top_sort_token), .. } = dfs_state;
    proof {
        let ghost s = Set::new(|i: usize| 0 <= i && i < graph.edges@.len());
        dfs_state.instance.borrow().done(s, &map_visited_deps, &top_sort_token);
        assert forall|i: usize| 0 <= i && i < graph.edges@.len() implies top_sort@.contains(i) by {
            assert(s.contains(i));
        }
        assert(is_complete_top_sort(&top_sort, graph));
    }
    TopSortResult::TopSort(top_sort)
}

fn main() {
}

} // verus!
