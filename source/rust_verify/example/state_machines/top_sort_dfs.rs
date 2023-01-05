#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::set::*;
use pervasive::vec::*;
use pervasive::slice::*;
use pervasive::option::*;
use pervasive::seq::*;
use pervasive::map::*;
use pervasive::modes::*;
use state_machines_macros::tokenized_state_machine;

use option::Option::Some;
use option::Option::None;

verus!{

pub struct DirectedGraph<#[verifier(maybe_negative)] V> {
    pub edges: Set<(V, V)>,
}

impl<V> DirectedGraph<V> {
    pub open spec fn dest_set(&self, v: V) -> Set<V> {
        Set::new(|w: V| self.edges.contains((v, w)))
    }

    pub open spec fn is_sorted(&self, s: Seq<V>) -> bool {
        forall |i, j: int| 0 <= i <= j < s.len() ==>
            !self.edges.contains((s.index(i), s.index(j)))
    }

    pub open spec fn is_cycle_i(&self, s: Seq<V>, i: int) -> bool {
        self.edges.contains((s[i], s[i + 1]))
    }

    pub open spec fn is_cycle(&self, s: Seq<V>) -> bool {
        s.len() > 0
        && (forall |i: int| 0 <= i < s.len() - 1 ==> self.is_cycle_i(s, i))
        && self.edges.contains((s.last(), s[0]))
    }
}

tokenized_state_machine!{
    TopSort<#[verifier(maybe_negative)] V> {
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
        forall |i, j| 0 <= i < self.edges@.len() && 0 <= j < self.edges@.index(i)@.len()
            ==> 0 <= (#[trigger] self.edges@.index(i)@.index(j)) < self.edges@.len()
    }

    spec fn view(&self) -> DirectedGraph<usize> {
        DirectedGraph {
            edges: Set::<(usize, usize)>::new(|p: (usize, usize)|
                0 <= (p.0 as int) < (self.edges@.len() as int)
                  && self.edges@.index(p.0 as int)@.contains(p.1)
            )
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

    #[proof] token: NodeToken,
}

impl NodeState {
    spec fn well_formed(&self, i: int, inst: TopSort::Instance<usize>) -> bool {
        match self.token {
            NodeToken::Unvisited(token) => {
                &&& !self.visited
                &&& !self.in_stack
                &&& token@.instance === inst
                &&& token@.key as int === i
            }
            NodeToken::InProgress => {
                &&& self.visited
                &&& self.in_stack
            }
            NodeToken::Visited(token) => {
                &&& self.visited
                &&& !self.in_stack
                &&& token@.instance === inst
                &&& token@.key as int === i
            }
        }
    }
}

struct DfsState {
    top_sort: Vec<usize>,
    cur_stack: Vec<usize>,
    cycle: Vec<usize>,

    node_states: Vec<NodeState>,

    #[proof] top_sort_token: TopSort::top_sort<usize>,
    #[proof] instance: TopSort::Instance<usize>,
}

spec fn valid_stack_i(cur_stack: Seq<usize>, graph: DirectedGraph<usize>, i: int) -> bool {
    graph.edges.contains((cur_stack[i], cur_stack[i+1]))
}

spec fn valid_stack(cur_stack: Seq<usize>, graph: DirectedGraph<usize>) -> bool {
    forall |i: int| 0 <= i < cur_stack.len() as int - 1 ==>
        valid_stack_i(cur_stack, graph, i)
}

impl DfsState {
    spec fn well_formed(&self, graph: &ConcreteDirectedGraph) -> bool {
        &&& graph.well_formed()
        &&& self.node_states@.len() == graph.edges@.len()
        &&& (forall |i| 0 <= i < self.node_states@.len() ==>
            self.node_states@[i].well_formed(i, self.instance))
        &&& self.top_sort_token@
            === TopSort::token![ self.instance => top_sort => self.top_sort.view() ]
        &&& self.instance.graph() === graph@
        &&& valid_stack(self.cur_stack@, graph@)
        &&& (forall |i: usize| 0 <= i < self.node_states@.len() ==>
           (self.node_states@[i as int].in_stack <==> self.cur_stack@.contains(i)))
    }
}

spec fn is_complete_top_sort(
    top_sort: &Vec<usize>,
    graph: &ConcreteDirectedGraph) -> bool
{
    graph@.is_sorted(top_sort@)
    && forall |i: usize| 0 <= i < graph.edges@.len() ==> top_sort@.contains(i)
}

fn vec_find(
    v: &Vec<usize>,
    needle: usize) -> (idx: usize)
        requires v@.contains(needle),
        ensures 0 <= idx < v@.len() && v@[idx] == needle,
{
    let mut idx = 0;

    loop
        invariant
            v@.contains(needle),
            0 <= idx < v@.len(),
            forall |j| 0 <= j < idx ==> v@[j] != needle,
    {
        if *v.index(idx) == needle {
            return idx;
        }
        assert(idx + 1 < v.spec_len());
        idx = idx + 1;
    }
}

fn find_cycle(
    graph: &ConcreteDirectedGraph,
    dfs_state: &mut DfsState,
    v: usize,
)
    requires
        0 <= v && v < graph.edges.view().len(),
        old(dfs_state).well_formed(graph),
        old(dfs_state).cur_stack.view().len() >= 1 ==>
            graph.view().edges.contains((old(dfs_state).cur_stack.view().last(), v)),
        old(dfs_state).node_states@.index(v as int).in_stack,
    ensures
        graph@.is_cycle(dfs_state.cycle@),
        equal(dfs_state.instance, old(dfs_state).instance),
{
    let j = vec_find(&dfs_state.cur_stack, v);
    let len = dfs_state.cur_stack.len();

    let cycle = slice_to_vec(slice_subrange(dfs_state.cur_stack.as_slice(), j, len));

    dfs_state.cycle = cycle;

    assert(graph@.is_cycle(dfs_state.cycle@)) by {
        assert forall |i: int| 0 <= i < dfs_state.cycle@.len() - 1 implies graph@.is_cycle_i(dfs_state.cycle@, i)
        by {
            assert(valid_stack_i(dfs_state.cur_stack@, graph@, i + j)); // trigger
        }
    };
}

}

fn visit(
    graph: &ConcreteDirectedGraph,
    dfs_state: &mut DfsState,
    v: usize,
) -> (bool, Trk<Option<TopSort::visited<usize>>>)
{
    requires([
        0 <= v && v < graph.edges.view().len(),
        old(dfs_state).well_formed(graph),
        old(dfs_state).cur_stack.view().len() >= 1 >>=
            graph.view().edges.contains((old(dfs_state).cur_stack.view().last(), v)),
    ]);
    ensures(|res: (bool, Trk<Option<TopSort::visited<usize>>>)| [
        res.0 >>= dfs_state.well_formed(graph),
        res.0 >>= equal(dfs_state.cur_stack.view(), old(dfs_state).cur_stack.view()),
        res.0 >>= res.1.0.is_Some() &&
            equal(res.1.0.get_Some_0().view(),
                TopSort::token![ dfs_state.instance => visited => v ]
            ),
        !res.0 >>= graph.view().is_cycle(dfs_state.cycle.view()),
        equal(dfs_state.instance, old(dfs_state).instance),
    ]);

    if dfs_state.node_states.index(v as usize).in_stack {
        find_cycle(graph, dfs_state, v);
        return (false, Trk(None));
    }

    if dfs_state.node_states.index(v as usize).visited {
        #[proof] let tok = match &dfs_state.node_states.index(v as usize).token {
            NodeToken::Visited(tok) => tok.clone(),
            _ => proof_from_false(),
        };
        return (true, Trk(Some(tok)));
    }

    let mut node_state_tmp = NodeState {
        in_stack: true,
        visited: true,
        token: NodeToken::InProgress,
    };
    dfs_state.node_states.swap(v as usize, &mut node_state_tmp);
    #[proof] let unvisited = match node_state_tmp.token {
        NodeToken::Unvisited(unvisited) => unvisited,
        _ => proof_from_false(),
    };

    dfs_state.cur_stack.push(v);

    #[spec] let v_spec = v;
    assert_by(dfs_state.well_formed(graph), {
        assert(forall(|i: int| 0 <= i && i < dfs_state.cur_stack.view().len() as int - 2 >>=
            valid_stack_i(old(dfs_state).cur_stack.view(), graph.view(), i) >>=
            #[trigger] valid_stack_i(dfs_state.cur_stack.view(), graph.view(), i)));
        assert(valid_stack(dfs_state.cur_stack.view(), graph.view()));

        #[spec] let v = v_spec;
        assert_forall_by(|i: usize| {
            requires(0 <= i && i < dfs_state.node_states.view().len());
            ensures(dfs_state.node_states.view().index(i as int).in_stack == dfs_state.cur_stack.view().contains(i));

            if i == v {
                assert(dfs_state.cur_stack.view().last() == i);
                assert(dfs_state.cur_stack.view().contains(i));
            } else {
                if old(dfs_state).cur_stack.view().contains(i) {
                    #[spec] let j = old(dfs_state).cur_stack.view().index_of(i);
                    assert(dfs_state.cur_stack.view().index(j) == i);
                }
                if dfs_state.cur_stack.view().contains(i) {
                    #[spec] let j = old(dfs_state).cur_stack.view().index_of(i);
                    assert(old(dfs_state).cur_stack.view().index(j) == i);
                }
                assert(dfs_state.cur_stack.view().contains(i)
                    == old(dfs_state).cur_stack.view().contains(i));
            }
        });

    });

    #[spec] let extended_cur_stack = dfs_state.cur_stack;
    #[proof] let mut map_visited_deps: Map<usize, TopSort::visited<usize>> = Map::tracked_empty();

    let mut idx: usize = 0;
    while idx < graph.edges.index(v as usize).len()
    {
        invariant([
            equal(dfs_state.instance, old(dfs_state).instance),
            dfs_state.cur_stack.view().len() > 0,
            dfs_state.cur_stack.view().last() == v,
            0 <= v && v < graph.edges.view().len(),
            0 <= idx && idx <= graph.edges.view().index(v as usize).view().len(),
            dfs_state.well_formed(graph),
            equal(dfs_state.cur_stack.view(), extended_cur_stack.view()),
            forall(|idx0: int| 0 <= idx0 && idx0 < idx >>= {
                #[spec] let w = #[trigger] graph.edges.view().index(v as int).view().index(idx0);
                map_visited_deps.dom().contains(w)
                    && equal(map_visited_deps.index(w).view(), TopSort::token![ dfs_state.instance => visited => w ])
            }),
        ]);

        let w = *graph.edges.index(v as usize).index(idx);

        assert((v as usize) as int == v as int);
        assert(graph.edges.view().index(v).view().index(idx as int) == w);
        assert(graph.edges.view().index(v).view().contains(w));
        assert(graph.view().edges.contains((v, w)));

        let (b, Trk(opt_visited)) = visit(graph, dfs_state, w);
        if !b {
            return (false, Trk(None));
        }

        #[spec] let old_map_visited_deps = map_visited_deps;
        #[spec] let old_idx = idx;

        #[proof] let visited = opt_visited.tracked_unwrap();
        map_visited_deps.tracked_insert(w, visited);

        idx = idx + 1;

        assert_forall_by(|idx0: int| {
            requires(0 <= idx0 && idx0 < idx);
            ensures({
                  #[spec] let w = #[trigger] graph.edges.view().index(v as int).view().index(idx0);
                  map_visited_deps.dom().contains(w)
                      && equal(map_visited_deps.index(w).view(), TopSort::token![ dfs_state.instance => visited => w ])
              });
            assume(false);
       });
    }

    dfs_state.cur_stack.pop();

    assert(equal(unvisited.view().instance, dfs_state.instance));
    #[proof] let visited = dfs_state.instance.push_into_top_sort(v,
        unvisited,
        &map_visited_deps,
        &mut dfs_state.top_sort_token,
    );
    dfs_state.top_sort.push(v);

    let mut node_state_tmp = NodeState {
        in_stack: false, // TODO don't need to write this field again
        visited: true,
        token: NodeToken::Visited(visited.clone()),
    };
    dfs_state.node_states.swap(v as usize, &mut node_state_tmp);

    assert_seqs_equal!(
        dfs_state.cur_stack.view(),
        old(dfs_state).cur_stack.view());

    assert_by(dfs_state.well_formed(graph), {
        assert(valid_stack(dfs_state.cur_stack.view(), graph.view()));
        assume(forall(|i: usize| 0 <= i && i < dfs_state.node_states.view().len() >>=
           (dfs_state.node_states.view().index(i as int).in_stack == dfs_state.cur_stack.view().contains(i))));

    });

    (true, Trk(Some(visited)))
}

fn init_node_states(
    n: usize,
    #[proof] instance: TopSort::Instance<usize>,
    #[proof] unv: Map<usize, TopSort::unvisited<usize>>,
) -> Vec<NodeState> {
    requires([
        forall(|j: usize| 0 <= j && j < n >>=
            unv.dom().contains(j)),
        forall(|j: usize| 0 <= j && j < n >>=
            equal(unv.index(j).view(), TopSort::token![
                instance => unvisited => j
            ])),
    ]);
    ensures(|node_states: Vec<NodeState>| [
        node_states.view().len() == n as int,
        forall(|j: int| 0 <= j && j < node_states.view().len() >>=
            node_states.view().index(j).well_formed(j, instance)),
        forall(|j: int| 0 <= j && j < node_states.view().len() >>=
            !node_states.view().index(j).in_stack)
    ]);

    let mut node_states = Vec::<NodeState>::new();
    let mut i: usize = 0;

    #[proof] let mut unv = unv;

    while i < n {
        invariant([
            0 <= i && i <= n,
            node_states.view().len() == i as int,
            forall(|j: int| 0 <= j && j < i >>=
                node_states.view().index(j).well_formed(j, instance)),
            forall(|j: int| 0 <= j && j < i >>=
                !node_states.view().index(j).in_stack),
            forall(|j: usize| i <= j && j < n >>=
                #[trigger] unv.dom().contains(j)),
            forall(|j: usize| i <= j && j < n >>=
                equal(unv.index(j).view(), TopSort::token![
                    instance => unvisited => j
                ])),
        ]);

        assert(unv.dom().contains(i));
        #[proof] let unv1 = unv.tracked_remove(i);
        //#[spec] let old_node_states = node_states;

        node_states.push(NodeState {
            visited: false,
            in_stack: false,
            token: NodeToken::Unvisited(unv1),
        });

        i = i + 1;

        /*#[spec] let i_spec = i;
        assert_forall_by(|j: int| {
            requires(0 <= j && j < i);
            ensures(node_states.view().index(j).well_formed(j, instance));

            if j + 1 < i_spec {
                assert(old_node_states.view().index(j).well_formed(j, instance));
            } else {
                assert(node_states.view().index(j).well_formed(j, instance));
            }
        });*/

    }

    node_states
}

enum TopSortResult {
    TopSort(Vec<usize>),
    Cycle(Vec<usize>)
}

fn compute_top_sort(graph: &ConcreteDirectedGraph) -> TopSortResult
{
    requires(graph.well_formed());
    ensures(|tsr: TopSortResult| {
        match tsr {
            TopSortResult::TopSort(top_sort) => is_complete_top_sort(&top_sort, graph),
            TopSortResult::Cycle(cycle) => graph.view().is_cycle(cycle.view()),
        }
    });

    #[proof] let (Trk(instance), Trk(unv), Trk(_), Trk(top_sort_token))
        = TopSort::Instance::<usize>::initialize(graph.view());

    let mut dfs_state = DfsState {
        top_sort: Vec::new(),
        cur_stack: Vec::new(),
        cycle: Vec::new(),
        node_states: init_node_states(graph.edges.len() as usize, instance.clone(), unv),
        top_sort_token,
        instance,
    };

    #[proof] let mut map_visited_deps: Map<usize, TopSort::visited<usize>> = Map::tracked_empty();

    assert_by(dfs_state.well_formed(graph), {
        assert(forall(|i: usize| 0 <= i && i < dfs_state.node_states.view().len() >>=
           (dfs_state.node_states.view().index(i as int).in_stack == dfs_state.cur_stack.view().contains(i))));
    });

    let mut v: usize = 0;
    while v < graph.edges.len() as usize
    {
        invariant([
            graph.well_formed(),
            dfs_state.well_formed(graph),
            forall(|w| 0 <= w && (w as int) < (v as int) >>=
                map_visited_deps.dom().contains(w)
                &&
                equal(map_visited_deps.index(w).view(), TopSort::token![
                    dfs_state.instance => visited => w
                ])
            ),
            dfs_state.cur_stack.view().len() == 0,
        ]);

        let (b, Trk(opt_visited)) = visit(graph, &mut dfs_state, v);

        if !b {
            return TopSortResult::Cycle(dfs_state.cycle);
        }

        map_visited_deps.tracked_insert(v, opt_visited.tracked_unwrap());

        v = v + 1;
    }

    let DfsState { top_sort, top_sort_token, .. } = dfs_state;

    #[spec] let s = Set::new(|i: usize| 0 <= i && i < graph.edges.view().len());
    dfs_state.instance.done(
        s,
        &map_visited_deps,
        &top_sort_token);

    assert_forall_by(|i: usize| {
        requires(0 <= i && i < graph.edges.view().len());
        ensures(top_sort.view().contains(i));
        assert(s.contains(i));
    });
    assert(is_complete_top_sort(&top_sort, graph));

    TopSortResult::TopSort(top_sort)
}

fn main() { }
