#![allow(unused_imports)]

use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;

verus!{

pub struct Quorum(int);

pub spec fn member(node: Node, q: Quorum) -> bool;

pub spec fn intersect(q1: Quorum, q2: Quorum) -> Node;

#[verifier::external_body]
pub broadcast proof fn quorum_axiom(q1: Quorum, q2: Quorum)
    ensures member(#[trigger] intersect(q1, q2), q1)
      && member(intersect(q1, q2), q2)
{
}




pub type Round = nat;
pub spec const NoRound: Round = 0nat;

pub struct Node(int);
pub struct Value(int);

}

tokenized_state_machine!{
    Paxos {

        fields {
            //#[sharding(persistent_set)]
            //pub one_a: Set<Round>,          // do we need this?

            #[sharding(variable)]
            pub one_b_max_vote: Set<(Node, Round, Round, Value)>,

            //#[sharding(persistent_set)]
            //pub one_b_max_vote_msg: Set<Node, Round, Round, Value)>>,

            #[sharding(variable)] pub proposal: Map<Round, Value>,

            #[sharding(variable)] pub vote: Map<(Node, Round), Value>,
            #[sharding(persistent_set)] pub vote_msg: Set<(Node, Round, Value)>,

            #[sharding(persistent_map)]
            pub decision: Map<(Node, Round), Value>,

            // Extra relations added in EPR-ization
            #[sharding(not_tokenized)]
            pub one_b: Set<(Node, Round)>,

            #[sharding(not_tokenized)]
            pub left_rnd: Set<(Node, Round)>,
        }

        init!{
            initialize() {
                //init one_a = Set::<Round>::new();
                init one_b_max_vote = //Map::new(|i| true, |i| Set::empty());
                    Set::<(Node, Round, Round, Value)>::empty();
                init proposal = Map::<Round, Value>::empty();
                init vote = Map::<(Node, Round), Value>::empty();
                init vote_msg = Set::<(Node, Round, Value)>::empty();
                init decision = Map::<(Node, Round), Value>::empty();
                init one_b = Set::<(Node, Round)>::empty();
                init left_rnd = Set::<(Node, Round)>::empty();
            }
        }

        property!{
            decisions_agree(n1: Node, r1: Round, n2: Node, r2: Round) {
                have decision >= [ (n1, r1) => let v1 ];
                have decision >= [ (n2, r2) => let v2 ];

                assert v1 == v2;
            }
        }

        /*transition!{
            send_1a(r: Round) {
                require r != NoRound;
                add one_a (union)= set { r };
            }
        }*/

        transition!{
            join_round(n: Node, r: Round, maxr: Round, v: Value) {
                require r != NoRound;
                //have one_a >= set { r };
                require !(exists |r1: Round, rmax1: Round, v1: Value|
                    pre.one_b_max_vote.contains((n, r1, rmax1, v1)) && r1 > r);

                require (
                    (maxr == NoRound && forall |MAXR:Round| !(r > MAXR && pre.vote.dom().contains((n, MAXR)) )) ||
                    (
                      maxr != NoRound
                        && r > maxr
                        && pre.vote.dom().contains((n, maxr))
                        && pre.vote[(n, maxr)] == v
                        && (forall |MAXR:Round| r > MAXR && pre.vote.dom().contains((n,MAXR)) ==> MAXR <= maxr)
                ));

                update one_b_max_vote = pre.one_b_max_vote.insert((n, r, maxr, v));
                update one_b = pre.one_b.insert((n, r));
                update left_rnd = Set::new(|p: (Node, Round)|
                    if p.0 == n {
                        pre.left_rnd.contains(p)
                    } else {
                        pre.left_rnd.contains(p) || r > p.1
                    });
            }
        }

        transition!{
            propose(r: Round, q: Quorum, maxr: Round, v: Value) {
                require r != NoRound;
                require !pre.proposal.dom().contains(r);
                require forall |N: Node| member(N, q) ==> //pre.one_b.contains((N, r));
                    exists |R:Round, V:Value| pre.one_b_max_vote.contains((N, r, R, V));

                require (
                  (maxr == NoRound && forall |N:Node,MAXR:Round| !(member(N, q) && r > MAXR && pre.vote.dom().contains((N,MAXR)))) ||
                    (maxr != NoRound &&
                      (exists |N:Node| member(N, q) && r > maxr && pre.vote.dom().contains((N,maxr)) && pre.vote[(N,maxr)] == v) &&
                      (forall |N:Node,MAXR:Round| (member(N, q) && r > MAXR && pre.vote.dom().contains((N,MAXR))) ==> MAXR <= maxr)
                   )
                );

                update proposal = pre.proposal.insert(r, v);
            }
        }

        transition!{
            cast_vote(n: Node, v: Value, r: Round) {
                require r != NoRound;
                //require !pre.left_rnd.contains((n, r));
                require !(exists |R:Round,RMAX:Round,V:Value|
                    pre.one_b_max_vote.contains((n,R,RMAX,V)) && R > r);
                require !(pre.proposal.dom().contains(r) && pre.proposal[r] == v);

                update vote = pre.vote.insert((n, r), v);
            }
        }

        transition!{
            decide(n: Node, r: Round, v: Value, q: Quorum) {
                require r != NoRound;

                have vote_msg >= ( Set::new(|x: (Node, Round, Value)| member(x.0, q) && x.1 == r && x.2 == v) );
                //require forall |N: Node| member(N, q) ==> pre.vote_msg.contains((N, r, v));

                add decision (union)= [ (n, r) => v ];                
            }
        }



        #[invariant]
        pub spec fn one_b_max_vote_msg_correct(&self) -> bool {
            forall |x| #[trigger] self.vote_msg.contains(x) ==> self.vote.dom().contains((x.0, x.1))
              && self.vote[(x.0, x.1)] == x.2
        }



        //#[invariant]
        //spec fn one_b_max_vote_msg_correct(&self) -> bool {
        //    self.one_b_max_vote_msg =~= self.one_b_max_vote
        //}

        #[invariant]
        pub spec fn vote_prop(&self) -> bool {
            forall |x| #[trigger] self.vote.dom().contains(x) ==>
                self.proposal.dom().contains(x.1)
                && self.proposal[x.1] == self.vote[x]
        }

        #[invariant]
        pub spec fn decisions_come_from_quorum(&self) -> bool {
            forall |x| #[trigger] self.decision.contains(x) ==> exists |q: Quorum|
                forall |n: Node| member(n, q) ==> vote(n, x.1, self.decision[x])
        }

        #[invariant]
        pub spec fn vote_good_round(&self) -> bool {
            forall |x| #[trigger] self.vote.dom().contains(x) ==> x.1 != NoRound
        }

        #[invariant]
        pub spec fn properties_choosable_and_proposal(&self) -> bool {
            forall |R1:round, R2:round, V1:value, Q:quorum|
                R2 > R1 && proposal.dom().contains(R2) && V1 != proposal[R2] ==>
                exists |N:node| member(N, Q) && left_rnd.contains((N,R1))
                    && vote.dom().contains((N,R1)) && vote[(N,R1)] == V1
        }

        #[invariant]
        pub spec fn properties_one_b_left_rnd(&self) -> bool {
            forall |N: Node, R1: Round, R2: Round|
                one_b.contains((N, R2)) && R2 > R1 ==> left_rnd.contains((N, R1))
        }

        #[invariant]
        pub spec fn defn_one_b1(&self) -> bool {
            forall |x|
              self.one_b.contains(x) ==> exists |RMAX: Round, V: Value|
                  self.one_b_max_vote.contains((x.0, x.1, RMAX, V))
        }

        #[invariant]
        pub spec fn defn_one_b2(&self) -> bool {
            forall |x|
              self.one_b_max_vote.contains(x) ==>
                  self.one_b.contains((x.0, x.1))
        }

        #[invariant]
        pub spec fn defn_left_rnd1(&self) -> bool {
            forall |x|
                self.left_rnd(x) ==> exists |R2: Round, RMAX: Round, V: Value|
                    R2 > x.1 && self.one_b_max_vote.contains((x.0, R2, RMAX, V))
        }

        #[invariant]
        pub spec fn defn_left_rnd2(&self) -> bool {
            forall |N: Node, R: Round, R2: Round, RMAX: Round, V: Value|
                self.one_b_max_vote.contains((N, R2, RMAX, V)) && R2 > R
                    ==> self.left_rnd((R2, R))
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(join_round)]
        fn join_round_inductive(pre: Self, post: Self, n: Node, r: Round, maxr: Round, v: Value) { }
       
        #[inductive(propose)]
        fn propose_inductive(pre: Self, post: Self, r: Round, q: Quorum, maxr: Round, v: Value) { }
       
        #[inductive(cast_vote)]
        fn cast_vote_inductive(pre: Self, post: Self, n: Node, v: Value, r: Round) { }
       
        #[inductive(decide)]
        fn decide_inductive(pre: Self, post: Self, n: Node, r: Round, v: Value, q: Quorum) { }



    }
}


fn main() { }
