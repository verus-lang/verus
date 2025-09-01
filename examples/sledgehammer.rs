
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

    uninterp spec fn f(x: int) -> int;

    uninterp spec fn another_prop() -> bool;

    broadcast axiom fn also_needed()
        ensures #[trigger] another_prop();

    broadcast axiom fn f_prop(x: int)
        requires another_prop()
        ensures #[trigger] f(x) > 42;


    #[verifier::sledgehammer]
    proof fn foo(x: int)
        ensures f(x) * 2 > 84
    {
    }

    #[verifier::sledgehammer]
    proof fn f_in_body(x: int)
    {
        assert(f(x) * 2 > 84);
    }


    uninterp spec fn implies_goal() -> bool;
    uninterp spec fn other() -> bool;

    broadcast axiom fn implies_goal_prop()
        ensures #[trigger] implies_goal() ==> f(2) > 80;

    broadcast axiom fn other_prop()
        ensures #[trigger] other() ==> implies_goal();

    #[verifier::sledgehammer]
    proof fn function_in_requires()
        requires other(),
        ensures f(2) > 80,
    {
    }

    // TODO: Sledgehammer cannot currently detect lemmas in other crates that
    // are not referenced from the current crate. broadcast groups can be used to
    // mention lemmas that should be used by Sledgehammer:
    broadcast group seq_lemmas {
        Seq::lemma_flatten_push,
    }

    #[verifier::sledgehammer]
    proof fn my_proof() {
        let xs = seq![seq![1int, 2], seq![3]];
        assert(xs.push(seq![5]).flatten() =~= xs.flatten() + seq![5]);
    }
}