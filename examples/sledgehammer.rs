
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
}