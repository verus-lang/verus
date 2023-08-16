#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_spec_fn_ensures_passes_postcondition verus_code! {
        spec fn spec_fn_ensures_passes_postcondition(x: int) -> (out: int)
        ensures out == 2 * x
        {
            x + x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_spec_fn_ensures_fails_postcondition verus_code! {
        spec fn spec_fn_ensures_fails_postcondition(x: int) -> (out: int)
        ensures out == 3 * x    // FAILS
        {
            x + x
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_spec_fn_ensures_has_usable_axiom verus_code! {
        #[verifier(opaque)]
        spec fn spec_fn_doubley(x: int) -> (out: int)
        ensures out == 2 * x
        {
            x + x
        }

        proof fn exercise()
        {
            assert(spec_fn_doubley(14) == 28);
        }
    } => Ok(())
}

test_verify_one_file! {
    // TODO(chris): Ignored for now because we don't support induction yet.
    #[ignore] #[test] test_spec_fn_ensures_induction verus_code! {
        use vstd::prelude::*;
        spec fn evens(count: int) -> (out: Seq<int>)
        ensures
            // basic test
            out.len()==count,

            // fancier result we really want
            // TODO(chris): previous ensures out.len()==count should be assumed for this next line,
            // where we want to pass the recommends check on spec_index:
            forall |j| out[j] == j*2,

            //evens(count).len()==count,  // TODO(chris): do we want to allow or disallow mentioning evens? IIRC this was something that was too hard for now -- but then probably it should be an error? You mentioned an SCC walk; I'm not sure how to do that.
        decreases count when 0 <= count
        {
            if count==0 { Seq::empty() }
            else { evens(count-1).push(count*2) }
        }
    } => Ok(())
}

test_verify_one_file! {
    // TODO(chris): ignored for now, but: do we want to allow or disallow mentioning evens? IIRC this was something that was too hard for now -- but then probably it should be an error? You mentioned an SCC walk; I'm not sure how to do that.
    #[ignore] #[test] test_spec_fn_ensures_names_self verus_code! {
        use vstd::prelude::*;
        spec fn evens(count: int) -> Seq<int>
        ensures
            evens(count).len()==count,
        decreases count when 0 <= count
        {
            if count==0 { Seq::empty() }
            else { evens(count-1).push(count*2) }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_spec_fn_associated_proof verus_code! {
        #[verifier(opaque)]
        spec fn dingle(x: int) -> int { x + x }

        // TODO(chris): This test confirms that an associated proof fn body
        // may be successfully used to complete a spec fn ensures proof.
        // It's a little silly, because we're calling it a "decreases_by"
        // even though that's not how we're using it.
        #[verifier(decreases_by)]
        proof fn dingle_helper(x: int) {
            reveal(dingle);
            assert( dingle(x) == x + x );
        }
        
        spec fn spec_fn_ensures_dingle(x: int) -> (out: int)
        ensures out == dingle(x)
        decreases x via dingle_helper
        {
            x + x
        }
    } => Ok(())
}

test_verify_one_file! {
    // TODO(chris): ignored for now, but this was another hairy case we discussed.
    #[ignore] #[test] test_spec_fn_mutual_ensures_decreases verus_code! {
        spec fn f(x: int) -> (out: int)
        ensures out == 1
        decreases x
        {
            if x == 0 { 1 } else { f(x - f(x)) }
        }
    } => Ok(())
    // Presently, "postcondition not satisfied" and "unable to show termination"
}
