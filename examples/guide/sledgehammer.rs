use vstd::prelude::*;

verus! {


/*
// ANCHOR: set_example_fails
proof fn union_three_sets<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
    ensures
        xs.union(ys).union(zs).len() <= xs.len() + ys.len() + zs.len()
{
}
// ANCHOR_END: set_example_fails

// ANCHOR: set_example_done
proof fn union_three_sets<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
    ensures
        xs.union(ys).union(zs).len() <= xs.len() + ys.len() + zs.len()
{
        broadcast use union_len;
}
// ANCHOR_END: set_example_done

// ANCHOR: set_example_lemma
// In a file far, far away..
broadcast proof fn union_len<A>(xs: Set<A>, ys: Set<A>)
    ensures
        #[trigger] xs.union(ys).len() <= xs.len() + ys.len(),
{ <proof omitted> }
// ANCHOR_END: set_example_lemma
*/

// ANCHOR: set_example_sledgehammer
#[verifier::sledgehammer]
proof fn union_three_sets<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
    ensures
        xs.union(ys).union(zs).len() <= xs.len() + ys.len() + zs.len()
{
}
// ANCHOR_END: set_example_sledgehammer

broadcast proof fn union_len<A>(xs: Set<A>, ys: Set<A>)
    ensures
        #[trigger] xs.union(ys).len() <= xs.len() + ys.len(),
{
    admit();
}

// ANCHOR: set_example_sledgehammer_no_min
#[verifier::sledgehammer(false)]
proof fn union_three_sets_unminimized<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
    ensures
        xs.union(ys).union(zs).len() <= xs.len() + ys.len() + zs.len()
{
}
// ANCHOR_END: set_example_sledgehammer_no_min

// ANCHOR: requires_vstd_lemma
#[verifier::sledgehammer]
proof fn my_proof() {
    let xs = seq![seq![1int, 2], seq![3]];
    assert(xs.push(seq![5]).flatten() =~= xs.flatten() + seq![5]);
}
// ANCHOR_END: requires_vstd_lemma

// ANCHOR: vstd_lemma_reference
broadcast group sledgehammer_hints {
    vstd::seq::Seq::group_seq_flatten,
}
// ANCHOR_END: vstd_lemma_reference

}
