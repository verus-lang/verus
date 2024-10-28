// examples of using the multiset, sorted_by lemmas in seq lib
use vstd::prelude::*;
use vstd::relations::sorted_by;
use vstd::seq_lib::*;

verus! {

proof fn multiset_ext_eq() {
    let a: Seq<int> = seq![1, 2, 3];
    let b: Seq<int> = seq![1, 3, 2];
    lemma_seq_properties::<int>();  //Provides the necessary lemmas for seq to multiset conversion
    // These two assertions trigger quantifiers relating sequence contents to multiset counts
    assert(a =~= seq![1].push(2).push(3));
    assert(b =~= seq![1].push(3).push(2));
    assert(a.to_multiset() =~= b.to_multiset());
}

proof fn multiset_ext_eq2() {
    let a: Seq<int> = seq![3, 2, 1, 1, 2, 3];
    let b: Seq<int> = seq![1, 2, 3, 1, 2, 3];
    lemma_seq_properties::<int>();  //Provides the necessary lemmas for seq to multiset conversion
    // These two assertions trigger quantifiers relating sequence contents to multiset counts
    assert(a =~= seq![3].push(2).push(1).push(1).push(2).push(3));
    assert(b =~= seq![1].push(2).push(3).push(1).push(2).push(3));
    assert(a.to_multiset() =~= b.to_multiset());
}

proof fn sorted_by_leq() {
    //Provides the verifier with important lemmas about sequences
    lemma_seq_properties::<int>();
    let leq = |x: int, y: int| x <= y;
    let unsorted = seq![3, 1, 5, 2, 4];
    let sorted = unsorted.sort_by(leq);
    //Tells the verifier what the sort_by function ensures to be true
    unsorted.lemma_sort_by_ensures(leq);
    let expected_result: Seq<int> = seq![1, 2, 3, 4, 5];
    assert(sorted_by(expected_result, leq));
    // These two assertions trigger quantifiers relating sequence contents to multiset counts
    assert(unsorted =~= seq![3].push(1).push(5).push(2).push(4));
    assert(expected_result =~= seq![1].push(2).push(3).push(4).push(5));
    assert(expected_result.to_multiset() =~= unsorted.to_multiset());
    //Proves that any two sequences that are sorted and have the same elements are equal.
    lemma_sorted_unique(expected_result, unsorted.sort_by(leq), leq);
    assert(sorted =~= expected_result);
}

} // verus!
fn main() {}
