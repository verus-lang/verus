// examples of using the multiset, sorted_by lemmas in seq lib
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::relations::sorted_by;

verus! {

proof fn multiset_ext_eq() {

    let a: Seq<int> = seq![1, 2, 3];
    let b: Seq<int> = seq![1, 3, 2];

    lemma_seq_properties::<int>(); //Provides the necessary lemmas for seq to multiset conversion
    assert(a.to_multiset() =~= b.to_multiset());
}

proof fn multiset_ext_eq2() {

    let a: Seq<int> = seq![3, 2, 1, 1, 2, 3];
    let b: Seq<int> = seq![1, 2, 3, 1, 2, 3];
    
    lemma_seq_properties::<int>(); //Provides the necessary lemmas for seq to multiset conversion
    assert(a.to_multiset() =~= b.to_multiset());
}

proof fn sorted_by_eg() {

    let leq = |x: int, y: int| x <= y;

    let unsorted = seq![3, 1, 2];
    let sorted = unsorted.sort_by(leq);
    
    let result: Seq<int> = seq![1, 2, 3];
    
    lemma_sort_by_ensures::<int>(unsorted, leq);
    lemma_sort_by_ensures::<int>(result, leq);
    lemma_seq_properties::<int>();
    
    assert(sorted_by(result,leq));

    assert(result =~= (unsorted.sort_by(leq))) by {
        assert(result.to_multiset() =~= unsorted.to_multiset());
        lemma_sorted_unique(result, unsorted.sort_by(leq), leq);
    };
        
    assert(sorted =~= result);
}

}

fn main() {}