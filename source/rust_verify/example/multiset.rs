// examples of using the multiset, sorted_by lemmas in seq lib
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

proof fn multiset_ext_eq() {

    let a: Seq<int> = seq![1, 2, 3];
    let b: Seq<int> = seq![1, 3, 2];

    let a1: Seq<int> = seq![1];
    a1.to_multiset_properties();
    a1.push(2).to_multiset_properties();
    a1.push(3).to_multiset_properties();

    assert(a.to_multiset() =~= b.to_multiset());
}

proof fn multiset_ext_eq2() {

    let a: Seq<int> = seq![1, 2, 3];
    let b: Seq<int> = seq![3, 1, 2];
    
    let a1: Seq<int> = Seq::empty();
    a1.to_multiset_properties();
    a1.push(1).to_multiset_properties();
    a1.push(3).to_multiset_properties();
    a1.push(1).push(2).to_multiset_properties();
    a1.push(3).push(1).to_multiset_properties();

    assert(a.to_multiset() =~= b.to_multiset());
}

proof fn sorted_by_eg() {

    let leq = |x: int, y: int| x <= y;

    let unsorted = seq![3, 1, 2];
    let sorted = unsorted.sort_by(leq);
    
    let result: Seq<int> = seq![1, 2, 3];
    
    lemma_sort_by_ensures::<int>(unsorted, leq);
    lemma_sort_by_ensures::<int>(result, leq);

    let a1: Seq<int> = Seq::empty();
    a1.to_multiset_properties();
    a1.push(1).to_multiset_properties();
    a1.push(3).to_multiset_properties();
    a1.push(1).push(2).to_multiset_properties();
    a1.push(3).push(1).to_multiset_properties();
    
    assert(result =~= result.sort_by(leq)) by {
        lemma_sorted_unique(result, result.sort_by(leq), leq);
    };

    assert((result.sort_by(leq)) =~= (unsorted.sort_by(leq))) by {
        assert(result.to_multiset() =~= unsorted.to_multiset());
        lemma_sorted_unique(result.sort_by(leq), unsorted.sort_by(leq), leq);
    };
        
    assert(sorted =~= result);
}

}

fn main() {}