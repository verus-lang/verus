// TODO: should this go in seq_lib or remain as its own file?
// Dafny puts it in its own file

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::seq::*;
#[allow(unused_imports)]
use crate::multiset::Multiset;
#[allow(unused_imports)]
use crate::relations::*;
use crate::seq_lib::lemma_seq_union_to_multiset_commutative;
use crate::seq_lib::lemma_seq_properties;
use crate::seq_lib::lemma_multiset_commutative;

verus!{

pub open spec fn merge_sort_by<A>(s: Seq<A>, leq: FnSpec(A,A) ->bool) -> Seq<A>
    recommends
        total_ordering(leq),
    decreases
        s.len(),
{
    if s.len() <=1 {s}
    else{
        let split_index = s.len() /2;
        let left = s.subrange(0,split_index as int);
        let right = s.subrange(split_index as int, s.len() as int);
        
        let left_sorted = merge_sort_by(left, leq);
        let right_sorted = merge_sort_by(right, leq);
        merge_sorted_with(left_sorted, right_sorted, leq)
    }
}

pub open spec fn merge_sorted_with<A>(left: Seq<A>, right: Seq<A>, leq: FnSpec(A,A) ->bool) -> Seq<A>
    recommends
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    decreases
        left.len(), right.len()
{
    if left.len() == 0 {right}
    else if right.len() == 0 {left}
    else if leq(left.first(), right.first()){
        Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right, leq)
    } else {
        Seq::<A>::empty().push(right.first()) + merge_sorted_with(left, right.drop_first(), leq)
    }
}

pub proof fn lemma_merge_sort_by_ensures<A>(s: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        total_ordering(leq),
    ensures
        s.to_multiset() =~= merge_sort_by(s,leq).to_multiset(),
        sorted_by(merge_sort_by(s,leq), leq),
    decreases
        s.len(),
{
    if s.len() <=1 {}
    else{
        let split_index = s.len() /2;
        let left = s.subrange(0,split_index as int);
        let right = s.subrange(split_index as int, s.len() as int);
        
        assert(s =~= left + right);

        let left_sorted = merge_sort_by(left, leq);
        lemma_merge_sort_by_ensures(left, leq);
        let right_sorted = merge_sort_by(right, leq);
        lemma_merge_sort_by_ensures(right, leq);

        lemma_merge_sorted_with_ensures(left_sorted, right_sorted, leq);
        lemma_multiset_commutative(left,right);
        lemma_multiset_commutative(left_sorted,right_sorted);
    }
}

pub proof fn lemma_merge_sorted_with_ensures<A>(left: Seq<A>, right: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    ensures
        (left+right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset(),
        sorted_by(merge_sorted_with(left, right, leq), leq),
    decreases
        left.len(), right.len()
{
    lemma_seq_properties::<A>();
    if left.len() == 0 {
        assert(left+right =~= right);
    }
    else if right.len() == 0 {
        assert(left+right =~= left);
    }
    else if leq(left.first(), right.first()){
        let result = Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right, leq);
        lemma_merge_sorted_with_ensures(left.drop_first(), right, leq);

        let rest = merge_sorted_with(left.drop_first(), right, leq);
        assert(rest.len() == 0 || rest.first() == left.drop_first().first() || rest.first() == right.first()) by {
            if left.drop_first().len() == 0 {}
            else if leq(left.drop_first().first(), right.first()) {
                assert(rest =~= Seq::<A>::empty().push(left.drop_first().first()) + merge_sorted_with(left.drop_first().drop_first(), right, leq));
            }
            else {
                assert(rest =~= Seq::<A>::empty().push(right.first()) + merge_sorted_with(left.drop_first(), right.drop_first(), leq));
            }
        }
        lemma_new_first_element_still_sorted_by(left.first(), rest, leq);
        assert((left.drop_first() + right) =~= (left + right).drop_first());
    } else {
        let result = Seq::<A>::empty().push(right.first()) + merge_sorted_with(left, right.drop_first(), leq);
        lemma_merge_sorted_with_ensures(left, right.drop_first(), leq);

        let rest = merge_sorted_with(left, right.drop_first(), leq);
        assert(rest.len() == 0 || rest.first() == left.first() || rest.first() == right.drop_first().first()) by {
            assert(left.len() > 0);
            if right.drop_first().len() == 0 {/*assert(rest =~= left);*/}
            else if leq(left.first(), right.drop_first().first()) { //right might be length 1
                assert(rest =~= Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right.drop_first(), leq));
            }
            else {
                assert(rest =~= Seq::<A>::empty().push(right.drop_first().first()) + merge_sorted_with(left, right.drop_first().drop_first(), leq));
            }
        }
       
        lemma_new_first_element_still_sorted_by(right.first(), merge_sorted_with(left, right.drop_first(), leq), leq);
        lemma_seq_union_to_multiset_commutative(left,right);
        assert((right.drop_first() + left) =~= (right + left).drop_first());
        lemma_seq_union_to_multiset_commutative(right.drop_first(), left);
    }
}

}