use vstd::prelude::*;
use vstd::multiset::*;

verus! {

    pub open spec fn is_sorted (v : &Vec<u64>) -> bool {
        forall | i : int, j : int | 0 <= i < j < v.len() ==>  #[trigger] v[i] <= #[trigger] v[j]
    }

    fn extend_from_idx(r : &mut Vec<u64>, v : &Vec<u64>, start : usize) 
        requires (start < v.len())
        ensures (r@ == old(r)@ + v@.subrange(start as int, v.len() as int))
    {
        let mut i : usize = start;
        while (i < v.len())
            invariant (start <= i <= v.len()), (r@ =~= old(r)@ + v@.subrange(start as int, i as int))
        {
            r.push(v[i]);
            i+=1;
        }
    }

    pub broadcast proof fn lemma_to_multiset_distributes_over_add(s1 : Seq<u64>, s2 : Seq<u64>) 
        ensures (#[trigger] (s1 + s2).to_multiset() =~= s1.to_multiset().add(s2.to_multiset())),
        decreases s2.len(),
    {
        s2.to_multiset_ensures();
        if (s2.len() == 0) {
            assert ((s1 + s2).to_multiset() =~= s1.to_multiset());
            assert (s2.to_multiset() =~= Multiset::<u64>::empty());
        } else {
            lemma_to_multiset_distributes_over_add(s1, s2.drop_last());
            vstd::seq::Seq::drop_last_distributes_over_add(s1, s2);
            assert (s2.drop_last() =~= s2.remove(s2.len() - 1));
            assert (s1 + s2 =~= (s1 + s2).drop_last().push(s2[(s2.len() - 1) as int]));
            assert ((s1 + s2).to_multiset() =~= ((s1 + s2).drop_last().push(s2[(s2.len() - 1) as int])).to_multiset());
            (s1 + s2).drop_last().to_multiset_ensures();
        }
    }

    proof fn lemma_subrange_push(s1 : Seq<u64>, start : int, end : int)
        requires 0 <= start <= end < s1.len(),
        ensures s1.subrange(start, end).push(s1[end]) =~= s1.subrange(start, end + 1),
        {
        }

     proof fn lemma_subrange_add(s1 : Seq<u64>, start : int, mid : int, end : int)
        requires 0 <= start <= mid <= end <= s1.len(),
        ensures s1.subrange(start, mid) + s1.subrange(mid, end) =~= s1.subrange(start, end),
        {
        }

    fn merge (v1 : &Vec<u64>, v2 : &Vec<u64>) -> (r : Vec<u64>)
        requires is_sorted(v1), is_sorted(v2),
        ensures (r@.to_multiset() == (v1@ + v2@).to_multiset()), is_sorted(&r),
    {
        broadcast use lemma_to_multiset_distributes_over_add;
        let mut r: Vec<u64> = Vec::new();
        let mut i1 : usize = 0;
        let mut i2 : usize = 0;
        assert (v1@.subrange(0 as int, i1 as int) == Seq::<u64>::empty());

        while (i1 < v1.len() && i2 < v2.len())
        invariant
            0 <= i1 <= v1.len(),
            0 <= i2 <= v2.len(),
            is_sorted(v1),
            is_sorted(v2),
            (forall | i : int | i1 < v1.len() ==> 0 <= i < r.len() ==> r[i] <= v1[i1 as int]),
            (forall | i : int | i2 < v2.len() ==> 0 <= i < r.len() ==> r[i] <= v2[i2 as int]),
            r@.to_multiset() =~= (v1@.subrange(0 as int, i1 as int) + v2@.subrange(0 as int, i2 as int)).to_multiset(),
            is_sorted(&r),
        {

            proof { r@.to_multiset_ensures(); }
            if v1[i1] < v2[i2] {
                r.push(v1[i1]);
                proof { lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, i1 as int), v2@.subrange(0 as int, i2 as int)); }
                proof { v1@.subrange(0 as int, i1 as int).to_multiset_ensures(); }
                proof { lemma_subrange_push(v1@, 0 as int, i1 as int); }
                proof { lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, (i1 + 1) as int), v2@.subrange(0 as int, i2 as int)); }
                i1+=1;
            }
            else {
                r.push(v2[i2]);
                proof { lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, i1 as int), v2@.subrange(0 as int, i2 as int)); }
                proof { v2@.subrange(0 as int, i2 as int).to_multiset_ensures(); }
                proof { lemma_subrange_push(v2@, 0 as int, i2 as int); }
                proof { lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, i1 as int), v2@.subrange(0 as int, (i2 + 1) as int)); }
                i2+=1;
            }

        }
        assert (v1@.subrange(0 as int, v1.len() as int) =~= v1@);
        assert (v2@.subrange(0 as int, v2.len() as int) =~= v2@);

        if i1 < v1.len() {
            extend_from_idx(&mut r, v1, i1);
            proof { lemma_subrange_add(v1@, 0 as int, i1 as int, v1.len() as int); }
            assert (r@.to_multiset() =~= (v1@ + v2@).to_multiset());
        }
        else if i2 < v2.len() {
            extend_from_idx(&mut r, v2, i2);
            proof { lemma_subrange_add(v2@, 0 as int, i2 as int, v2.len() as int); }
            assert (r@.to_multiset() =~= (v1@ + v2@).to_multiset());
        }
        r
    }

    fn merge_sort (v : &Vec<u64>) -> (r : Vec<u64>)
    		ensures (r@.to_multiset() == (*v)@.to_multiset()), is_sorted(&r),
    {
        let n = v.len();
        let mut v1 = v.clone();
        if (n <= 1) {
            v1
        }
        else {
            let mut v2 = v1.split_off(n/2);
            assert(v1@ + v2@ == v@);
            proof { lemma_to_multiset_distributes_over_add(v1@, v2@); }
            let r1 = merge_sort(&mut v1);
            let r2 = merge_sort(&mut v2);
            proof { lemma_to_multiset_distributes_over_add(r1@, r2@); }
            let r = merge(&r1, &r2);
            r
        }
    }

    #[verifier::external_body]
    fn main () {
        let v = vec![9, 10, 4, 5, 1, 3];
        let v_sorted = merge_sort(&v);
        // Why does this fail
        let res : Vec<u64> = vec![1,3,4,5,9,10];
        assert(v_sorted =~= res);
    }

} // verus!

