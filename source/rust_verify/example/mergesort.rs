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
            forall | i : int | i1 < v1.len() ==> 0 <= i < r.len() ==> r[i] <= v1[i1 as int],
            forall | i : int | i2 < v2.len() ==> 0 <= i < r.len() ==> r[i] <= v2[i2 as int],
            r@.to_multiset() =~= (v1@.subrange(0 as int, i1 as int) + v2@.subrange(0 as int, i2 as int)).to_multiset(),
            is_sorted(&r),
        {

            proof { r@.to_multiset_ensures(); }
            if v1[i1] < v2[i2] {
                r.push(v1[i1]);
                proof {
                    lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, i1 as int), v2@.subrange(0 as int, i2 as int));
                    v1@.subrange(0 as int, i1 as int).to_multiset_ensures();
                    lemma_subrange_push(v1@, 0 as int, i1 as int);
                    lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, (i1 + 1) as int), v2@.subrange(0 as int, i2 as int));
                }
                i1+=1;
            }
            else {
                r.push(v2[i2]);
                proof {
                    lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, i1 as int), v2@.subrange(0 as int, i2 as int));
                    v2@.subrange(0 as int, i2 as int).to_multiset_ensures();
                    lemma_subrange_push(v2@, 0 as int, i2 as int);
                    lemma_to_multiset_distributes_over_add(v1@.subrange(0 as int, i1 as int), v2@.subrange(0 as int, (i2 + 1) as int));
                }
                i2+=1;
            }

        }
        assert (v1@.subrange(0 as int, v1.len() as int) =~= v1@);
        assert (v2@.subrange(0 as int, v2.len() as int) =~= v2@);

        if i1 < v1.len() {
            extend_from_idx(&mut r, v1, i1);
            proof {
                lemma_subrange_add(v1@, 0 as int, i1 as int, v1.len() as int);
                assert(r@.to_multiset() =~= (v1@ + v2@).to_multiset());
            }
        }
        else if i2 < v2.len() {
            extend_from_idx(&mut r, v2, i2);
            proof {
                lemma_subrange_add(v2@, 0 as int, i2 as int, v2.len() as int);
                assert (r@.to_multiset() =~= (v1@ + v2@).to_multiset());
            }
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

    pub open spec fn seq_count_value<A>(s: Seq<A>, a: A) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            ((if s.last() == a { 1nat } else { 0nat }) + seq_count_value(s.drop_last(), a)) as nat
        }
    }

    pub proof fn lemma_multiset_matching_sequences<A>(s1: Seq<A>, s2: Seq<A>)
        requires
            s1.len() == s2.len(),
            forall|a: A| seq_count_value(s1, a) == seq_count_value(s2, a),
        ensures 
            s1.to_multiset() == s2.to_multiset()
        decreases
            s1.len(),
    {
        reveal_with_fuel(seq_count_value, 10);
        s1.to_multiset_ensures();
        s2.to_multiset_ensures();
        if forall|a: A| seq_count_value(s1, a) == 0 {
            assert(forall|a: A| seq_count_value(s2, a) == 0);
            if s1.len() != 0 {
                let x = s1.last();
                assert(seq_count_value(s1, x) >= 1);
            }
            assert(s1.to_multiset() == s2.to_multiset());
        } else {
            let a = s1.last();
            assert(seq_count_value(s1, a) == seq_count_value(s2, a));
            if forall|i2: nat| i2 < s2.len() ==> s2[i2 as int] != a {
                assert(seq_count_value(s2, a) == 0);
                assert(false);
            }
            let i2 = choose|i2: nat| i2 < s2.len() && s2[i2 as int] == a;
            let s1_d = s1.drop_last();
            s1_d.to_multiset_ensures();
            assert(s1_d.to_multiset() == s1.to_multiset().remove(a));
            let s2_d = s2.subrange(0int, i2 as int) + s2.subrange((i2 + 1) as int, s2.len() as int);
            s2_d.to_multiset_ensures();
            assert(s2_d.to_multiset() == s1.to_multiset().remove(a));
            assert(seq_count_value(s1_d, a) == seq_count_value(s1, a) - 1);
            assert forall|aa: A| seq_count_value(s1_d, aa) == seq_count_value(s2_d, aa) by {

            }
            lemma_multiset_matching_sequences(s1_d, s2_d);
            assert(s1_d.to_multiset().insert(a) == s2_d.to_multiset().insert(a));
            assert(s1.to_multiset() == s2.to_multiset());
        }
    }

    fn main () {
        let v = vec![9, 10, 4, 5, 1, 3];
        let v_sorted = merge_sort(&v);
        // Why does this fail
        let ghost expected_res: Seq<u64> = seq![1, 3, 4, 5, 9, 10];
        proof {
            reveal_with_fuel(seq_count_value, 10);
            lemma_multiset_matching_sequences(expected_res, v@);
            assert(expected_res.to_multiset() =~= v@.to_multiset());
            assert(is_sorted(&v_sorted));
            assert(vstd::relations::sorted_by(expected_res, |a: u64, b: u64| a <= b));
            vstd::seq_lib::lemma_sorted_unique(expected_res, v_sorted@, |a: u64, b: u64| a <= b);
            assert(v_sorted@ =~= expected_res);
        }
    }

} // verus!

