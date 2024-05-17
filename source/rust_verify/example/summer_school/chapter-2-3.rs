use multiset::*;
#[allow(unused_imports)]
use prelude::*;
#[allow(unused_imports)]
use seq::*;
use set::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::*;

verus! {

spec fn is_sorted(seqint: Seq<int>) -> bool {
    // summer school definition:
    //    forall(|idx: nat| idx < seqint.len()-1 ==> seqint.index(idx) <= seqint.index(idx+1 as int)) // TODO(utaal): the as int here is nasty. Why would index take something other than a nat?
    //    TODO(utaal): Could not automatically infer triggers for this quantifer.  Use #[trigger] annotations to manually mark trigger terms instead.
    // But jonh hates that summer school definition! Better to forall pairs of indices.
    forall|i: int, j: int| 0 <= i <= j < seqint.len() ==> seqint[i] <= seqint[j]
}

spec fn count_in_seq<T>(a: Seq<T>, t: T) -> nat
    decreases a.len(),
{
    //decreases(a);   // TOOD(utaal): thread 'rustc' panicked at 'internal error: unsupported type for decreases Boxed(Datatype(PathX { krate: None, segments: ["vstd", "seq", "Seq"] }, [TypParam("T")]))', vir/src/recursion.rs:86:14
    if a.len() == 0 {
        0
    } else {
        count_in_seq(a.drop_last(), t) + if a.last() == t {
            1nat
        } else {
            0
        }
    }
}

//fn count_in_seq<T>(a: Seq<T>, t: T) -> nat
//{
//    exists(|indices:Set<nat>|
//            true
//         && forall(|idx:nat| indices.contains(idx) ==> idx < a.len())
//         && forall(|idx:nat| idx < a.len() && indices.contains(idx) == a.index(t))
//         )
//}
spec fn multiset_matches_seq<T>(a: Seq<T>, b: Multiset<T>) -> bool {
    forall|t: T| count_in_seq(a, t) == b.count(t)
}

spec fn multiset_from_seq<T>(input: Seq<T>) -> Multiset<T>
    decreases input.len(),  // TODO(utaal): when bug fixed, remove len
{
    // show we CAN build a multiset constructively from a seq
    if input.len() == 0 {
        Multiset::empty()
    } else {
        multiset_from_seq(input.drop_last()).insert(input.last())
    }
}

proof fn multiset_lemma<T>(input: Seq<T>, output: Multiset<T>)
    requires
        multiset_from_seq(input) == output,
    ensures
// show we did build a multiset constructively from a seq

        multiset_matches_seq(input, output),
        // show there's no other multiset that'll work.
        forall|other: Multiset<T>| multiset_matches_seq(input, other) ==> other == output,
{
    if input.len() == 0 {
        //assert(output == Multiset::empty());
        assert(multiset_matches_seq(input, output));
        assume(forall|other: Multiset<T>| multiset_matches_seq(input, other) ==> other == output);  // TODO
    } else {
        /*
        let prev = multiset_from_seq(
        let output = multiset_lemma(input.drop_last()
        assert(multiset_matches_seq(input, output));
        // show there's no other multiset that'll work.
        assert(forall(|other:Multiset<T>| multiset_matches_seq(input, other) ==> equal(other, output)));
        output
        */
        assume(false);
        assert(multiset_matches_seq(input, output));
        assert(forall|other: Multiset<T>| multiset_matches_seq(input, other) ==> other == output);
    }
}

spec fn sort_spec(input: Seq<int>, output: Seq<int>) -> bool {
    &&& is_sorted(output)
    &&& multiset_from_seq(output) == multiset_from_seq(input)
}

spec fn view_i64(i64seq: Seq<i64>) -> Seq<int> {
    i64seq.map(|_index: int, i: i64| i as int)
}

fn merge_sort(input: Vec<i64>) -> (output: Vec<i64>)
    ensures
        sort_spec(view_i64(input.view()), view_i64(output.view())),
{
    assume(false);
    input  // TODO(jonh): haven't actually implemented

}

fn main() {
}

} // verus!
