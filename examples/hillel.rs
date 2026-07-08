// A port of `hillel_creusot.rs` from Creusot annotations to Verus.
// Creusot original:
//   https://github.com/creusot-rs/creusot/blob/bef58f6aa7493ac8c8012164a8eeab462c346d1a/tests/should_succeed/vector/07_read_write.rs
//
// A series of formal verification challenges by Hillel Wayne:
// https://www.hillelwayne.com/post/theorem-prover-showdown/
//

use vstd::prelude::*;
use vstd::math::abs;
use vstd::std_specs::iter::*;
use vstd::std_specs::slice::*;
use vstd::std_specs::cmp::*;
use vstd::laws_eq::*;

verus! {

fn right_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T)
    ensures
        final(str)@.len() >= len && final(str)@.len() >= old(str)@.len(),
        final(str)@.len() == len || final(str)@.len() == old(str)@.len(),
        len <= old(str)@.len() ==> final(str)@.len() == old(str)@.len(),
        len > old(str)@.len() ==> final(str)@.len() == len,
        forall|i: int| 0 <= i < old(str)@.len() ==> final(str)@[i] == old(str)@[i],
        forall|i: int| old(str)@.len() <= i < len ==> final(str)@[i] == pad,
{
    let ghost old_str = str@;

    while str.len() < len
        invariant
            old_str.len() <= str@.len(),
            old_str.len() < len ==> str@.len() <= len,
            str@.len() > len ==> str@.len() == old_str.len(),
            forall|i: int| 0 <= i < old_str.len() ==> #[trigger] str@[i] == old_str[i],
            forall|i: int| old_str.len() <= i < str@.len() ==> #[trigger] str@[i] == pad,
        decreases len - str.len(),
    {
        str.push(pad);
    }
}

fn left_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T)
    ensures
        final(str)@.len() >= len && final(str)@.len() >= old(str)@.len(),
        final(str)@.len() == len || final(str)@.len() == old(str)@.len(),
        forall|i: int| 0 <= i < (final(str)@.len() - old(str)@.len()) ==> final(str)@[i] == pad,
        forall|i: int| 0 <= i < old(str)@.len() ==>
            final(str)@[i + (final(str)@.len() - old(str)@.len())] == old(str)@[i],
{
    let ghost old_str = str@;
    let ghost mut c: int = 0;

    while str.len() < len
        invariant
            old_str.len() <= str@.len(),
            old_str.len() < len ==> str@.len() <= len,
            str@.len() > len ==> str@.len() == old_str.len(),
            c == str@.len() - old_str.len(),
            forall|i: int| c <= i < str@.len() ==> #[trigger] str@[i] == old_str[i - c],
            forall|i: int| 0 <= i < c ==> #[trigger] str@[i] == pad,
        decreases len - str.len(),
    {
        str.insert(0, pad);
        proof {
            c = 1 + c;
        }
    }
}

spec fn is_unique<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == s[j] ==> i == j
}

spec fn seq_contains<T>(seq: Seq<T>, elem: T) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == elem
}

spec fn is_subset<T>(sub: Seq<T>, sup: Seq<T>) -> bool {
    forall|i: int| 0 <= i < sub.len() ==> #[trigger] seq_contains(sup, sub[i])
}

proof fn subset_push<T>(s: Seq<T>, elem: T)
    ensures
        is_subset(s, s.push(elem)),
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] seq_contains(s.push(elem), s[i]) by {
        assert(s.push(elem)[i] == s[i]);
    }
}

proof fn subset_trans<T>(a: Seq<T>, b: Seq<T>, c: Seq<T>)
    requires
        is_subset(a, b),
        is_subset(b, c),
    ensures
        is_subset(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] seq_contains(c, a[i]) by {
        assert(seq_contains(b, a[i]));
        let k = choose|k: int| 0 <= k < b.len() && b[k] == a[i];
        assert(seq_contains(c, b[k]));
    }
}

fn insert_unique<T: PartialEq + DeepView>(vec: &mut Vec<T>, elem: T)
    requires
        obeys_deep_eq::<T>(),
        is_unique(old(vec).deep_view()),
    ensures
        is_unique(final(vec).deep_view()),
        is_subset(old(vec).deep_view(), final(vec).deep_view()),
        is_subset(final(vec).deep_view(), old(vec).deep_view().push(elem.deep_view())),
        seq_contains(final(vec).deep_view(), elem.deep_view()),
{
    broadcast use group_laws_eq;

    reveal(obeys_deep_eq);
    let ghost gvec = vec@;
    let ghost gdv = vec.deep_view();

    for e in it: vec.iter()
        invariant
            obeys_deep_eq::<T>(),
            vec@ == gvec,
            is_unique(vec.deep_view()),
            it.seq() == vec@.as_ref(),
            it.seq().len() == vec@.len(),
            it.index() <= vec@.len(),
            forall|j: int| 0 <= j < it.index() ==>
                (#[trigger] vec@[j]).deep_view() != elem.deep_view(),
    {
        proof {
            reveal(obeys_deep_eq);
        }
        if *e == elem {
            proof {
                assert(vec.deep_view()[it.index()] == elem.deep_view());
                assert(final(vec).deep_view() =~= vec.deep_view());
                assert(old(vec).deep_view() =~= vec.deep_view());
                let dv = vec.deep_view();
                subset_push(dv, elem.deep_view());
            }
            return;
        }
        proof {
            assert(vec@[it.index()].deep_view() == (*e).deep_view());
        }
    }
    proof {
        broadcast use vstd::seq_lib::group_seq_lib_default;
        assert forall|j: int| 0 <= j < vec@.len() implies (#[trigger] vec@[j]).deep_view()
            != elem.deep_view() by {}
        assert forall|j: int| 0 <= j < gdv.len() implies #[trigger] gdv[j] != elem.deep_view() by {
            assert(gdv[j] == gvec[j].deep_view());
        }
    }
    vec.push(elem);
    proof {
        let dv = vec.deep_view();
        assert(dv =~= gdv.push(elem.deep_view()));
        assert forall|i: int, j: int|
            0 <= i < dv.len() && 0 <= j < dv.len() && dv[i] == dv[j] implies i == j by {
            assert(dv[i] == gdv.push(elem.deep_view())[i]);
            assert(dv[j] == gdv.push(elem.deep_view())[j]);
        }
        subset_push(gdv, elem.deep_view());
        assert(dv[gdv.len() as int] == elem.deep_view());
    }
}

fn unique<T: PartialEq + DeepView + Copy>(str: &[T]) -> (result: Vec<T>)
    requires
        obeys_deep_eq::<T>(),
    ensures
        is_unique(result.deep_view()),
        is_subset(result.deep_view(), str.deep_view()),
        is_subset(str.deep_view(), result.deep_view()),
{
    let mut unique: Vec<T> = Vec::new();

    for i in it: 0..str.len()
        invariant
            obeys_deep_eq::<T>(),
            is_unique(unique.deep_view()),
            is_subset(unique.deep_view(), str.deep_view()),
            is_subset(str.deep_view().subrange(0, it.index()), unique.deep_view()),
    {
        let elem: T = str[i];
        let ghost old_unique = unique.deep_view();
        insert_unique(&mut unique, elem);
        proof {
            assert(str.deep_view()[i as int] == elem.deep_view());
            let pushed = old_unique.push(elem.deep_view());
            assert forall|k: int| 0 <= k < pushed.len() implies #[trigger] seq_contains(
                str.deep_view(),
                pushed[k],
            ) by {
                if k < old_unique.len() {
                    assert(pushed[k] == old_unique[k]);
                } else {
                    assert(pushed[k] == elem.deep_view());
                }
            }
            subset_trans(unique.deep_view(), pushed, str.deep_view());
            subset_trans(
                str.deep_view().subrange(0, it.index()),
                old_unique,
                unique.deep_view(),
            );
            let subk = str.deep_view().subrange(0, it.index());
            let subk1 = str.deep_view().subrange(0, it.index() + 1);
            assert forall|m: int| 0 <= m < subk1.len() implies #[trigger] seq_contains(
                unique.deep_view(),
                subk1[m],
            ) by {
                if m < it.index() {
                    assert(subk1[m] == subk[m]);
                } else {
                    assert(subk1[m] == elem.deep_view());
                }
            }
        }
    }
    proof {
        assert(str.deep_view().subrange(0, str@.len() as int) =~= str.deep_view());
    }
    unique
}

spec fn sum_range(seq: Seq<u32>, from: int, to: int) -> int
    decreases to - from,
{
    if 0 <= from < to <= seq.len() {
        seq[from] as int + sum_range(seq, from + 1, to)
    } else {
        0
    }
}

proof fn sum_range_nonneg(seq: Seq<u32>, from: int, to: int)
    requires
        0 <= from <= to <= seq.len(),
    ensures
        sum_range(seq, from, to) >= 0,
    decreases to - from,
{
    if to - from > 0 {
        sum_range_nonneg(seq, from + 1, to);
    }
}

proof fn sum_range_split(seq: Seq<u32>, from: int, to: int, i: int)
    requires
        0 <= from <= i <= to <= seq.len(),
    ensures
        sum_range(seq, from, to) == sum_range(seq, from, i) + sum_range(seq, i, to),
    decreases i - from,
{
    if i > from {
        sum_range_split(seq, from + 1, to, i);
    }
}

spec fn score(seq: Seq<u32>, i: int) -> int {
    abs(sum_range(seq, 0, i) - sum_range(seq, i, seq.len() as int)) as int
}

proof fn score_props(seq: Seq<u32>, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        0 <= score(seq, i) <= sum_range(seq, 0, seq.len() as int),
        (0 == i || i == seq.len()) ==> score(seq, i) == sum_range(seq, 0, seq.len() as int),
{
    sum_range_split(seq, 0, seq.len() as int, i);
    sum_range_nonneg(seq, 0, i);
    sum_range_nonneg(seq, i, seq.len() as int);
}

// Creuso used `u32::abs_diff`, so we supply a spec here
pub assume_specification[ u32::abs_diff ](x: u32, y: u32) -> (r: u32)
    ensures
        r == abs(x - y),
;

// Fulcrum. Given a sequence of integers, returns the index i that minimizes
// |sum(seq[..i]) - sum(seq[i..])|. Does this in O(n) time and O(n) memory.
// Hard
fn fulcrum(s: &[u32]) -> (result: usize)
    requires
        sum_range(s@, 0, s@.len() as int) <= 1000,
        s@.len() > 0,
    ensures
        0 <= result < s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> score(s@, result as int) <= score(s@, i),
{
    broadcast use group_slice_axioms;

    let mut total: u32 = 0;

    proof {
        sum_range_nonneg(s@, 0, s@.len() as int);
    }

    for x in it: s
        invariant
            it.seq() == s@.as_ref(),
            sum_range(s@, 0, s@.len() as int) <= 1000,
            total@ == sum_range(s@, 0, it.index()),
            total@ <= sum_range(s@, 0, s@.len() as int),
    {
        proof {
            sum_range_split(s@, 0, s@.len() as int, it.index() + 1);
            sum_range_split(s@, 0, it.index() + 1, it.index());
            sum_range_nonneg(s@, it.index() + 1, s@.len() as int);
            reveal_with_fuel(sum_range, 2);
        }
        total += *x;
    }

    proof {
        score_props(s@, 0);
    }

    let mut min_i: usize = 0;
    let mut min_dist: u32 = total;

    let mut sum: u32 = 0;
    for i in it: 0..s.len()
        invariant
            sum@ == sum_range(s@, 0, it.index()),
            sum@ <= total@,
            total@ == sum_range(s@, 0, s@.len() as int),
            min_i@ <= it.index() && min_i@ < s@.len(),
            min_dist@ == score(s@, min_i as int),
            forall|j: int| 0 <= j < it.index() ==> score(s@, min_i as int) <= score(s@, j),
    {
        proof {
            score_props(s@, i as int);
            sum_range_split(s@, 0, s@.len() as int, i as int);
            sum_range_nonneg(s@, i as int, s@.len() as int);
            sum_range_split(s@, 0, s@.len() as int, i + 1);
            sum_range_split(s@, 0, i + 1, i as int);
            sum_range_nonneg(s@, i + 1, s@.len() as int);
        }
        let dist = sum.abs_diff(total - sum);
        if dist < min_dist {
            min_i = i;
            min_dist = dist;
        }

        sum += s[i];
    }

    min_i
}

fn main() {}

} // verus!
