use vstd::prelude::*;
use vstd::std_specs::iter::{FromIteratorSpec, FromIteratorSpecImpl, IteratorSpec};

verus! {

// A collection whose contents match the iterator's initial remaining sequence.
pub struct Collected<A> {
    pub values: Vec<A>,
}

impl<A> FromIteratorSpecImpl<A> for Collected<A> {
    open spec fn from_iter_ensures(remaining: Seq<A>, s: Self) -> bool {
        remaining == s.values@
    }
}

impl<A> core::iter::FromIterator<A> for Collected<A> {
    // Arbitrary iterator inputs may be infinite, so verify partial correctness.
    #[verifier::exec_allows_no_decreases_clause]
    fn from_iter<T: IntoIterator<Item = A>>(src: T) -> (s: Self) {
        let mut iter = src.into_iter();
        // The actual iterator supplies the witness for from_iter's contract.
        let ghost initial = iter;
        let mut values = Vec::new();
        loop
            invariant
                call_ensures(T::into_iter, (src,), initial),
                iter.obeys_prophetic_iter_laws() == initial.obeys_prophetic_iter_laws(),
                initial.obeys_prophetic_iter_laws() ==> initial.remaining() == values@
                    + iter.remaining(),
        {
            match iter.next() {
                Some(x) => {
                    values.push(x);
                },
                None => {
                    let s = Collected { values };
                    assert(initial.obeys_prophetic_iter_laws() ==> initial.remaining()
                        == s.values@);
                    return s;
                },
            }
        }
    }
}

fn use_collected() {
    let v = vec![1u8, 2, 3];
    let w: Collected<u8> = Collected::from_iter(v);
    assert(w.values@ == v@);

    let mut iter = w.values.into_iter().rev();
    let x: Collected<u8> = Collected::from_iter(&mut iter);
    assert(x.values@ == seq![3u8, 2, 1]);
}

// For Iterator inputs, into_iter returns its input unchanged, so the result
// satisfies the collection's relation to that iterator's remaining sequence.
fn generic_collection<A, I: Iterator<Item = A>, B: core::iter::FromIterator<A>>(iter: I) -> (out: B)
    ensures
        iter.obeys_prophetic_iter_laws() ==> <B as FromIteratorSpec<A>>::from_iter_ensures(
            iter.remaining(),
            out,
        ),
{
    B::from_iter(iter)
}

// A property shared by every allowed conversion outcome also holds for the
// collected sequence. The caller does not need to construct an iterator witness
// for the existential in the postcondition of `from_iter`.
fn generic_property<T: IntoIterator<Item = u8>>(
    src: T,
    Ghost(p): Ghost<spec_fn(Seq<u8>) -> bool>,
) -> (out: Vec<u8>)
    requires
        forall|i: T::IntoIter|
            #![auto]
            call_ensures(T::into_iter, (src,), i) ==> i.obeys_prophetic_iter_laws() && p(
                i.remaining(),
            ),
    ensures
        p(out@),
{
    Vec::from_iter(src)
}

// This specification allows many possible sequences, so callers have no
// particular iterator value to supply as a witness.
pub struct CoarseSrc;

impl IntoIterator for CoarseSrc {
    type Item = u8;

    type IntoIter = std::vec::IntoIter<u8>;

    fn into_iter(self) -> (i: Self::IntoIter)
        ensures
            IteratorSpec::remaining(&i).len() == 2,
            forall|k: int| 0 <= k < 2 ==> IteratorSpec::remaining(&i)[k] < 10,
    {
        vec![1u8, 2].into_iter()
    }
}

fn use_coarse_source() {
    let out: Vec<u8> = Vec::from_iter(CoarseSrc);
    assert(out.len() == 2);
    assert(forall|k: int| 0 <= k < out.len() ==> out[k] < 10);

    let out = generic_property(
        CoarseSrc,
        Ghost(|s: Seq<u8>| s.len() == 2 && forall|k: int| 0 <= k < 2 ==> s[k] < 10),
    );
    assert(out.len() == 2);
    assert(out[0] < 10);
}

} // verus!
