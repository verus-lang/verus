use super::super::map::*;
use super::super::modes::*;
use super::super::prelude::*;
use super::super::seq::*;
use super::Loc;
use super::pcm::Resource;
use super::pcm::*;
use super::relations::*;

verus! {

broadcast use super::super::group_vstd_default;

/// Combines a list of values into one value using P::op().
pub open spec fn combine_values<P: PCM>(values: Seq<P>) -> P
    decreases values.len(),
{
    if values.len() == 0 {
        P::unit()
    } else {
        P::op(values[0], combine_values(values.skip(1)))
    }
}

/// Provides four quantified facts about a partially commutative
/// monoid: that it's closed under inclusion, that it's commutative,
/// that it's a monoid, and that its unit element is valid.
///
/// Note that, to avoid trigger loops, it doesn't provide associativity and thus
/// should not be used in the same context as [`lemma_pcm_associative`]
pub proof fn lemma_pcm_properties<P: PCM>()
    ensures
        forall|a: P, b: P| (#[trigger] P::op(a, b)).valid() ==> a.valid(),
        forall|a: P, b: P| (#[trigger] P::op(a, b)) == P::op(b, a),
        forall|a: P| (#[trigger] P::op(a, P::unit())) == a,
        P::valid(P::unit()),
{
    assert forall|a: P, b: P| (#[trigger] P::op(a, b)).valid() implies a.valid() by {
        P::valid_op(a, b);
    }
    assert forall|a: P, b: P| (#[trigger] P::op(a, b)) == P::op(b, a) by {
        P::commutative(a, b);
    }
    assert forall|a: P| P::op(a, P::unit()) == a by {
        P::op_unit(a);
    }
    assert(P::valid(P::unit())) by {
        P::unit_valid();
    }
}

/// Provides a quantified associativity fact about a partially commutative
/// monoid.
///
/// Note that, to avoid trigger loops, it doesn't provide associativity and thus
/// should not be used in the same context as [`lemma_pcm_properties`]
pub proof fn lemma_pcm_associative<P: PCM>()
    ensures
        forall|a: P, b: P, c: P| (#[trigger] P::op(a, P::op(b, c))) == P::op(P::op(a, b), c),
{
    assert forall|a: P, b: P, c: P| (#[trigger] P::op(a, P::op(b, c))) == P::op(P::op(a, b), c) by {
        P::associative(a, b, c);
    }
}

/// Produces a new resource with value `new_value` given a shared
/// reference to a resource `r` whose value has a duplicable part
/// `new_value`. More precisely, produces a resource with value
/// `new_value` given that `r.value() == P::op(r.value(), new_value)`.
pub proof fn copy_duplicable_part<P: PCM>(tracked r: &Resource<P>, new_value: P) -> (tracked out:
    Resource<P>)
    requires
        r.value() == P::op(r.value(), new_value),
    ensures
        out.loc() == r.loc(),
        out.value() == new_value,
{
    lemma_pcm_properties::<P>();
    r.validate();
    r.duplicate_previous(new_value)
}

/// Duplicates `r`, returning an identical resource. The value of
/// `r` must be duplicable, i.e., `r.value()` must be equal to
/// `P::op(r.value(), r.value())`.
pub proof fn duplicate<P: PCM>(tracked r: &Resource<P>) -> (tracked other: Resource<P>)
    requires
        P::op(r.value(), r.value()) == r.value(),
    ensures
        other.loc() == r.loc(),
        other.value() == r.value(),
{
    copy_duplicable_part(r, r.value())
}

/// Incorporates the resources of `r2` into `r1`, consuming `r2`.
pub proof fn incorporate<P: PCM>(tracked r1: &mut Resource<P>, tracked r2: Resource<P>)
    requires
        old(r1).loc() == r2.loc(),
    ensures
        r1.loc() == old(r1).loc(),
        r1.value() == P::op(old(r1).value(), r2.value()),
{
    let tracked mut r = r1.extract();
    let tracked mut joined_r = r.join(r2);
    tracked_swap(r1, &mut joined_r);
}

/// Splits the value of `r` into `left` and `right`. At the end, `r`
/// ends up with `left` as its value and the function returns a new
/// resource with value `right`.
pub proof fn split_mut<P: PCM>(tracked r: &mut Resource<P>, left: P, right: P) -> (tracked other:
    Resource<P>)
    requires
        old(r).value() == P::op(left, right),
    ensures
        r.loc() == other.loc() == old(r).loc(),
        r.value() == left,
        other.value() == right,
{
    let tracked mut r_value = r.extract();
    let tracked (mut r_left, r_right) = r_value.split(left, right);
    tracked_swap(r, &mut r_left);
    r_right
}

/// Updates `r` to have new value `new_value`. This must be a
/// frame-preserving update. That is, `new_value` must be compatible
/// with all frames `old(r).value()` was compatible with.
pub proof fn update_mut<P: PCM>(tracked r: &mut Resource<P>, new_value: P)
    requires
        frame_preserving_update(old(r).value(), new_value),
    ensures
        r.loc() == old(r).loc(),
        r.value() == new_value,
{
    let tracked mut r_value = r.extract();
    let tracked mut r_upd = r_value.update(new_value);
    tracked_swap(r, &mut r_upd);
}

/// Redistribute the values held by resources `r1` and `r2` such that they
/// have the same combination as before. The new value of `r1` will be `v1`
/// and the new value of `r2` will be `v2`.
pub proof fn redistribute<P: PCM>(
    tracked r1: &mut Resource<P>,
    tracked r2: &mut Resource<P>,
    v1: P,
    v2: P,
)
    requires
        old(r1).loc() == old(r2).loc(),
        P::op(old(r1).value(), old(r2).value()) == P::op(v1, v2),
    ensures
        r1.loc() == r2.loc() == old(r1).loc(),
        r1.value() == v1,
        r2.value() == v2,
{
    lemma_pcm_properties::<P>();
    let tracked r2_extracted = r2.extract();
    incorporate(r1, r2_extracted);
    let tracked mut r2_new = split_mut(r1, v1, v2);
    tracked_swap(r2, &mut r2_new);
}

/// Update the values held by resources `r1` and `r2` such that their
/// values' combination is updated in a frame-preserving way (i.e.,
/// that combination must be updatable in a frame-preserving way to
/// the combination of `v1` and `v2`). The new value of `r1` will be
/// `v1` and the new value of `r2` will be `v2`.
pub proof fn update_and_redistribute<P: PCM>(
    tracked r1: &mut Resource<P>,
    tracked r2: &mut Resource<P>,
    v1: P,
    v2: P,
)
    requires
        old(r1).loc() == old(r2).loc(),
        frame_preserving_update(P::op(old(r1).value(), old(r2).value()), P::op(v1, v2)),
    ensures
        r1.loc() == r2.loc() == old(r1).loc(),
        r1.value() == v1,
        r2.value() == v2,
{
    lemma_pcm_properties::<P>();
    let tracked r2_extracted = r2.extract();
    incorporate(r1, r2_extracted);
    update_mut(r1, P::op(v1, v2));
    let tracked mut r2_new = split_mut(r1, v1, v2);
    tracked_swap(r2, &mut r2_new);
}

// This is a helper function used by `validate_multiple_resources` but
// not meant for public export.
//
// This function is given a map of resources and removes them one by one, accumulating them in a
// resource by `join`ing them
proof fn aggregate_resources_from_map_starting_at_offset<P: PCM>(
    tracked m: &mut Map<int, Resource<P>>,
    loc: Loc,
    values: Seq<P>,
    offset: int,
) -> (tracked all: Resource<P>)
    requires
        0 <= offset < values.len(),
        forall|i|
            #![trigger old(m).dom().contains(i)]
            0 <= i < offset ==> !old(m).dom().contains(i),
        forall|i|
            #![trigger old(m).dom().contains(i)]
            offset <= i < values.len() ==> old(m).dom().contains(i),
        forall|i|
            #![trigger old(m)[i]]
            offset <= i < values.len() ==> old(m)[i].loc() == loc && old(m)[i].value() == values[i],
    ensures
        forall|i| #![trigger m.dom().contains(i)] 0 <= i < values.len() ==> !m.dom().contains(i),
        all.loc() == loc,
        all.value() == combine_values::<P>(values.skip(offset)),
    decreases values.len() - offset,
{
    assert(m.dom().contains(offset));
    assert(m[offset].loc() == loc && m[offset].value() == values[offset]);
    let tracked p = m.tracked_remove(offset);
    if offset == values.len() - 1 {
        assert(combine_values::<P>(values.skip(offset)) == values[offset]) by {
            lemma_pcm_properties::<P>();  // needed to show that combining with unit is locentity
            reveal_with_fuel(combine_values, 2);
        };
        p
    } else {
        assert(combine_values::<P>(values.skip(offset)) == P::op(
            values[offset],
            combine_values::<P>(values.skip(offset + 1)),
        )) by {
            assert(values[offset] == values.skip(offset)[0]);
            assert(values.skip(offset + 1) == values.skip(offset).skip(1));
        }
        assert forall|i|
            #![trigger m.dom().contains(i)]
            offset + 1 <= i < values.len() implies m.dom().contains(i) && m[i].loc() == loc
            && m[i].value() == values[i] by {
            assert(m.dom().contains(i));
            assert(m[i].loc() == loc && m[i].value() == values[i]);
        }
        let tracked most = aggregate_resources_from_map_starting_at_offset(
            m,
            loc,
            values,
            offset + 1,
        );
        assert(most.loc() == loc);
        assert(most.value() == combine_values::<P>(values.skip(offset + 1)));
        p.join(most)
    }
}

// This is a helper function used by `validate_multiple_resources` but
// not meant for public export.
//
// This function restores the resources in the map to their original values.
//
// This function is given a map `m`, and the original carrier values in values.
// Moreover, the aggregated resource is `p`. It splits the aggregated resource and restores the
// original resources in map
proof fn store_resources_into_map_starting_at_offset<P: PCM>(
    tracked m: &mut Map<int, Resource<P>>,
    values: Seq<P>,
    offset: int,
    tracked p: Resource<P>,
)
    requires
        0 <= offset < values.len(),
        forall|i| #![trigger old(m).dom().contains(i)] 0 <= i < offset ==> old(m).dom().contains(i),
        forall|i|
            #![trigger old(m)[i]]
            0 <= i < offset ==> old(m)[i].loc() == p.loc() && old(m)[i].value() == values[i],
        forall|i|
            #![trigger old(m).dom().contains(i)]
            offset <= i < values.len() ==> !old(m).dom().contains(i),
        p.value() == combine_values::<P>(values.skip(offset)),
    ensures
        forall|i| #![trigger m.dom().contains(i)] 0 <= i < values.len() ==> m.dom().contains(i),
        forall|i|
            #![trigger m[i]]
            0 <= i < values.len() ==> m[i].loc() == p.loc() && m[i].value() == values[i],
    decreases values.len() - offset,
{
    assert(combine_values::<P>(values.skip(offset)) == P::op(
        values[offset],
        combine_values::<P>(values.skip(offset + 1)),
    )) by {
        assert(values[offset] == values.skip(offset)[0]);
        assert(values.skip(offset + 1) == values.skip(offset).skip(1));
    }
    let tracked (p_first, p_rest) = p.split(
        values[offset],
        combine_values::<P>(values.skip(offset + 1)),
    );
    m.tracked_insert(offset, p_first);
    if offset < values.len() - 1 {
        store_resources_into_map_starting_at_offset(m, values, offset + 1, p_rest);
    }
}

/// Validates that a given sequence of resources has values that
/// combine to form a valid value. Although that sequence consists of
/// mutable references, none of those resources change. (They change
/// in the middle of the function, but are restored by the time it
/// completes.) The sequence of resources is specified using the
/// following input parameters:
///
/// `m` -- a map from integers to resources, mapping 0 to the first
/// resource, 1 to the second, etc.
///
/// `loc` -- the `loc()` shared by all the resources in `m`
///
/// `values` -- the sequence of resources
// The proof goes as follows:
// - join all the mutable resources, with aggregate_resources_from_map_starting_at_offset
// - validate the joined resource with the shared reference with validate_2
// - restore the mutable resources with store_resources_into_map_starting_at_offset
pub proof fn validate_multiple<P: PCM>(
    tracked m: &mut Map<int, Resource<P>>,
    values: Seq<P>,
    tracked shared: &Resource<P>,
)
    requires
        values.len() > 0,
        forall|i|
            #![trigger old(m).dom().contains(i)]
            0 <= i < values.len() ==> old(m).dom().contains(i),
        forall|i|
            #![trigger old(m)[i]]
            0 <= i < values.len() ==> old(m)[i].loc() == shared.loc() && old(m)[i].value()
                == values[i],
    ensures
        forall|i| #![trigger m.dom().contains(i)] 0 <= i < values.len() ==> m.dom().contains(i),
        forall|i|
            #![trigger m[i]]
            0 <= i < values.len() ==> m[i].loc() == shared.loc() && m[i].value() == values[i],
        P::op(combine_values::<P>(values), shared.value()).valid(),
{
    let tracked mut agg = aggregate_resources_from_map_starting_at_offset(
        m,
        shared.loc(),
        values,
        0,
    );
    assert(agg.value() == combine_values::<P>(values)) by {
        assert(values == values.skip(0));
    }
    agg.validate_2(shared);
    store_resources_into_map_starting_at_offset(m, values, 0, agg);
}

/// Validates that the three given resources have values that combine to form a valid value.
/// Although `r1` and `r2` are mutable, they don't change. (They change during the function but
/// are restored to the way they were by the time the function returns.)
pub proof fn validate_3<P: PCM>(
    tracked r1: &mut Resource<P>,
    tracked r2: &mut Resource<P>,
    tracked r3: &Resource<P>,
)
    requires
        old(r1).loc() == r3.loc(),
        old(r2).loc() == r3.loc(),
    ensures
        r1.loc() == r3.loc(),
        r2.loc() == r3.loc(),
        r1.value() == old(r1).value(),
        r2.value() == old(r2).value(),
        P::op(r1.value(), P::op(r2.value(), r3.value())).valid(),
{
    lemma_pcm_properties::<P>();
    let tracked mut m: Map<int, Resource<P>> = Map::<int, Resource<P>>::tracked_empty();
    let values: Seq<P> = seq![r1.value(), r2.value()];
    m.tracked_insert(0, r1.extract());
    m.tracked_insert(1, r2.extract());
    assert(combine_values::<P>(values) == P::op(old(r1).value(), old(r2).value())) by {
        lemma_pcm_properties::<P>();
        reveal_with_fuel(combine_values, 3);
    }
    validate_multiple(&mut m, values, r3);
    let tracked mut new_r1 = m.tracked_remove(0);
    let tracked mut new_r2 = m.tracked_remove(1);
    tracked_swap(r1, &mut new_r1);
    tracked_swap(r2, &mut new_r2);
    assert(P::op(r1.value(), P::op(r2.value(), r3.value())).valid()) by {
        lemma_pcm_associative::<P>();
    };
}

/// Validates that the four given resources have values that combine to form a valid value.
/// Although the inputs `r1`, `r2` and `r3` are mutable, they don't change. (They change during
/// the function but are restored to the way they were by the time the function returns.)
pub proof fn validate_4<P: PCM>(
    tracked r1: &mut Resource<P>,
    tracked r2: &mut Resource<P>,
    tracked r3: &mut Resource<P>,
    tracked r4: &Resource<P>,
)
    requires
        old(r1).loc() == r4.loc(),
        old(r2).loc() == r4.loc(),
        old(r3).loc() == r4.loc(),
    ensures
        r1.loc() == r4.loc(),
        r2.loc() == r4.loc(),
        r3.loc() == r4.loc(),
        r1.value() == old(r1).value(),
        r2.value() == old(r2).value(),
        r3.value() == old(r3).value(),
        P::op(r1.value(), P::op(r2.value(), P::op(r3.value(), r4.value()))).valid(),
{
    lemma_pcm_properties::<P>();
    let tracked mut m: Map<int, Resource<P>> = Map::<int, Resource<P>>::tracked_empty();
    let values: Seq<P> = seq![r1.value(), r2.value(), r3.value()];
    m.tracked_insert(0, r1.extract());
    m.tracked_insert(1, r2.extract());
    m.tracked_insert(2, r3.extract());
    assert(combine_values::<P>(values) == P::op(
        old(r1).value(),
        P::op(old(r2).value(), old(r3).value()),
    )) by {
        lemma_pcm_properties::<P>();
        reveal_with_fuel(combine_values, 4);
    }
    validate_multiple(&mut m, values, r4);
    let tracked mut new_r1 = m.tracked_remove(0);
    let tracked mut new_r2 = m.tracked_remove(1);
    let tracked mut new_r3 = m.tracked_remove(2);
    tracked_swap(r1, &mut new_r1);
    tracked_swap(r2, &mut new_r2);
    tracked_swap(r3, &mut new_r3);
    assert(P::op(r1.value(), P::op(r2.value(), P::op(r3.value(), r4.value()))).valid()) by {
        lemma_pcm_associative::<P>();
    }
}

/// Validates that the five given resources have values that combine to form a valid value.
/// Although the inputs `r1`, `r2`, `r3` and `r4` are mutable, they don't change. (They change
/// during the function but are restored to the way they were by the time the function returns.)
pub proof fn validate_5<P: PCM>(
    tracked r1: &mut Resource<P>,
    tracked r2: &mut Resource<P>,
    tracked r3: &mut Resource<P>,
    tracked r4: &mut Resource<P>,
    tracked r5: &Resource<P>,
)
    requires
        old(r1).loc() == r5.loc(),
        old(r2).loc() == r5.loc(),
        old(r3).loc() == r5.loc(),
        old(r4).loc() == r5.loc(),
    ensures
        r1.loc() == r5.loc(),
        r2.loc() == r5.loc(),
        r3.loc() == r5.loc(),
        r4.loc() == r5.loc(),
        r1.value() == old(r1).value(),
        r2.value() == old(r2).value(),
        r3.value() == old(r3).value(),
        r4.value() == old(r4).value(),
        P::op(
            r1.value(),
            P::op(r2.value(), P::op(r3.value(), P::op(r4.value(), r5.value()))),
        ).valid(),
{
    lemma_pcm_properties::<P>();
    let tracked mut m: Map<int, Resource<P>> = Map::<int, Resource<P>>::tracked_empty();
    let values: Seq<P> = seq![r1.value(), r2.value(), r3.value(), r4.value()];
    assert(combine_values::<P>(values) == P::op(
        old(r1).value(),
        P::op(old(r2).value(), P::op(old(r3).value(), old(r4).value())),
    )) by {
        lemma_pcm_properties::<P>();
        reveal_with_fuel(combine_values, 5);
    }
    m.tracked_insert(0, r1.extract());
    m.tracked_insert(1, r2.extract());
    m.tracked_insert(2, r3.extract());
    m.tracked_insert(3, r4.extract());
    validate_multiple(&mut m, values, r5);
    let tracked mut new_r1 = m.tracked_remove(0);
    let tracked mut new_r2 = m.tracked_remove(1);
    let tracked mut new_r3 = m.tracked_remove(2);
    let tracked mut new_r4 = m.tracked_remove(3);
    tracked_swap(r1, &mut new_r1);
    tracked_swap(r2, &mut new_r2);
    tracked_swap(r3, &mut new_r3);
    tracked_swap(r4, &mut new_r4);
    assert(P::op(
        r1.value(),
        P::op(r2.value(), P::op(r3.value(), P::op(r4.value(), r5.value()))),
    ).valid()) by {
        lemma_pcm_associative::<P>();
    }
}

} // verus!
