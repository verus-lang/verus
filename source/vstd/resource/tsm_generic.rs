//! Per-strategy facts used by the checked generic field-token interface
//! (`#[verified_generic_tokens]`). Each lemma states what one token's
//! singleton component determines about a full state when it is included
//! in a fragment that completes to `embed(state)`, so that the generated
//! operation proofs need no per-machine fragment reasoning.
use super::super::prelude::*;
use super::super::map::Map;
use super::super::multiset::Multiset;
use super::agree::AgreementRA;
use super::algebra::ResourceAlgebra;
use super::exclusive::ExclusiveRA;
use super::pcm::PCM;
use super::tsm::CountRA;
use super::tsm_collections::*;
use super::tsm_finite_multiset::*;
use super::tsm_persistent::*;

verus! {

broadcast use {
    super::super::imap::group_imap_lemmas,
    super::super::iset::group_iset_lemmas,
    super::super::map::group_map_lemmas,
    super::super::set::group_set_lemmas,
    super::super::multiset::group_multiset_axioms,
};

/// A `variable` token's exclusive value is the state's value.
pub proof fn exclusive_included_owned<V>(
    owned: Option<ExclusiveRA<V>>,
    rest: Option<ExclusiveRA<V>>,
    frame: Option<ExclusiveRA<V>>,
    whole: V,
    value: V,
)
    requires
        Option::<ExclusiveRA<V>>::op(Option::<ExclusiveRA<V>>::op(owned, rest), frame)
            == Some(ExclusiveRA::Exclusive(whole)),
        owned == Some(ExclusiveRA::Exclusive(value)),
    ensures
        Option::<ExclusiveRA<V>>::op(owned, rest) == Some(ExclusiveRA::Exclusive(value)),
        whole == value,
{
}

/// A constant's agreed value is the state's value.
pub proof fn agree_included_owned<V>(
    owned: Option<AgreementRA<V>>,
    rest: Option<AgreementRA<V>>,
    frame: Option<AgreementRA<V>>,
    whole: V,
    value: V,
)
    requires
        Option::<AgreementRA<V>>::op(Option::<AgreementRA<V>>::op(owned, rest), frame)
            == Some(AgreementRA::Agree(whole)),
        owned == Some(AgreementRA::Agree(value)),
    ensures
        Option::<AgreementRA<V>>::op(owned, rest) == Some(AgreementRA::Agree(value)),
        whole == value,
{
}

/// An `option` token's value is the state's value.
pub proof fn option_included_owned<V>(
    owned: OptionFragment<V>,
    rest: OptionFragment<V>,
    frame: OptionFragment<V>,
    whole: Option<V>,
    value: V,
)
    requires
        OptionFragment::op(OptionFragment::op(owned, rest), frame) == option_frag(whole),
        owned == Some(ExclusiveRA::Exclusive(value)),
    ensures
        OptionFragment::op(owned, rest) == Some(ExclusiveRA::Exclusive(value)),
        whole == Some(value),
{
}

/// An optional collection of `option` tokens: present values are the state's.
pub proof fn option_included_general<V>(
    owned: OptionFragment<V>,
    rest: OptionFragment<V>,
    frame: OptionFragment<V>,
    whole: Option<V>,
    value: Option<V>,
)
    requires
        OptionFragment::op(OptionFragment::op(owned, rest), frame) == option_frag(whole),
        owned == option_frag(value),
    ensures
        value is Some ==> OptionFragment::op(owned, rest) == option_frag(value) && whole == value,
{
}

/// An optional collection of `persistent_option` tokens.
pub proof fn persistent_option_included_general<V>(
    owned: PersistentOptionFragment<V>,
    rest: PersistentOptionFragment<V>,
    frame: PersistentOptionFragment<V>,
    whole: Option<V>,
    value: Option<V>,
)
    requires
        PersistentOptionFragment::op(PersistentOptionFragment::op(owned, rest), frame)
            == persistent_option_frag(whole),
        owned == persistent_option_frag(value),
    ensures
        value is Some ==> PersistentOptionFragment::op(owned, rest) == persistent_option_frag(value)
            && whole == value,
{
}

/// A `count` token's amount is a lower bound of the state's count.
pub proof fn count_included_owned(owned: CountRA, rest: CountRA, frame: CountRA, whole: nat, n: nat)
    requires
        CountRA::op(CountRA::op(owned, rest), frame) == (CountRA { count: whole }),
        owned.count == n,
    ensures
        CountRA::op(owned, rest).count >= n,
        whole >= n,
{
}

/// A `persistent_count` token's amount is a lower bound of the state's count.
pub proof fn persistent_count_included_owned(
    owned: PersistentCountRA,
    rest: PersistentCountRA,
    frame: PersistentCountRA,
    whole: nat,
    n: nat,
)
    requires
        PersistentCountRA::op(PersistentCountRA::op(owned, rest), frame) == (PersistentCountRA {
            count: whole,
        }),
        owned.count == n,
    ensures
        PersistentCountRA::op(owned, rest).count >= n,
        whole >= n,
{
}

/// A `persistent_bool` token means the state's boolean is true.
pub proof fn persistent_bool_included_owned(
    owned: PersistentCountRA,
    rest: PersistentCountRA,
    frame: PersistentCountRA,
    whole: bool,
)
    requires
        PersistentCountRA::op(PersistentCountRA::op(owned, rest), frame) == persistent_bool_frag(
            whole,
        ),
        owned.count == 1,
    ensures
        PersistentCountRA::op(owned, rest).count == 1,
        whole,
{
}

/// An optional `bool` collection: if present, the state's boolean is true.
pub proof fn bool_included_general(
    owned: CountRA,
    rest: CountRA,
    frame: CountRA,
    whole: bool,
    value: bool,
)
    requires
        CountRA::op(CountRA::op(owned, rest), frame) == super::tsm_bool::bool_frag(whole),
        owned == super::tsm_bool::bool_frag(value),
    ensures
        value ==> CountRA::op(owned, rest).count == 1 && whole,
{
}

/// An optional `persistent_bool` collection.
pub proof fn persistent_bool_included_general(
    owned: PersistentCountRA,
    rest: PersistentCountRA,
    frame: PersistentCountRA,
    whole: bool,
    value: bool,
)
    requires
        PersistentCountRA::op(PersistentCountRA::op(owned, rest), frame) == persistent_bool_frag(
            whole,
        ),
        owned == persistent_bool_frag(value),
    ensures
        value ==> PersistentCountRA::op(owned, rest).count == 1 && whole,
{
}

/// A `multiset` token's element occurs in the state's multiset.
pub proof fn multiset_included_owned<V>(
    owned: FiniteMultisetRA<V>,
    rest: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    value: V,
)
    requires
        FiniteMultisetRA::op(FiniteMultisetRA::op(owned, rest), frame) == finite_multiset_frag(
            whole,
        ),
        owned.values.count(value) >= 1,
    ensures
        FiniteMultisetRA::op(owned, rest).values.count(value) >= 1,
        whole.count(value) >= 1,
{
}

/// A multiset token collection is contained in the state's multiset.
pub proof fn multiset_included_many<V>(
    owned: FiniteMultisetRA<V>,
    rest: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    observed: Multiset<V>,
)
    requires
        FiniteMultisetRA::op(FiniteMultisetRA::op(owned, rest), frame) == finite_multiset_frag(
            whole,
        ),
        owned.values == observed,
    ensures
        observed.subset_of(FiniteMultisetRA::op(owned, rest).values),
        observed.subset_of(whole),
{
}

/// A multiset token collection included in the shared part `shared` of a
/// fragment that completes to `whole`: it is contained in `shared`, and
/// together with the owned part in `whole`.
pub proof fn multiset_shared_included_many<V>(
    tok: FiniteMultisetRA<V>,
    rest: FiniteMultisetRA<V>,
    owned: FiniteMultisetRA<V>,
    shared: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    observed: Multiset<V>,
)
    requires
        shared == FiniteMultisetRA::op(tok, rest),
        FiniteMultisetRA::op(FiniteMultisetRA::op(owned, shared), frame) == finite_multiset_frag(
            whole,
        ),
        tok.values == observed,
    ensures
        observed.subset_of(shared.values),
        owned.values.add(observed).subset_of(whole),
{
}

/// A persistent map token's entry is the state's entry.
pub proof fn persistent_map_included_owned_at<K, V>(
    owned: PersistentMapFragment<K, V>,
    rest: PersistentMapFragment<K, V>,
    frame: PersistentMapFragment<K, V>,
    map: IMap<K, V>,
    key: K,
    value: V,
)
    requires
        PersistentMapFragment::op(PersistentMapFragment::op(owned, rest), frame)
            == persistent_map_frag(map),
        owned.at(key) == Some(AgreementRA::Agree(value)),
    ensures
        PersistentMapFragment::op(owned, rest).at(key) == Some(AgreementRA::Agree(value)),
        map.contains_key(key),
        map[key] == value,
{
    assert(PersistentMapFragment::op(PersistentMapFragment::op(owned, rest), frame).at(key)
        == persistent_map_frag(map).at(key));
}

/// A persistent set token's element is in the state's set.
pub proof fn persistent_set_included_owned_at<K>(
    owned: PersistentSetFragment<K>,
    rest: PersistentSetFragment<K>,
    frame: PersistentSetFragment<K>,
    set: ISet<K>,
    key: K,
)
    requires
        PersistentSetFragment::op(PersistentSetFragment::op(owned, rest), frame)
            == persistent_set_frag(set),
        owned.at(key) == Some(AgreementRA::Agree(())),
    ensures
        PersistentSetFragment::op(owned, rest).at(key) == Some(AgreementRA::Agree(())),
        set.contains(key),
{
    assert(PersistentSetFragment::op(PersistentSetFragment::op(owned, rest), frame).at(key)
        == persistent_set_frag(set).at(key));
}

/// The same for a collection of persistent map tokens.
pub proof fn persistent_map_included_owned_many<K, V>(
    owned: PersistentMapFragment<K, V>,
    rest: PersistentMapFragment<K, V>,
    frame: PersistentMapFragment<K, V>,
    map: IMap<K, V>,
    observed: IMap<K, V>,
)
    requires
        PersistentMapFragment::op(PersistentMapFragment::op(owned, rest), frame)
            == persistent_map_frag(map),
        forall|key: K|
            observed.contains_key(key) ==> #[trigger] owned.at(key) == Some(
                AgreementRA::Agree(observed[key]),
            ),
    ensures
        forall|key: K|
            observed.contains_key(key) ==> #[trigger] PersistentMapFragment::op(owned, rest).at(
                key,
            ) == Some(AgreementRA::Agree(observed[key])),
        observed.submap_of(map),
{
    assert forall|key: K| observed.contains_key(key) implies #[trigger] PersistentMapFragment::op(
        owned,
        rest,
    ).at(key) == Some(AgreementRA::Agree(observed[key])) && map.contains_key(key) && map[key]
        == observed[key] by {
        persistent_map_included_owned_at(owned, rest, frame, map, key, observed[key]);
    }
    assert forall|key: K| #[trigger] observed.contains_key(key) implies map.contains_key(key)
        && observed[key] == map[key] by {
        persistent_map_included_owned_at(owned, rest, frame, map, key, observed[key]);
    }
}

/// The same for a collection of persistent set tokens.
pub proof fn persistent_set_included_owned_many<K>(
    owned: PersistentSetFragment<K>,
    rest: PersistentSetFragment<K>,
    frame: PersistentSetFragment<K>,
    set: ISet<K>,
    observed: ISet<K>,
)
    requires
        PersistentSetFragment::op(PersistentSetFragment::op(owned, rest), frame)
            == persistent_set_frag(set),
        forall|key: K|
            observed.contains(key) ==> #[trigger] owned.at(key) == Some(AgreementRA::Agree(())),
    ensures
        forall|key: K|
            observed.contains(key) ==> #[trigger] PersistentSetFragment::op(owned, rest).at(key)
                == Some(AgreementRA::Agree(())),
        observed.subset_of(set),
{
    assert forall|key: K| observed.contains(key) implies #[trigger] PersistentSetFragment::op(
        owned,
        rest,
    ).at(key) == Some(AgreementRA::Agree(())) && set.contains(key) by {
        persistent_set_included_owned_at(owned, rest, frame, set, key);
    }
    assert forall|key: K| #[trigger] observed.contains(key) implies set.contains(key) by {
        persistent_set_included_owned_at(owned, rest, frame, set, key);
    }
}

/// Splitting one entry off a finite map's pointwise fragment.
pub proof fn pointwise_map_split<K, P: PCM>(
    whole: Pointwise<K, P>,
    one: Pointwise<K, P>,
    others: Pointwise<K, P>,
    key: K,
)
    requires
        forall|k: K| k != key ==> #[trigger] one.at(k) == P::unit(),
        others.at(key) == P::unit(),
        one.at(key) == whole.at(key),
        forall|k: K| k != key ==> #[trigger] others.at(k) == whole.at(k),
    ensures
        Pointwise::<K, P>::op(one, others) == whole,
{
    assert forall|k: K| #[trigger] Pointwise::<K, P>::op(one, others).at(k) == whole.at(k) by {
        if k == key {
            whole.at(k).op_unit();
        } else {
            P::commutative(P::unit(), whole.at(k));
            whole.at(k).op_unit();
        }
    }
    Pointwise::extensionality(Pointwise::<K, P>::op(one, others), whole);
}

/// Two agreement resources at one location hold the same value.
pub proof fn agreement_resources_agree<V>(
    tracked a: &super::pcm::Resource<Option<AgreementRA<V>>>,
    tracked b: &super::pcm::Resource<Option<AgreementRA<V>>>,
)
    requires
        a.loc() == b.loc(),
        a.value() is Some && a.value()->Some_0 is Agree,
        b.value() is Some && b.value()->Some_0 is Agree,
    ensures
        a.value() == b.value(),
{
    let tracked upper = a.join_shared(b);
    upper.validate();
    let left = choose|frame: Option<AgreementRA<V>>|
        Option::<AgreementRA<V>>::op(a.value(), frame) == upper.value();
    let right = choose|frame: Option<AgreementRA<V>>|
        Option::<AgreementRA<V>>::op(b.value(), frame) == upper.value();
    assert(upper.value() == a.value());
    assert(upper.value() == b.value());
}

/// A copy of an agreement resource (its value is idempotent).
pub proof fn agreement_duplicate<V>(tracked a: &super::pcm::Resource<Option<AgreementRA<V>>>)
    -> (tracked out: super::pcm::Resource<Option<AgreementRA<V>>>)
    requires
        a.value() is Some && a.value()->Some_0 is Agree,
    ensures
        out.loc() == a.loc(),
        out.value() == a.value(),
{
    assert(Option::<AgreementRA<V>>::op(a.value(), a.value()) == a.value());
    super::duplicate(a)
}

/// Remove a submap `t` from a tracked map, returning it.
pub proof fn tracked_remove_submap<K, V>(tracked m: &mut IMap<K, V>, t: IMap<K, V>) -> (tracked out:
    IMap<K, V>)
    requires
        t.submap_of(*old(m)),
    ensures
        out == t,
        *final(m) == old(m).remove_keys(t.dom()),
{
    let tracked out = m.tracked_remove_keys(t.dom());
    assert(out =~= t);
    out
}

/// A tracked finite map as a tracked infinite map with the same entries.
pub proof fn tracked_map_to_imap<K, V>(tracked m: Map<K, V>) -> (tracked out: IMap<K, V>)
    ensures
        out == m.to_imap(),
        out.dom().finite(),
    decreases m.len(),
{
    let ghost original = m;
    if m.len() == 0 {
        super::super::set_lib::lemma_set_empty_equivalency_len(m.dom());
        let tracked out = IMap::tracked_empty();
        assert(out =~= original.to_imap());
        out
    } else {
        let key = m.dom().choose();
        super::super::set_lib::lemma_set_empty_equivalency_len(m.dom());
        assert(m.dom().contains(key));
        let tracked mut m = m;
        let tracked value = m.tracked_remove(key);
        let tracked mut out = tracked_map_to_imap(m);
        out.tracked_insert(key, value);
        assert(out =~= original.to_imap());
        out
    }
}

/// A tracked infinite map with a finite domain as a tracked finite map.
pub proof fn tracked_imap_to_map<K, V>(tracked m: IMap<K, V>) -> (tracked out: Map<K, V>)
    requires
        m.dom().finite(),
    ensures
        out.to_imap() == m,
    decreases m.dom().len(),
{
    let ghost original = m;
    if m.dom().len() == 0 {
        assert forall|k: K| !m.dom().contains(k) by {
            if m.dom().contains(k) {
                super::super::iset::lemma_iset_contains_len(m.dom(), k);
            }
        }
        let tracked out = Map::tracked_empty();
        assert(out.to_imap() =~= original);
        out
    } else {
        super::super::iset::lemma_iset_choose_len(m.dom());
        let key = m.dom().choose();
        super::super::iset::lemma_iset_remove_len(m.dom(), key);
        let tracked mut m = m;
        let tracked value = m.tracked_remove(key);
        assert(m.dom() =~= original.dom().remove(key));
        let tracked mut out = tracked_imap_to_map(m);
        let ghost rec = out;
        out.tracked_insert(key, value);
        assert forall|k: K| #[trigger] original.contains_key(k) == out.dom().contains(k)
            && (out.dom().contains(k) ==> out[k] == original[k]) by {
            assert(rec.to_imap().contains_key(k) == rec.dom().contains(k));
            if k != key && rec.dom().contains(k) {
                assert(rec.to_imap()[k] == rec[k]);
            }
        }
        assert(out.to_imap() =~= original);
        out
    }
}

} // verus!
