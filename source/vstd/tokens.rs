//// ValueToken - for variable, option, persistent_option

use super::prelude::*;
use super::multiset::*;
use core::marker::PhantomData;

verus!{

#[verusfmt::skip]
broadcast use
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms,
    super::map::group_map_axioms;

pub ghost struct InstanceId(pub int);

pub trait ValueToken<Value> {
    spec fn instance(&self) -> InstanceId;
    spec fn value(&self) -> Value;

    proof fn agree(tracked &self, tracked other: &Self)
        requires self.instance() == other.instance(),
        ensures self.value() == other.value();
}

pub trait UniqueValueToken<Value> : ValueToken<Value> {
    proof fn unique(tracked &mut self, tracked other: &Self)
        ensures self.instance() != other.instance();
}

//pub trait PersistentValueToken<Value> : ValueToken<Value> + Copy {
//}

pub trait KeyValueToken<Key, Value> {
    spec fn instance(&self) -> InstanceId;
    spec fn key(&self) -> Key;
    spec fn value(&self) -> Value;

    proof fn agree(tracked &self, tracked other: &Self)
        requires self.instance() == other.instance(),
                 self.key() == other.key(),
        ensures self.value() == other.value();
}

pub trait UniqueKeyValueToken<Key, Value> : KeyValueToken<Key, Value> {
    proof fn unique(tracked &mut self, tracked other: &Self)
        ensures self.instance() != other.instance()
            || self.key() != other.key();
}

//pub trait PersistentKeyValueToken<Key, Value> : KeyValueToken<Key, Value> + Copy {
//}

pub trait CountToken : Sized {
    spec fn instance(&self) -> InstanceId;
    spec fn count(&self) -> nat;

    proof fn join(tracked &mut self, tracked other: Self)
        requires
            old(self).instance() == other.instance(),
        ensures
            self.instance() == old(self).instance(),
            self.count() == old(self).count() + other.count();

    proof fn split(tracked &mut self, count: nat) -> (tracked token: Self)
        requires
            count <= old(self).count()
        ensures
            self.instance() == old(self).instance(),
            self.count() == old(self).count() - count,
            token.instance() == old(self).instance(),
            token.count() == count;
}

pub trait MonotonicCountToken : Sized {
    spec fn instance(&self) -> InstanceId;
    spec fn count(&self) -> nat;
}

pub trait ElementToken<Element> {
    spec fn instance(&self) -> InstanceId;
    spec fn element(&self) -> Element;
}

pub trait UniqueElementToken<Element> : ElementToken<Element> {
    proof fn unique(tracked &mut self, tracked other: &Self)
        ensures self.instance() == other.instance()
            ==> self.element() != other.element();
}

pub trait SimpleToken {
    spec fn instance(&self) -> InstanceId;
}

pub trait UniqueSimpleToken<Element> : ElementToken<Element> {
    proof fn unique(tracked &mut self, tracked other: &Self)
        ensures self.instance() != other.instance();
}

#[verifier::reject_recursive_types(Key)]
tracked struct MapToken<Key, Value, Token>
    where Token: KeyValueToken<Key, Value>
{
    ghost _v: PhantomData<Value>,
    ghost inst: InstanceId,
    tracked m: Map<Key, Token>,
}

impl<Key, Value, Token> MapToken<Key, Value, Token>
    where Token: KeyValueToken<Key, Value>
{
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        forall |k| #[trigger] self.m.dom().contains(k) ==> self.m[k].key() == k
            && self.m[k].instance() == self.inst
    }

    pub closed spec fn instance(self) -> InstanceId {
        self.inst
    }

    pub closed spec fn map(self) -> Map<Key, Value> {
        Map::new(
            |k: Key| self.m.dom().contains(k),
            |k: Key| self.m[k].value(),
        )
    }

    proof fn empty(instance: InstanceId) -> (tracked s: Self)
        ensures
            s.instance() == instance,
            s.map() === Map::empty(),
    {
        let tracked s = Self { inst: instance, m: Map::tracked_empty(), _v: PhantomData };
        assert(s.map() =~= Map::empty());
        return s;
    }

    proof fn insert(tracked &mut self, tracked token: Token)
        requires
            old(self).instance() == token.instance(),
        ensures
            self.instance() == old(self).instance(),
            self.map() == old(self).map().insert(token.key(), token.value()),
    {
        use_type_invariant(&*self);
        self.m.tracked_insert(token.key(), token);
        assert(self.map() =~= old(self).map().insert(token.key(), token.value()));
    }

    proof fn remove(tracked &mut self, key: Key) -> (tracked token: Token)
        requires
            old(self).map().dom().contains(key)
        ensures
            self.instance() == old(self).instance(),
            self.map() == old(self).map().remove(key),
            token.instance() == self.instance(),
            token.key() == key,
            token.value() == old(self).map()[key]
    {
        use_type_invariant(&*self);
        let tracked t = self.m.tracked_remove(key);
        assert(self.map() =~= old(self).map().remove(key));
        t
    }

    proof fn into_map(tracked self) -> (tracked map: Map<Key, Token>)
        ensures
            map.dom() == self.map().dom(),
            forall |key| #[trigger] map.dom().contains(key)
                ==> map[key].instance() == self.instance()
                 && map[key].key() == key
                 && map[key].value() == self.map()[key]
    {
        use_type_invariant(&self);
        let tracked MapToken { inst, m, _v } = self;
        assert(m.dom() =~= self.map().dom());
        return m;
    }

    proof fn from_map(instance: InstanceId, tracked map: Map<Key, Token>) -> (s: Self)
        requires
            forall |key| #[trigger] map.dom().contains(key) ==> map[key].instance() == instance,
            forall |key| #[trigger] map.dom().contains(key) ==> map[key].key() == key,
        ensures
            map.dom() == s.map().dom(),
            forall |key| #[trigger] map.dom().contains(key)
                ==> map[key].instance() == s.instance()
                 && map[key].key() == key
                 && map[key].value() == s.map()[key]
    {
        let tracked s = MapToken { inst: instance, m: map, _v: PhantomData };
        assert(map.dom() == s.map().dom());
        s
    }
}

#[verifier::reject_recursive_types(Element)]
tracked struct SetToken<Element, Token>
    where Token: ElementToken<Element>
{
    ghost inst: InstanceId,
    tracked m: Map<Element, Token>,
}

impl<Element, Token> SetToken<Element, Token>
    where Token: ElementToken<Element>
{
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        forall |k| #[trigger] self.m.dom().contains(k) ==> self.m[k].element() == k
            && self.m[k].instance() == self.inst
    }

    pub closed spec fn instance(self) -> InstanceId {
        self.inst
    }

    pub closed spec fn set(self) -> Set<Element> {
        Set::new(
            |e: Element| self.m.dom().contains(e),
        )
    }

    proof fn empty(instance: InstanceId) -> (tracked s: Self)
        ensures
            s.instance() == instance,
            s.set() === Set::empty(),
    {
        let tracked s = Self { inst: instance, m: Map::tracked_empty() };
        assert(s.set() =~= Set::empty());
        return s;
    }

    proof fn insert(tracked &mut self, tracked token: Token)
        requires
            old(self).instance() == token.instance(),
        ensures
            self.instance() == old(self).instance(),
            self.set() == old(self).set().insert(token.element()),
    {
        use_type_invariant(&*self);
        self.m.tracked_insert(token.element(), token);
        assert(self.set() =~= old(self).set().insert(token.element()));
    }

    proof fn remove(tracked &mut self, element: Element) -> (tracked token: Token)
        requires
            old(self).set().contains(element)
        ensures
            self.instance() == old(self).instance(),
            self.set() == old(self).set().remove(element),
            token.instance() == self.instance(),
            token.element() == element,
    {
        use_type_invariant(&*self);
        let tracked t = self.m.tracked_remove(element);
        assert(self.set() =~= old(self).set().remove(element));
        t
    }
}

tracked struct MultisetToken<Element, Token>
    where Token: ElementToken<Element>
{
    ghost _v: PhantomData<Element>,
    ghost inst: InstanceId,
    tracked m: Map<int, Token>,
}

spec fn map_values<K, V>(m: Map<K, V>) -> Multiset<V> {
    m.dom().fold(Multiset::empty(), |multiset: Multiset<V>, k: K| multiset.insert(m[k]))
}

proof fn map_values_insert_not_in<K, V>(m: Map<K, V>, k: K, v: V)
    requires
        !m.dom().contains(k)
    ensures
        map_values(m.insert(k, v)) == map_values(m).insert(v)
{
    assume(false);
}

proof fn map_values_remove<K, V>(m: Map<K, V>, k: K)
    requires
        m.dom().contains(k)
    ensures
        map_values(m.remove(k)) == map_values(m).remove(m[k])
{
    assume(false);
}

//proof fn map_values_empty_empty<K, V>()
//    ensures map_values(Map::<K, V>::empty()) == Multiset::empty(),

spec fn fresh(m: Set<int>) -> int {
    m.find_unique_maximal(|a: int, b: int| a <= b) + 1
}

proof fn fresh_is_fresh(s: Set<int>)
    requires s.finite(),
    ensures !s.contains(fresh(s))
{
    assume(false);
}

proof fn get_key_for_value<K, V>(m: Map<K, V>, value: V) -> (k: K)
    requires map_values(m).contains(value), m.dom().finite(),
    ensures m.dom().contains(k), m[k] == value,
{
    assume(false);
    arbitrary()
}

impl<Element, Token> MultisetToken<Element, Token>
    where Token: ElementToken<Element>
{
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        self.m.dom().finite() &&
        forall |k| #[trigger] self.m.dom().contains(k)
            ==> self.m[k].instance() == self.inst
    }

    pub closed spec fn instance(self) -> InstanceId {
        self.inst
    }

    spec fn map_elems(m: Map<int, Token>) -> Map<int, Element> {
        m.map_values(|t: Token| t.element())
    }

    pub closed spec fn multiset(self) -> Multiset<Element> {
        map_values(Self::map_elems(self.m))
    }

    proof fn empty(instance: InstanceId) -> (tracked s: Self)
        ensures
            s.instance() == instance,
            s.multiset() === Multiset::empty(),
    {
        let tracked s = Self { inst: instance, m: Map::tracked_empty(), _v: PhantomData, };
        assert(Self::map_elems(Map::empty()) =~= Map::empty());
        return s;
    }

    proof fn insert(tracked &mut self, tracked token: Token)
        requires
            old(self).instance() == token.instance(),
        ensures
            self.instance() == old(self).instance(),
            self.multiset() == old(self).multiset().insert(token.element()),
    {
        use_type_invariant(&*self);
        let f = fresh(self.m.dom());
        fresh_is_fresh(self.m.dom());
        map_values_insert_not_in(
            Self::map_elems(self.m),
            f,
            token.element());
        self.m.tracked_insert(f, token);
        assert(Self::map_elems(self.m) =~= Self::map_elems(old(self).m).insert(
            f, token.element()));
        assert(self.multiset() =~= old(self).multiset().insert(token.element()));
    }

    proof fn remove(tracked &mut self, element: Element) -> (tracked token: Token)
        requires
            old(self).multiset().contains(element)
        ensures
            self.instance() == old(self).instance(),
            self.multiset() == old(self).multiset().remove(element),
            token.instance() == self.instance(),
            token.element() == element,
    {
        use_type_invariant(&*self);
        assert(Self::map_elems(self.m).dom() =~= self.m.dom());
        let k = get_key_for_value(Self::map_elems(self.m), element);
        map_values_remove(Self::map_elems(self.m), k);
        let tracked t = self.m.tracked_remove(k);
        assert(Self::map_elems(self.m) =~= Self::map_elems(old(self).m).remove(k));
        assert(self.multiset() =~= old(self).multiset().remove(element));
        t
    }
}

pub open spec fn option_value_eq_option_token<Value, Token: ValueToken<Value>>(
    opt_value: Option<Value>,
    opt_token: Option<Token>,
    inst: InstanceId,
) -> bool {
    match opt_value {
        Some(val) => opt_token.is_some()
            && opt_token.unwrap().value() == val,
            && opt_token.unwrap().instance() == inst,
        None => opt_token.is_none(),
    }
}

pub open spec fn option_value_le_option_token<Value, Token: ValueToken<Value>>(
    opt_value: Option<Value>,
    opt_token: Option<Token>,
    inst: InstanceId,
) -> bool {
    match opt_value {
        Some(val) => opt_token.is_some()
            && opt_token.unwrap().value() == val,
            && opt_token.unwrap().instance() == inst,
        None => true,
    }
}

pub open spec fn bool_value_eq_option_token<Token: SimpleToken>(
    b: bool,
    opt_token: Option<Token>,
    inst: InstanceId,
) -> bool {
    if b {
        opt_token.is_some() && opt_token.unwrap().instance() == inst,
    } else {
        opt_token.is_none()
    }
}

pub open spec fn bool_value_le_option_token<Token: SimpleToken>(
    b: bool,
    opt_token: Option<Token>,
    inst: InstanceId,
) -> bool {
    b ==>
        opt_token.is_some() && opt_token.unwrap().instance() == inst,
}

}
