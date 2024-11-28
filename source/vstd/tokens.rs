//// ValueToken - for variable, option, persistent_option

use vstd::prelude::*;
use core::marker::PhantomData;

verus!{

ghost struct InstanceId(pub int);

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

pub trait CountToken {
    spec fn instance() -> InstanceId;
    spec fn count() -> nat;

    proof fn join(tracked &self, tracked other: Self);
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
            forall |key| map.dom().contains(key) ==> map[key].instance() == instance,
            forall |key| map.dom().contains(key) ==> map[key].key() == key,
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

}
