//// ValueToken - for variable, option, persistent_option

pub trait ValueToken<Instance, Value> {
    spec fn instance() -> Instance;
    spec fn value() -> Value;

    proof fn agree(tracked &self, tracked other: &Self)
        requires self.instance() == other.instance(),
        ensures self.value() == other.value();
}

pub trait UniqueValueToken<Instance, Value> : ValueToken<Instance, Value> {
    proof fn unique(tracked &mut self, tracked other: &Self)
        ensures self.instance() != other.instance();
}

pub trait PersistentValueToken<Instance, Value> : ValueToken<Instance, Value> + Copy {
}

pub trait KeyValueToken<Instance, Key, Value> {
    spec fn instance() -> Instance;
    spec fn key() -> Key;
    spec fn value() -> Value;

    proof fn agree(tracked &self, tracked other: &Self)
        requires self.instance() == other.instance(),
                 self.key() == other.key(),
        ensures self.value() == other.value();
}

pub trait UniqueKeyValueToken<Instance, Key, Value> : KeyValueToken<Instance, Key, Value> {
    proof fn unique(tracked &mut self, tracked other: &Self)
        ensures self.instance() != other.instance()
            || self.key() != other.key();
}

pub trait PersistentKeyValueToken<Instance, Key, Value> : KeyValueToken<Instance, Key, Value> + Copy {
}

tracked struct MapToken<Instance, K, V, Token> {
    ghost inst: Instance,
    tracked m: Map<K, Token>,
}

impl<Instance, Key, Value, Token> MapToken<Instance, K, V, Token>
    where Token: KeyValueToken<Instance, Key, Value>
{
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        forall |k| self.m.dom().contains(k) ==> self.m[k].key() == k
    }

    pub closed spec fn instance(self) -> Instance {
        self.inst
    }

    pub closed spec fn map(self) -> Map<K, V> {
        Map::new(
            |k: Key| self.m.dom().contains(k),
            |k: Key| self.m[k].value(),
        )
    }

    fn empty(instance: Instance) -> (s: Self)
        ensures
            s.instance() == instance,
            s.map() === Map::empty(),
    {
        Self { inst: instance, m: Map::empty() }
    }
}
