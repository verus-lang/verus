#![allow(unused_imports)]

use verus_builtin::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;

verified_tokenized_state_machine! {

GenericCounter<Value> {
    fields {
        #[sharding(storage_option)]
        pub stored: Option<Value>,

        #[sharding(variable)]
        pub main_counter: Option<(nat, Value)>,

        #[sharding(multiset)]
        pub read_ref: Multiset<Value>,
    }

    init!{
        new() {
            init stored = None;
            init main_counter = None;
            init read_ref = Multiset::empty();
        }
    }

    transition!{
        writeable_to_readable(t: Value) {
            require pre.main_counter.is_none();
            update main_counter = Some((0, t));
            deposit stored += Some(t);
        }
    }

    transition!{
        readable_to_writeable() {
            require let Some((count, t)) = pre.main_counter;
            require count == 0;
            update main_counter = None;
            withdraw stored -= Some(t);
        }
    }

    transition!{
        new_ref() {
            require let Some((count, t)) = pre.main_counter;
            update main_counter = Some((count + 1, t));
            add read_ref += { t };
        }
    }

    transition!{
        delete_ref(t1: Value) {
            remove read_ref -= { t1 };
            require let Some((count, t2)) = pre.main_counter;
            assert count >= 1;
            assert t1 == t2;
            update main_counter = Some(((count - 1) as nat, t1));
        }
    }

    property!{
        compare_refs(t1: Value, t2: Value) {
            have read_ref >= { t1 };
            have read_ref >= { t2 };
            assert t1 == t2;
        }
    }

    property!{
        compare_ref_and_counter(t1: Value) {
            have read_ref >= { t1 };
            require let Some((count, t2)) = pre.main_counter;
            assert count >= 1;
            assert t1 == t2;
        }
    }

    property!{
        read_ref_guards(t: Value) {
            have read_ref >= { t };
            guard stored >= Some(t);
        }
    }

    property!{
        counter_guards() {
            require let Some((count, t)) = pre.main_counter;
            guard stored >= Some(t);
        }
    }

    #[invariant]
    pub spec fn main_inv(&self) -> bool {
        match self.stored {
            None => {
                &&& self.main_counter.is_none()
                &&& self.read_ref =~= Multiset::empty()
            }
            Some(t) => {
                match self.main_counter {
                    Some((count, t1)) => {
                        &&& t == t1
                        &&& self.read_ref.count(t) == count
                        &&& (forall |t0: Value| t0 != t ==> self.read_ref.count(t0) == 0)
                    }
                    None => false,
                }
            }
        }
    }

    #[inductive(new)]
    fn new_inductive(post: Self) { }

    #[inductive(writeable_to_readable)]
    fn writeable_to_readable_inductive(pre: Self, post: Self, t: Value) { }

    #[inductive(readable_to_writeable)]
    fn readable_to_writeable_inductive(pre: Self, post: Self) { }

    #[inductive(new_ref)]
    fn new_ref_inductive(pre: Self, post: Self) { }

    #[inductive(delete_ref)]
    fn delete_ref_inductive(pre: Self, post: Self, t1: Value) { }
}}

verus! {

tracked struct Instance<Value> {
    tracked instance: GenericCounter::Instance<Value>,
}

tracked struct MainCounter<Value> {
    tracked token: GenericCounter::main_counter<Value>,
}

tracked struct ReadRef<Value> {
    tracked token: GenericCounter::read_ref<Value>,
}

impl<Value> MainCounter<Value> {
    pub closed spec fn instance_id(self) -> vstd::resource::Loc {
        self.token.instance_id()
    }

    pub closed spec fn value(self) -> Option<(nat, Value)> {
        self.token.value()
    }
}

impl<Value> ReadRef<Value> {
    pub closed spec fn instance_id(self) -> vstd::resource::Loc {
        self.token.instance_id()
    }

    pub closed spec fn value(self) -> Value {
        self.token.element()
    }
}

impl<Value> Instance<Value> {
    pub closed spec fn id(self) -> vstd::resource::Loc {
        self.instance.id()
    }

    proof fn new() -> (tracked res: (Instance<Value>, MainCounter<Value>))
        ensures
            res.1.instance_id() == res.0.id(),
            res.1.value() == None,
    {
        let tracked (Tracked(inst), Tracked(c), Tracked(_r)) = GenericCounter::Instance::new(None);
        (Instance { instance: inst }, MainCounter { token: c })
    }

    proof fn writeable_to_readable(
        tracked &self,
        tracked counter: &mut MainCounter<Value>,
        tracked t: Value,
    )
        requires
            old(counter).instance_id() == self.id(),
            old(counter).value() == None,
        ensures
            final(counter).instance_id() == self.id(),
            final(counter).value() == Some((0, t)),
    {
        self.instance.writeable_to_readable(t, t, &mut counter.token);
    }

    proof fn readable_to_writeable(
        tracked &self,
        tracked counter: &mut MainCounter<Value>,
    ) -> (tracked t: Value)
        requires
            old(counter).instance_id() == self.id(),
            match old(counter).value() {
                None => false,
                Some((count, _)) => count == 0,
            },
        ensures
            final(counter).instance_id() == self.id(),
            final(counter).value() == None,
            t == old(counter).value().unwrap().1,
    {
        self.instance.readable_to_writeable(&mut counter.token)
    }

    proof fn new_ref(tracked &self, tracked counter: &mut MainCounter<Value>) -> (tracked read_ref:
        ReadRef<Value>)
        requires
            old(counter).instance_id() == self.id(),
            old(counter).value().is_some(),
        ensures
            final(counter).instance_id() == self.id(),
            match old(counter).value() {
                None => false,
                Some((count, t)) => final(counter).value() == Some((count + 1, t))
                    && read_ref.value() == t,
            },
    {
        ReadRef { token: self.instance.new_ref(&mut counter.token) }
    }

    proof fn delete_ref(
        tracked &self,
        tracked counter: &mut MainCounter<Value>,
        tracked read_ref: ReadRef<Value>,
    )
        requires
            old(counter).instance_id() == self.id(),
            old(counter).value().is_some(),
            read_ref.instance_id() == self.id(),
        ensures
            final(counter).instance_id() == self.id(),
            match old(counter).value() {
                None => false,
                Some((count, t)) => count >= 1 && final(counter).value() == Some(
                    ((count - 1) as nat, t),
                ),
            },
    {
        self.instance.delete_ref(read_ref.token.element(), &mut counter.token, read_ref.token)
    }

    proof fn read_ref_guards<'a>(
        tracked &self,
        tracked read_ref: &'a ReadRef<Value>,
    ) -> (tracked borrowed_t: &'a Value)
        requires
            read_ref.instance_id() == self.id(),
        ensures
            borrowed_t == read_ref.value(),
    {
        self.instance.read_ref_guards(read_ref.value(), &read_ref.token)
    }
}

} // verus!
fn main() {}
