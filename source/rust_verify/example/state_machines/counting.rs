#![allow(unused_imports)]

use builtin::*;
use vstd::prelude::*;
use vstd::multiset::*;
use state_machines_macros::tokenized_state_machine;

tokenized_state_machine!{ CountingPermissions<T> {
    fields {
        #[sharding(storage_option)]
        pub stored: Option<T>,

        #[sharding(variable)]
        pub main_counter: Option<(nat, T)>,

        #[sharding(multiset)]
        pub read_ref: Multiset<T>,
    }

    init!{
        new() {
            init stored = None;
            init main_counter = None;
            init read_ref = Multiset::empty();
        }
    }

    transition!{
        writeable_to_readable(t: T) {
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
        delete_ref(t1: T) {
            remove read_ref -= { t1 };
            require let Some((count, t2)) = pre.main_counter;
            assert count >= 1;
            assert t1 == t2;
            update main_counter = Some(((count - 1) as nat, t1));
        }
    }

    property!{
        compare_refs(t1: T, t2: T) {
            have read_ref >= { t1 };
            have read_ref >= { t2 };
            assert t1 == t2;
        }
    }

    property!{
        compare_ref_and_counter(t1: T) {
            have read_ref >= { t1 };
            require let Some((count, t2)) = pre.main_counter;
            assert count >= 1;
            assert t1 == t2;
        }
    }

    property!{
        read_ref_guards(t: T) {
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
                        &&& (forall |t0: T| t0 != t ==> self.read_ref.count(t0) == 0)
                    }
                    None => false,
                }
            }
        }
    }

    #[inductive(new)]
    fn new_inductive(post: Self) { }
   
    #[inductive(writeable_to_readable)]
    fn writeable_to_readable_inductive(pre: Self, post: Self, t: T) { }
   
    #[inductive(readable_to_writeable)]
    fn readable_to_writeable_inductive(pre: Self, post: Self) { }
   
    #[inductive(new_ref)]
    fn new_ref_inductive(pre: Self, post: Self) { }
   
    #[inductive(delete_ref)]
    fn delete_ref_inductive(pre: Self, post: Self, t1: T) { }
}}

verus!{

tracked struct Instance<T> {
    tracked instance: CountingPermissions::Instance<T>,
}

tracked struct MainCounter<T> {
    tracked token: CountingPermissions::main_counter<T>,
}

tracked struct ReadRef<T> {
    tracked token: CountingPermissions::read_ref<T>
}

impl<T> MainCounter<T> {
    pub closed spec fn instance(self) -> Instance<T> {
        Instance { instance: self.token@.instance }
    }

    pub closed spec fn value(self) -> Option<(nat, T)> {
        self.token@.value
    }
}

impl<T> ReadRef<T> {
    pub closed spec fn instance(self) -> Instance<T> {
        Instance { instance: self.token@.instance }
    }

    pub closed spec fn value(self) -> T {
        self.token@.key
    }

    pub closed spec fn wf(self) -> bool {
        self.token@.count == 1
    }
}

impl<T> Instance<T> {
    proof fn new() -> (tracked res: (Instance<T>, MainCounter<T>))
        ensures
            res.1.instance() == res.0,
            res.1.value() === None
    {
        let tracked (Tracked(inst), Tracked(c), Tracked(_r)) =
            CountingPermissions::Instance::new(None);
        (Instance { instance: inst }, MainCounter { token: c })
    }

    proof fn writeable_to_readable(
        tracked &self,
        tracked counter: &mut MainCounter<T>,
        tracked t: T
    )
        requires
            old(counter).instance() == self,
            old(counter).value() === None,
        ensures
            counter.instance() == self,
            counter.value() === Some((0, t)),
    {
        self.instance.writeable_to_readable(t, t, &mut counter.token);
    }

    proof fn readable_to_writeable(
        tracked &self,
        tracked counter: &mut MainCounter<T>,
    ) -> (tracked t: T)
        requires
            old(counter).instance() == self,
            match old(counter).value() {
                None => false,
                Some((count, _)) => count == 0,
            }
        ensures
            counter.instance() == self,
            counter.value() === None,
            t == old(counter).value().unwrap().1,
    {
        self.instance.readable_to_writeable(&mut counter.token)
    }

    proof fn new_ref(
        tracked &self,
        tracked counter: &mut MainCounter<T>,
    ) -> (tracked read_ref: ReadRef<T>)
        requires
            old(counter).instance() == self,
            old(counter).value().is_some()
        ensures
            counter.instance() == self,
            match old(counter).value() {
                None => false,
                Some((count, t)) =>
                    counter.value() == Some((count + 1, t))
                      && read_ref.value() == t
            },
            read_ref.wf(),
    {
        ReadRef { token: self.instance.new_ref(&mut counter.token) }
    }

    proof fn delete_ref(
        tracked &self,
        tracked counter: &mut MainCounter<T>,
        tracked read_ref: ReadRef<T>,
    )
        requires
            old(counter).instance() == self,
            old(counter).value().is_some(),
            read_ref.instance() == self,
            read_ref.wf(),
        ensures
            counter.instance() == self,
            match old(counter).value() {
                None => false,
                Some((count, t)) =>
                    count >= 1
                      && counter.value() == Some(((count - 1) as nat, t))
            },
    {
        self.instance.delete_ref(read_ref.token@.key, &mut counter.token, read_ref.token)
    }

    proof fn read_ref_guards<'a>(
        tracked &self,
        tracked read_ref: &'a ReadRef<T>,
    ) -> (tracked borrowed_t: &'a T)
        requires read_ref.wf(),
            read_ref.instance() == self,
        ensures
            borrowed_t == read_ref.value()
    {
        self.instance.read_ref_guards(read_ref.value(), &read_ref.token)
    }
}

}

fn main() { }
