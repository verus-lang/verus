#![allow(unused_imports)]

use verus_builtin::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;

verified_tokenized_state_machine! {

NativeCounterNames<T> {
    fields {
        #[sharding(storage_option)]
        pub __tsm_borrow_payload: Option<T>,

        #[sharding(variable)]
        pub __tsm_borrow_owner: Option<(nat, T)>,

        #[sharding(multiset)]
        pub __tsm_borrow_state: Multiset<T>,
    }

    init!{
        new() {
            init __tsm_borrow_payload = None;
            init __tsm_borrow_owner = None;
            init __tsm_borrow_state = Multiset::empty();
        }
    }

    transition!{
        writeable_to_readable(t: T) {
            require pre.__tsm_borrow_owner.is_none();
            update __tsm_borrow_owner = Some((0, t));
            deposit __tsm_borrow_payload += Some(t);
        }
    }

    transition!{
        readable_to_writeable() {
            require let Some((count, t)) = pre.__tsm_borrow_owner;
            require count == 0;
            update __tsm_borrow_owner = None;
            withdraw __tsm_borrow_payload -= Some(t);
        }
    }

    transition!{
        new_ref() {
            require let Some((count, t)) = pre.__tsm_borrow_owner;
            update __tsm_borrow_owner = Some((count + 1, t));
            add __tsm_borrow_state += { t };
        }
    }

    transition!{
        delete_ref(__tsm_borrow_left: T) {
            remove __tsm_borrow_state -= { __tsm_borrow_left };
            require let Some((count, __tsm_borrow_right)) = pre.__tsm_borrow_owner;
            assert count >= 1;
            assert __tsm_borrow_left == __tsm_borrow_right;
            update __tsm_borrow_owner = Some(((count - 1) as nat, __tsm_borrow_left));
        }
    }

    property!{
        compare_refs(__tsm_borrow_left: T, __tsm_borrow_right: T) {
            have __tsm_borrow_state >= { __tsm_borrow_left };
            have __tsm_borrow_state >= { __tsm_borrow_right };
            assert __tsm_borrow_left == __tsm_borrow_right;
        }
    }

    property!{
        compare_ref_and_counter(__tsm_borrow_left: T) {
            have __tsm_borrow_state >= { __tsm_borrow_left };
            require let Some((count, __tsm_borrow_right)) = pre.__tsm_borrow_owner;
            assert count >= 1;
            assert __tsm_borrow_left == __tsm_borrow_right;
        }
    }

    property!{
        __tsm_borrow_state_guards(t: T) {
            have __tsm_borrow_state >= { t };
            guard __tsm_borrow_payload >= Some(t);
        }
    }

    property!{
        counter_guards() {
            require let Some((count, t)) = pre.__tsm_borrow_owner;
            guard __tsm_borrow_payload >= Some(t);
        }
    }

    #[invariant]
    pub spec fn main_inv(&self) -> bool {
        match self.__tsm_borrow_payload {
            None => {
                &&& self.__tsm_borrow_owner.is_none()
                &&& self.__tsm_borrow_state =~= Multiset::empty()
            }
            Some(t) => {
                match self.__tsm_borrow_owner {
                    Some((count, __tsm_borrow_left)) => {
                        &&& t == __tsm_borrow_left
                        &&& self.__tsm_borrow_state.count(t) == count
                        &&& (forall |t0: T| t0 != t ==> self.__tsm_borrow_state.count(t0) == 0)
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
    fn delete_ref_inductive(pre: Self, post: Self, __tsm_borrow_left: T) { }
}}

verus! {

tracked struct Instance<T> {
    tracked instance: NativeCounterNames::Instance<T>,
}

tracked struct MainCounter<T> {
    tracked token: NativeCounterNames::__tsm_borrow_owner<T>,
}

tracked struct ReadRef<T> {
    tracked token: NativeCounterNames::__tsm_borrow_state<T>,
}

impl<T> MainCounter<T> {
    pub closed spec fn instance_id(self) -> vstd::resource::Loc {
        self.token.instance_id()
    }

    pub closed spec fn value(self) -> Option<(nat, T)> {
        self.token.value()
    }
}

impl<T> ReadRef<T> {
    pub closed spec fn instance_id(self) -> vstd::resource::Loc {
        self.token.instance_id()
    }

    pub closed spec fn value(self) -> T {
        self.token.element()
    }
}

impl<T> Instance<T> {
    pub closed spec fn id(self) -> vstd::resource::Loc {
        self.instance.id()
    }

    proof fn new() -> (tracked res: (Instance<T>, MainCounter<T>))
        ensures
            res.1.instance_id() == res.0.id(),
            res.1.value() == None,
    {
        let tracked (Tracked(inst), Tracked(c), Tracked(_r)) = NativeCounterNames::Instance::new(
            None,
        );
        (Instance { instance: inst }, MainCounter { token: c })
    }

    proof fn writeable_to_readable(
        tracked &self,
        tracked counter: &mut MainCounter<T>,
        tracked t: T,
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
        tracked counter: &mut MainCounter<T>,
    ) -> (tracked t: T)
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

    proof fn new_ref(
        tracked &self,
        tracked counter: &mut MainCounter<T>,
    ) -> (tracked __tsm_borrow_state: ReadRef<T>)
        requires
            old(counter).instance_id() == self.id(),
            old(counter).value().is_some(),
        ensures
            final(counter).instance_id() == self.id(),
            match old(counter).value() {
                None => false,
                Some((count, t)) => final(counter).value() == Some((count + 1, t))
                    && __tsm_borrow_state.value() == t,
            },
    {
        ReadRef { token: self.instance.new_ref(&mut counter.token) }
    }

    proof fn delete_ref(
        tracked &self,
        tracked counter: &mut MainCounter<T>,
        tracked __tsm_borrow_state: ReadRef<T>,
    )
        requires
            old(counter).instance_id() == self.id(),
            old(counter).value().is_some(),
            __tsm_borrow_state.instance_id() == self.id(),
        ensures
            final(counter).instance_id() == self.id(),
            match old(counter).value() {
                None => false,
                Some((count, t)) => count >= 1 && final(counter).value() == Some(
                    ((count - 1) as nat, t),
                ),
            },
    {
        self.instance.delete_ref(
            __tsm_borrow_state.token.element(),
            &mut counter.token,
            __tsm_borrow_state.token,
        )
    }

    proof fn __tsm_borrow_state_guards<'a>(
        tracked &self,
        tracked __tsm_borrow_state: &'a ReadRef<T>,
    ) -> (tracked borrowed_t: &'a T)
        requires
            __tsm_borrow_state.instance_id() == self.id(),
        ensures
            borrowed_t == __tsm_borrow_state.value(),
    {
        self.instance.__tsm_borrow_state_guards(
            __tsm_borrow_state.value(),
            &__tsm_borrow_state.token,
        )
    }
}

} // verus!
fn main() {}
