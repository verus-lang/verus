// mod pervasive; #[allow(unused_imports)] use { builtin_macros::*, builtin::*, pervasive::*, option::*, seq::*, vec::*, cell::*, modes::*, cell::*}; #[allow(unused_imports)] use vstd::option::Option::*;

// Further experimentation at https://gist.github.com/utaal/aba64ad723c65068247af00c63756e10

#[verifier(external_body)]
pub struct PCell<#[verifier(strictly_positive)] V> {
    ucell: UnsafeCell<MaybeUninit<V>>,
}

#[verifier(unforgeable)]
pub struct Permission<V> {
    pub pcell: ghost int,
    pub value: ghost Option<V>,
}

impl<V> PCell<V> {
    pub fn view(&self) -> int { uninterpreted!() }

    #[verifier(external_body)]
    #[ghost(requires, equal(self.view(), (raise perm).pcell))]
    #[ghost(requires, (raise perm).value.is_Some())]
    #[ghost(ensures, equal(return, (raise perm).value.get_Some_0()))]
    pub fn borrow<'a>(&'a self, perm: ghost &'a Permission<V>) -> &'a V { ... }

    #[verifier(external_body)]
    #[ghost(requires, equal(self.view(), old(raise perm).pcell))]
    #[ghost(requires, old(raise perm).value.is_Some())]
    #[ghost(ensures, equal((raise perm).pcell, old(raise perm).pcell))]
    #[ghost(ensures, equal((raise perm).value, option::Option::Some(in_v)))]
    #[ghost(ensures, equal(return, old(raise perm).value.get_Some_0()))]
    pub fn replace(&self, perm: ghost &mut Permission<V>, in_v: V) -> V { ... }

    ...
}

struct X { pub i: u64, }

#[verifier(external_body)]
fn release_permission(perm: ghost Permission<X>) { todo!() }

#[ghost(requires, counter.view() == old(raise perm).pcell)]
#[ghost(requires, old(raise perm).value.is_Some())]
#[ghost(requires, old(raise perm).value.get_Some_0().i < 100)]
#[ghost(ensures, equal((raise perm).pcell, old(raise perm).pcell))]
#[ghost(ensures, equal((raise perm).value, Some(X { i: old(raise perm).value.get_Some_0().i + 1 })))]
fn increment(
    counter: PCell<X>,
    perm: ghost &mut Permission<X>,
) {

    let cur_i: u64 = counter.borrow(ghost { permission }).i;

    counter.replace(ghost { permission }, X { i: cur_i + 1 });

}

#[ghost(requires, counter.view() == permission.pcell, equal(permission.value, None))]
fn start_thread(counter: PCell<X>, permission: ghost Permission<X>) {

    let mut permission: ghost Permission<X> = ghost { permission };

    counter.put(ghost { &mut raise permission }, X { i: 5 });

    #[no_borrowck] ghost {
        assert(equal((raise permission).value, Some(X { i : 5 })));
    }

    ghost {
        release_permission(permission);
    }

    increment(counter, ghost { &mut raise permission });

    #[no_borrowck] ghost {
        assert(equal((raise permission).value, Some(X { i : 6 })));
    }
}
