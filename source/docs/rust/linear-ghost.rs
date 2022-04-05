// mod pervasive; #[allow(unused_imports)] use { builtin_macros::*, builtin::*, pervasive::*, option::*, seq::*, vec::*, cell::*, modes::*, cell::*}; #[allow(unused_imports)] use pervasive::option::Option::*;

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
    #[ghost(requires, equal(self.view(), perm.pcell))]
    #[ghost(requires, perm.value.is_Some())]
    #[ghost(ensures, equal(return, perm.value.get_Some_0()))]
    pub fn borrow<'a>(&'a self, perm: ghost &'a /* ghost? */ Permission<V>) -> &'a V { ... }

    #[verifier(external_body)]
    #[ghost(requires, equal(self.view(), old(perm).pcell))]
    #[ghost(requires, old(perm).value.is_Some())]
    #[ghost(ensures, equal(perm.pcell, old(perm).pcell))]
    #[ghost(ensures, equal(perm.value, option::Option::Some(in_v)))]
    #[ghost(ensures, equal(return, old(perm).value.get_Some_0()))]
    pub fn replace(&self, #[proof] perm: ghost &mut /* ghost? */ Permission<V>, in_v: V) -> V { ... }

    ...
}

struct X { pub i: u64, }

#[verifier(external_body)]
fn release_permission(permission: ghost Permission<X>) { todo!() }

#[ghost(requires, counter.view() == old(permission).pcell)]
#[ghost(requires, old(permission).value.is_Some())]
#[ghost(requires, old(permission).value.get_Some_0().i < 100)]
#[ghost(ensures, equal(permission.pcell, old(permission).pcell))]
#[ghost(ensures, equal(permission.value, Some(X { i: old(permission).value.get_Some_0().i + 1 })))]
fn increment(
    counter: PCell<X>,
    permission: ghost &mut /* ghost? */ Permission<X>,
) {

    let cur_i: u64 = counter.borrow(/* ghost? */ permission).i;

    counter.replace(/* ghost? */ permission, X { i: cur_i + 1 });

}

#[ghost(requires, counter.view() == permission.pcell, equal(permission.value, None))]
fn start_thread(counter: PCell<X>, permission: ghost Permission<X>) {

    let mut permission /*: ghost Permission<X> */ = ghost permission;

    counter.put(/* ghost? */ &mut permission, X { i: 5 });

    #[no_borrowck] ghost {
        assert(equal(permission.value, Some(X { i : 5 })));
    }

    ghost {
        release_permission(permission);
    }

    increment(counter, ghost &mut permission);

    #[no_borrowck] ghost {
        assert(equal(permission.value, Some(X { i : 6 })));
    }
}
