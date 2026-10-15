//! Complete refutable-binding case, with an exact tagged physical store.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;
use vstd::{imap::*, iset::*, map::*, modes::*, pervasive::*, set::*};

verus! {

pub enum Goo {
    Bar,
    Qux(u64),
    Tal(u64, u64),
}

} // verus!
verified_state_machine_model! { Y {
    fields {
        #[sharding(imap)]
        pub m: IMap<int, Goo>,

        #[sharding(storage_imap)]
        pub storage_m: IMap<int, Goo>,

        #[sharding(option)]
        pub opt: Option<Goo>,

        #[sharding(storage_option)]
        pub storage_opt: Option<Goo>,
    }

    init!{
        initialize(m: IMap<int, Goo>, opt: Option<Goo>) {
            init m = m;
            init storage_m = m;
            init opt = opt;
            init storage_opt = opt;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, m: IMap<int, Goo>, opt: Option<Goo>) { }

    transition!{
        tr1() {
            remove opt -= Some(let Goo::Bar);
            withdraw storage_opt -= Some(let Goo::Bar);
        }
    }

    transition!{
        tr2() {
            remove opt -= Some(let Goo::Qux(i1));
            withdraw storage_opt -= Some(let Goo::Qux(j1));
            assert(i1 == j1);
        }
    }

    transition!{
        tr3() {
            remove opt -= Some(let Goo::Tal(i1, i2));
            withdraw storage_opt -= Some(let Goo::Tal(j1, j2));
            assert(i1 == j1);
            assert(i2 == j2);
        }
    }

    transition!{
        tr4(key: int) {
            remove m -= [key => let Goo::Bar];
            withdraw storage_m -= [key => let Goo::Bar];
        }
    }

    transition!{
        tr5(key: int) {
            remove m -= [key => let Goo::Qux(i1)];
            withdraw storage_m -= [key => let Goo::Qux(j1)];
            assert(i1 == j1);
        }
    }

    transition!{
        tr6(key: int) {
            remove m -= [key => let Goo::Tal(i1, i2)];
            withdraw storage_m -= [key => let Goo::Tal(j1, j2)];
            assert(i1 == j1);
            assert(i2 == j2);
        }
    }

    transition!{
        tr7(key: int) {
            have opt >= Some(let Goo::Bar);
            have m >= [key => let Goo::Bar];
        }
    }

    transition!{
        tr8(key: int) {
            have opt >= Some(let Goo::Qux(i1));
            have m >= [key => let Goo::Qux(j1)];
            require(i1 == j1);
        }
    }

    transition!{
        tr9(key: int) {
            have opt >= Some(let Goo::Tal(i1, i2));
            have m >= [key => let Goo::Tal(j1, j2)];
            require(i1 == j1);
            require(i2 == j2);
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        equal(self.m, self.storage_m)
        && equal(self.opt, self.storage_opt)
    }

        #[inductive(tr1)]
        fn tr1_inductive(pre: Self, post: Self) { }

        #[inductive(tr2)]
        fn tr2_inductive(pre: Self, post: Self) { }

        #[inductive(tr3)]
        fn tr3_inductive(pre: Self, post: Self) { }

        #[inductive(tr4)]
        fn tr4_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr5)]
        fn tr5_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr6)]
        fn tr6_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr7)]
        fn tr7_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr8)]
        fn tr8_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr9)]
        fn tr9_inductive(pre: Self, post: Self, key: int) { }
}}
verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Bar) => {
            match pre.storage_opt {
                Option::Some(Goo::Bar) => {
                    equal(post.opt, Option::None) && equal(post.storage_opt, Option::None) && equal(
                        post.m,
                        pre.m,
                    ) && equal(post.storage_m, pre.storage_m)
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Bar) => {
            match pre.storage_opt {
                Option::Some(Goo::Bar) => {
                    equal(post.opt, Option::None) && equal(post.storage_opt, Option::None) && equal(
                        post.m,
                        pre.m,
                    ) && equal(post.storage_m, pre.storage_m)
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Qux(i1)) => {
            match pre.storage_opt {
                Option::Some(Goo::Qux(j1)) => {
                    (i1 == j1) ==> {
                        &&& post.opt == Option::None
                        &&& post.storage_opt == Option::None
                        &&& post.m == pre.m
                        &&& post.storage_m == pre.storage_m
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Qux(i1)) => {
            match pre.storage_opt {
                Option::Some(Goo::Qux(j1)) => {
                    &&& i1 == j1
                    &&& post.opt == Option::None
                    &&& post.storage_opt == Option::None
                    &&& post.m == pre.m
                    &&& post.storage_m == pre.storage_m
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Tal(i1, i2)) => {
            match pre.storage_opt {
                Option::Some(Goo::Tal(j1, j2)) => {
                    (i1 == j1 && i2 == j2) ==> {
                        &&& post.opt == Option::None
                        &&& post.storage_opt == Option::None
                        &&& post.m == pre.m
                        &&& post.storage_m == pre.storage_m
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Tal(i1, i2)) => {
            match pre.storage_opt {
                Option::Some(Goo::Tal(j1, j2)) => {
                    &&& i1 == j1 && i2 == j2
                    &&& post.opt == Option::None
                    &&& post.storage_opt == Option::None
                    &&& post.m == pre.m
                    &&& post.storage_m == pre.storage_m
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr4(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Bar => {
            pre.storage_m.dom().contains(key) ==> match pre.storage_m.index(key) {
                Goo::Bar => {
                    &&& post.opt == pre.opt
                    &&& post.storage_opt == pre.storage_opt
                    &&& post.m == pre.m.remove(key)
                    &&& post.storage_m == pre.storage_m.remove(key)
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Bar => {
            pre.storage_m.dom().contains(key) && match pre.storage_m.index(key) {
                Goo::Bar => {
                    &&& post.opt == pre.opt
                    &&& post.storage_opt == pre.storage_opt
                    &&& post.m == pre.m.remove(key)
                    &&& post.storage_m == pre.storage_m.remove(key)
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr5(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Qux(i1) => {
            pre.storage_m.dom().contains(key) ==> match pre.storage_m.index(key) {
                Goo::Qux(j1) => {
                    (i1 == j1) ==> {
                        &&& post.opt == pre.opt
                        &&& post.storage_opt == pre.storage_opt
                        &&& post.m == pre.m.remove(key)
                        &&& post.storage_m == pre.storage_m.remove(key)
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr5_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Qux(i1) => {
            pre.storage_m.dom().contains(key) && match pre.storage_m.index(key) {
                Goo::Qux(j1) => {
                    &&& i1 == j1
                    &&& post.opt == pre.opt
                    &&& post.storage_opt == pre.storage_opt
                    &&& post.m == pre.m.remove(key)
                    &&& post.storage_m == pre.storage_m.remove(key)
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr6(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Tal(i1, i2) => {
            pre.storage_m.dom().contains(key) ==> match pre.storage_m.index(key) {
                Goo::Tal(j1, j2) => {
                    (i1 == j1 && i2 == j2) ==> {
                        &&& post.opt == pre.opt
                        &&& post.storage_opt == pre.storage_opt
                        &&& post.m == pre.m.remove(key)
                        &&& post.storage_m == pre.storage_m.remove(key)
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr6_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Tal(i1, i2) => {
            pre.storage_m.dom().contains(key) && match pre.storage_m.index(key) {
                Goo::Tal(j1, j2) => {
                    i1 == j1 && i2 == j2 && equal(post.opt, pre.opt) && equal(
                        post.storage_opt,
                        pre.storage_opt,
                    ) && equal(post.m, pre.m.remove(key)) && equal(
                        post.storage_m,
                        pre.storage_m.remove(key),
                    )
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr7(pre: Y::State, post: Y::State, key: int) -> bool {
    match pre.opt {
        Option::Some(Goo::Bar) => {
            pre.m.dom().contains(key) && match pre.m.index(key) {
                Goo::Bar => equal(post, pre),
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr7_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    rel_tr7(pre, post, key)
}

spec fn rel_tr8(pre: Y::State, post: Y::State, key: int) -> bool {
    match pre.opt {
        Option::Some(Goo::Qux(i1)) => {
            pre.m.dom().contains(key) && match pre.m.index(key) {
                Goo::Qux(j1) => i1 == j1 && equal(post, pre),
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr8_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    rel_tr8(pre, post, key)
}

spec fn rel_tr9(pre: Y::State, post: Y::State, key: int) -> bool {
    match pre.opt {
        Option::Some(Goo::Tal(i1, i2)) => {
            pre.m.dom().contains(key) && match pre.m.index(key) {
                Goo::Tal(j1, j2) => i1 == j1 && i2 == j2 && equal(post, pre),
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr9_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    rel_tr9(pre, post, key)
}

proof fn correct_tr(pre: Y::State, post: Y::State, key: int) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr1(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr2(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
            rel_tr3(pre, post) == Y::State::tr3(pre, post),
            rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
            rel_tr4(pre, post, key) == Y::State::tr4(pre, post, key),
            rel_tr4_strong(pre, post, key) == Y::State::tr4_strong(pre, post, key),
            rel_tr5(pre, post, key) == Y::State::tr5(pre, post, key),
            rel_tr5_strong(pre, post, key) == Y::State::tr5_strong(pre, post, key),
            rel_tr6(pre, post, key) == Y::State::tr6(pre, post, key),
            rel_tr6_strong(pre, post, key) == Y::State::tr6_strong(pre, post, key),
            rel_tr7(pre, post, key) == Y::State::tr7(pre, post, key),
            rel_tr7_strong(pre, post, key) == Y::State::tr7_strong(pre, post, key),
            rel_tr8(pre, post, key) == Y::State::tr8(pre, post, key),
            rel_tr8_strong(pre, post, key) == Y::State::tr8_strong(pre, post, key),
            rel_tr9(pre, post, key) == Y::State::tr9(pre, post, key),
            rel_tr9_strong(pre, post, key) == Y::State::tr9_strong(pre, post, key),
        ],
    );
}

} // verus!
verus! {

broadcast use {
    vstd::map::group_map_lemmas,
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
};

pub ghost enum StorageKey {
    MapKey(int),
    Optional,
}

pub open spec fn packed(m: IMap<int, Goo>, opt: Option<Goo>) -> IMap<StorageKey, Goo> {
    let entries = m;
    IMap::new(
        |tag: StorageKey|
            match tag {
                StorageKey::MapKey(k) => entries.dom().contains(k),
                StorageKey::Optional => opt is Some,
            },
        |tag: StorageKey|
            match tag {
                StorageKey::MapKey(k) => entries[k],
                StorageKey::Optional => opt->Some_0,
            },
    )
}

pub proof fn packed_map_at(m: IMap<int, Goo>, opt: Option<Goo>, key: int)
    ensures
        packed(m, opt).dom().contains(StorageKey::MapKey(key)) == m.dom().contains(key),
        m.dom().contains(key) ==> packed(m, opt)[StorageKey::MapKey(key)] == m[key],
{
}

pub proof fn packed_option_at(m: IMap<int, Goo>, opt: Option<Goo>)
    ensures
        packed(m, opt).dom().contains(StorageKey::Optional) == (opt is Some),
        opt is Some ==> packed(m, opt)[StorageKey::Optional] == opt->Some_0,
{
}

pub proof fn remove_optional_store(m: IMap<int, Goo>, opt: Option<Goo>)
    ensures
        packed(m, None) == packed(m, opt).remove(StorageKey::Optional),
{
    let remaining = packed(m, opt).remove(StorageKey::Optional);
    let empty_optional = packed(m, None);
    assert forall|tag: StorageKey|
        empty_optional.dom().contains(tag) == remaining.dom().contains(tag) by {
        match tag {
            StorageKey::MapKey(k) => {
                packed_map_at(m, None, k);
                packed_map_at(m, opt, k);
            },
            StorageKey::Optional => {
                packed_option_at(m, None);
                packed_option_at(m, opt);
            },
        }
    }
    assert forall|tag: StorageKey| empty_optional.dom().contains(tag) implies empty_optional[tag]
        == remaining[tag] by {
        match tag {
            StorageKey::MapKey(k) => {
                packed_map_at(m, None, k);
                packed_map_at(m, opt, k);
            },
            StorageKey::Optional => {
                packed_option_at(m, None);
                assert(false);
            },
        }
    }
    assert(empty_optional =~= remaining);
}

pub proof fn remove_map_store(m: IMap<int, Goo>, opt: Option<Goo>, key: int)
    ensures
        packed(m.remove(key), opt) == packed(m, opt).remove(StorageKey::MapKey(key)),
{
    assert(packed(m.remove(key), opt) =~= packed(m, opt).remove(StorageKey::MapKey(key)));
}

/// Exact embedding: both original physical fields are recoverable independently.
pub proof fn packed_injective(
    m: IMap<int, Goo>,
    opt: Option<Goo>,
    m2: IMap<int, Goo>,
    opt2: Option<Goo>,
)
    requires
        packed(m, opt) == packed(m2, opt2),
    ensures
        m == m2,
        opt == opt2,
{
    assert(m =~= m2) by {
        assert forall|k: int| m.dom().contains(k) == m2.dom().contains(k) by {
            packed_map_at(m, opt, k);
            packed_map_at(m2, opt2, k);
            assert(packed(m, opt).dom().contains(StorageKey::MapKey(k)) == packed(
                m2,
                opt2,
            ).dom().contains(StorageKey::MapKey(k)));
        }
        assert forall|k: int| m.dom().contains(k) implies m[k] == m2[k] by {
            packed_map_at(m, opt, k);
            packed_map_at(m2, opt2, k);
            assert(packed(m, opt)[StorageKey::MapKey(k)] == packed(m2, opt2)[StorageKey::MapKey(
                k,
            )]);
        }
    }
    packed_option_at(m, opt);
    packed_option_at(m2, opt2);
    assert(packed(m, opt).dom().contains(StorageKey::Optional) == packed(m2, opt2).dom().contains(
        StorageKey::Optional,
    ));
    if opt is Some {
        assert(packed(m, opt)[StorageKey::Optional] == packed(m2, opt2)[StorageKey::Optional]);
    }
}

} // verus!
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 SafeY {
    fields {
        #[sharding(imap)] pub m: IMap<int,Goo>,
        #[sharding(option)] pub opt: Option<Goo>,
        #[sharding(storage_imap)] pub stored: IMap<StorageKey,Goo>,
    }
    init! { initialize(m:IMap<int,Goo>,opt:Option<Goo>) {
        init m=m;
        init opt=opt;
        init stored=packed(m,opt);
    } }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, m: IMap<int, Goo>, opt: Option<Goo>) { }

    transition!{
        tr1() {
            remove opt -= Some(let Goo::Bar);
            withdraw stored -= [StorageKey::Optional => let Goo::Bar];
        }
    }

    transition!{
        tr2() {
            remove opt -= Some(let Goo::Qux(i1));
            withdraw stored -= [StorageKey::Optional => let Goo::Qux(j1)];
            assert(i1 == j1);
        }
    }

    transition!{
        tr3() {
            remove opt -= Some(let Goo::Tal(i1, i2));
            withdraw stored -= [StorageKey::Optional => let Goo::Tal(j1, j2)];
            assert(i1 == j1);
            assert(i2 == j2);
        }
    }

    transition!{
        tr4(key: int) {
            remove m -= [key => let Goo::Bar];
            withdraw stored -= [StorageKey::MapKey(key) => let Goo::Bar];
        }
    }

    transition!{
        tr5(key: int) {
            remove m -= [key => let Goo::Qux(i1)];
            withdraw stored -= [StorageKey::MapKey(key) => let Goo::Qux(j1)];
            assert(i1 == j1);
        }
    }

    transition!{
        tr6(key: int) {
            remove m -= [key => let Goo::Tal(i1, i2)];
            withdraw stored -= [StorageKey::MapKey(key) => let Goo::Tal(j1, j2)];
            assert(i1 == j1);
            assert(i2 == j2);
        }
    }

    transition!{
        tr7(key: int) {
            have opt >= Some(let Goo::Bar);
            have m >= [key => let Goo::Bar];
        }
    }

    transition!{
        tr8(key: int) {
            have opt >= Some(let Goo::Qux(i1));
            have m >= [key => let Goo::Qux(j1)];
            require(i1 == j1);
        }
    }

    transition!{
        tr9(key: int) {
            have opt >= Some(let Goo::Tal(i1, i2));
            have m >= [key => let Goo::Tal(j1, j2)];
            require(i1 == j1);
            require(i2 == j2);
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.stored == packed(self.m,self.opt)
    }

        #[inductive(tr1)]
        fn tr1_inductive(pre: Self, post: Self) { remove_optional_store(pre.m,pre.opt); }

        #[inductive(tr2)]
        fn tr2_inductive(pre: Self, post: Self) { remove_optional_store(pre.m,pre.opt); }

        #[inductive(tr3)]
        fn tr3_inductive(pre: Self, post: Self) { remove_optional_store(pre.m,pre.opt); }

        #[inductive(tr4)]
        fn tr4_inductive(pre: Self, post: Self, key: int) { remove_map_store(pre.m,pre.opt,key); }

        #[inductive(tr5)]
        fn tr5_inductive(pre: Self, post: Self, key: int) { remove_map_store(pre.m,pre.opt,key); }

        #[inductive(tr6)]
        fn tr6_inductive(pre: Self, post: Self, key: int) { remove_map_store(pre.m,pre.opt,key); }

        #[inductive(tr7)]
        fn tr7_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr8)]
        fn tr8_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr9)]
        fn tr9_inductive(pre: Self, post: Self, key: int) { }
}}

verus! {

/// Recover the original two stores through the checked exact packing invariant.
pub open spec fn project(state: SafeY::State) -> Y::State {
    Y::State { m: state.m, storage_m: state.m, opt: state.opt, storage_opt: state.opt }
}

pub proof fn original_protocol_refinement(pre: SafeY::State, post: SafeY::State, key: int)
    requires
        pre.invariant(),
        post.invariant(),
    ensures
        SafeY::State::tr1_strong(pre, post) ==> Y::State::tr1_strong(project(pre), project(post)),
        SafeY::State::tr2_strong(pre, post) ==> Y::State::tr2_strong(project(pre), project(post)),
        SafeY::State::tr3_strong(pre, post) ==> Y::State::tr3_strong(project(pre), project(post)),
        SafeY::State::tr4_strong(pre, post, key) ==> Y::State::tr4_strong(
            project(pre),
            project(post),
            key,
        ),
        SafeY::State::tr5_strong(pre, post, key) ==> Y::State::tr5_strong(
            project(pre),
            project(post),
            key,
        ),
        SafeY::State::tr6_strong(pre, post, key) ==> Y::State::tr6_strong(
            project(pre),
            project(post),
            key,
        ),
        SafeY::State::tr7_strong(pre, post, key) ==> Y::State::tr7_strong(
            project(pre),
            project(post),
            key,
        ),
        SafeY::State::tr8_strong(pre, post, key) ==> Y::State::tr8_strong(
            project(pre),
            project(post),
            key,
        ),
        SafeY::State::tr9_strong(pre, post, key) ==> Y::State::tr9_strong(
            project(pre),
            project(post),
            key,
        ),
        project(pre).invariant(),
        project(post).invariant(),
{
}

} // verus!
verus! {

pub proof fn initial_tokens(
    value: Goo,
    tracked map_permission: Goo,
    tracked option_permission: Goo,
) -> (tracked token: SafeY::Token)
    requires
        map_permission == value,
        option_permission == value,
    ensures
        token.fragment().opt == Some(vstd::resource::exclusive::ExclusiveRA::Exclusive(value)),
        token.fragment().m == map_frag(IMap::empty().insert(1int, value)),
{
    let entries = IMap::<int, Goo>::empty().insert(1int, value);
    let tracked mut base = IMap::tracked_empty();
    base.tracked_insert(StorageKey::MapKey(1int), map_permission);
    base.tracked_insert(StorageKey::Optional, option_permission);
    assert(base =~= packed(entries, Some(value)));
    let tracked token = SafeY::Protocol::initialize(base, entries, Some(value));
    let initial = choose|state: SafeY::State|
        SafeY::State::initialize(state, entries, Some(value)) && state.invariant()
            && token.fragment() == SafeY::Protocol::embed(state);
    Pointwise::extensionality(token.fragment().m, map_frag(IMap::empty().insert(1int, value)));
    token
}

pub proof fn original_have_ready(owned: SafeY::Fragment, value: Goo)
    requires
        owned.opt == Some(vstd::resource::exclusive::ExclusiveRA::Exclusive(value)),
        owned.m == map_frag(IMap::empty().insert(1int, value)),
    ensures
        value is Bar ==> SafeY::Protocol::tr7_requires(
            owned,
            SafeY::Fragment::unit(),
            IMap::empty(),
            1int,
        ),
        value is Qux ==> SafeY::Protocol::tr8_requires(
            owned,
            SafeY::Fragment::unit(),
            IMap::empty(),
            1int,
        ),
        value is Tal ==> SafeY::Protocol::tr9_requires(
            owned,
            SafeY::Fragment::unit(),
            IMap::empty(),
            1int,
        ),
{
    SafeY::Fragment::op_unit(owned);
    assert forall|frame: SafeY::Fragment, pre: SafeY::State|
        pre.invariant() && SafeY::Fragment::op(owned, frame) == SafeY::Protocol::embed(
            pre,
        ) implies (value is Bar ==> SafeY::State::tr7_enabled(pre, 1int)
        && SafeY::State::tr7_owners_enabled(pre, owned, SafeY::Fragment::unit(), 1int)
        && SafeY::State::tr7_deposited(pre, 1int) == IMap::empty()) && (value is Qux
        ==> SafeY::State::tr8_enabled(pre, 1int) && SafeY::State::tr8_owners_enabled(
        pre,
        owned,
        SafeY::Fragment::unit(),
        1int,
    ) && SafeY::State::tr8_deposited(pre, 1int) == IMap::empty()) && (value is Tal
        ==> SafeY::State::tr9_enabled(pre, 1int) && SafeY::State::tr9_owners_enabled(
        pre,
        owned,
        SafeY::Fragment::unit(),
        1int,
    ) && SafeY::State::tr9_deposited(pre, 1int) == IMap::empty()) by {
        map_owned_frame(owned.m, frame.m, pre.m, 1int, value);
    }
}

pub proof fn original_map_remove_ready(owned: SafeY::Fragment, value: Goo)
    requires
        owned.m == map_frag(IMap::empty().insert(1int, value)),
    ensures
        value is Bar ==> SafeY::Protocol::tr4_requires(
            owned,
            SafeY::Fragment::unit(),
            IMap::empty(),
            1int,
        ),
        value is Qux ==> SafeY::Protocol::tr5_requires(
            owned,
            SafeY::Fragment::unit(),
            IMap::empty(),
            1int,
        ),
        value is Tal ==> SafeY::Protocol::tr6_requires(
            owned,
            SafeY::Fragment::unit(),
            IMap::empty(),
            1int,
        ),
{
    SafeY::Fragment::op_unit(owned);
    assert forall|frame: SafeY::Fragment, pre: SafeY::State|
        pre.invariant() && SafeY::Fragment::op(owned, frame) == SafeY::Protocol::embed(
            pre,
        ) implies (value is Bar ==> SafeY::State::tr4_enabled(pre, 1int)
        && SafeY::State::tr4_owners_enabled(pre, owned, SafeY::Fragment::unit(), 1int)
        && SafeY::State::tr4_deposited(pre, 1int) == IMap::empty()) && (value is Qux
        ==> SafeY::State::tr5_enabled(pre, 1int) && SafeY::State::tr5_owners_enabled(
        pre,
        owned,
        SafeY::Fragment::unit(),
        1int,
    ) && SafeY::State::tr5_deposited(pre, 1int) == IMap::empty()) && (value is Tal
        ==> SafeY::State::tr6_enabled(pre, 1int) && SafeY::State::tr6_owners_enabled(
        pre,
        owned,
        SafeY::Fragment::unit(),
        1int,
    ) && SafeY::State::tr6_deposited(pre, 1int) == IMap::empty()) by {
        map_owned_frame(owned.m, frame.m, pre.m, 1int, value);
    }
}

pub proof fn test_inst1() {
    let tracked token = initial_tokens(Goo::Bar, Goo::Bar, Goo::Bar);
    original_have_ready(token.fragment(), Goo::Bar);
    let tracked token = SafeY::Protocol::tr7(token, 1int);
    let tracked (token, mut opt_withdrawn) = SafeY::Protocol::tr1(token);
    let tracked wi = opt_withdrawn.tracked_remove(StorageKey::Optional);
    assert(wi == Goo::Bar);
    original_map_remove_ready(token.fragment(), Goo::Bar);
    let old = token.fragment();
    let tracked (token, mut map_withdrawn) = SafeY::Protocol::tr4(token, 1int);
    let (pre, post, frame) = SafeY::Protocol::tr4_witness(
        old,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        map_withdrawn,
        1int,
    );
    SafeY::Fragment::op_unit(old);
    map_owned_frame(old.m, frame.m, pre.m, 1int, Goo::Bar);
    packed_map_at(pre.m, pre.opt, 1int);
    packed_map_at(post.m, post.opt, 1int);
    assert(!post.stored.dom().contains(StorageKey::MapKey(1int)));
    assert(map_withdrawn[StorageKey::MapKey(1int)] == Goo::Bar);
    let tracked wi2 = map_withdrawn.tracked_remove(StorageKey::MapKey(1int));
    assert(wi2 == Goo::Bar);
    token.validate();
}

pub proof fn test_inst2() {
    let tracked token = initial_tokens(Goo::Qux(8u64), Goo::Qux(8u64), Goo::Qux(8u64));
    original_have_ready(token.fragment(), Goo::Qux(8u64));
    let tracked token = SafeY::Protocol::tr8(token, 1int);
    let tracked (token, mut opt_withdrawn) = SafeY::Protocol::tr2(token);
    let tracked wi = opt_withdrawn.tracked_remove(StorageKey::Optional);
    assert(wi == Goo::Qux(8u64));
    original_map_remove_ready(token.fragment(), Goo::Qux(8u64));
    let old = token.fragment();
    let tracked (token, mut map_withdrawn) = SafeY::Protocol::tr5(token, 1int);
    let (pre, post, frame) = SafeY::Protocol::tr5_witness(
        old,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        map_withdrawn,
        1int,
    );
    SafeY::Fragment::op_unit(old);
    map_owned_frame(old.m, frame.m, pre.m, 1int, Goo::Qux(8u64));
    packed_map_at(pre.m, pre.opt, 1int);
    packed_map_at(post.m, post.opt, 1int);
    assert(!post.stored.dom().contains(StorageKey::MapKey(1int)));
    assert(map_withdrawn[StorageKey::MapKey(1int)] == Goo::Qux(8u64));
    let tracked wi2 = map_withdrawn.tracked_remove(StorageKey::MapKey(1int));
    assert(wi2 == Goo::Qux(8u64));
    token.validate();
}

pub proof fn test_inst3() {
    let tracked token = initial_tokens(
        Goo::Tal(8u64, 9u64),
        Goo::Tal(8u64, 9u64),
        Goo::Tal(8u64, 9u64),
    );
    original_have_ready(token.fragment(), Goo::Tal(8u64, 9u64));
    let tracked token = SafeY::Protocol::tr9(token, 1int);
    let tracked (token, mut opt_withdrawn) = SafeY::Protocol::tr3(token);
    let tracked wi = opt_withdrawn.tracked_remove(StorageKey::Optional);
    assert(wi == Goo::Tal(8u64, 9u64));
    original_map_remove_ready(token.fragment(), Goo::Tal(8u64, 9u64));
    let old = token.fragment();
    let tracked (token, mut map_withdrawn) = SafeY::Protocol::tr6(token, 1int);
    let (pre, post, frame) = SafeY::Protocol::tr6_witness(
        old,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        map_withdrawn,
        1int,
    );
    SafeY::Fragment::op_unit(old);
    map_owned_frame(old.m, frame.m, pre.m, 1int, Goo::Tal(8u64, 9u64));
    packed_map_at(pre.m, pre.opt, 1int);
    packed_map_at(post.m, post.opt, 1int);
    assert(!post.stored.dom().contains(StorageKey::MapKey(1int)));
    assert(map_withdrawn[StorageKey::MapKey(1int)] == Goo::Tal(8u64, 9u64));
    let tracked wi2 = map_withdrawn.tracked_remove(StorageKey::MapKey(1int));
    assert(wi2 == Goo::Tal(8u64, 9u64));
    token.validate();
}

pub fn demonstration() {
    proof {
        test_inst1();
        test_inst2();
        test_inst3();
    }
}

} // verus!
fn main() {
    demonstration();
}
