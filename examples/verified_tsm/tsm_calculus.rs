//! The statement calculus of `vstd::resource::tsm_calculus`, used by hand on a raw machine
//! with map, imap, set, iset and option fields: the machine's configuration split into and
//! joined from its fields' (`cfg_split`, `cfg_join`), and, per transition, a chain of step
//! lemmas from the generated ownership condition (`State::t_owners_enabled`) and a completion
//! to the frontend's enabling condition (`State::t_enabled`), its strong relation
//! (`State::t_strong`) for the chain's post-state, and the output configuration. Each
//! remove/have/add lemma of the calculus occurs in one chain (singleton, pattern-bound and
//! general operands; have after add; a branch before a have); the proofs have no
//! quantifier. The machine's generated `C1::local_ready::t::ready` is proved by the same
//! chains, emitted by the macro.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    C1 {
        fields {
            #[sharding(map)] pub m: Map<int, int>,
            #[sharding(imap)] pub im: IMap<int, int>,
            #[sharding(set)] pub s: Set<int>,
            #[sharding(iset)] pub is: ISet<int>,
            #[sharding(option)] pub o: Option<int>,
        }
        #[invariant] pub fn inv(&self) -> bool { true }
        init! { initialize() {
            init m = Map::empty(); init im = IMap::empty(); init s = Set::empty();
            init is = ISet::empty(); init o = None;
        } }
        // map: singleton remove, have and add
        transition! { rm_have(a: int, b: int) {
            remove m -= [a => 1];
            have m >= [b => 2];
            add m += [a => 3];
        } }
        // option: pattern-bound remove, `Some` add; map: a have after an add
        transition! { add_have(a: int, b: int) {
            remove o -= Some(let x);
            require(x > 0);
            remove m -= [a => x];
            add m += [a => x + 1];
            have m >= [b => 2];
            add o += Some(x);
        } }
        // a branch (map in one arm, set in the other) before a have
        transition! { branch_have(c: bool, a: int, b: int) {
            if c {
                remove m -= [a => 1];
                add m += [a => 0];
            } else {
                remove s -= set {a};
                add s += set {a};
            }
            have m >= [b => 2];
        } }
        // map and set: general remove, have and add; option: general have
        transition! { general(x: Map<int, int>, y: Map<int, int>, p: Set<int>, q: Option<int>) {
            remove m -= (x);
            have m >= (y);
            add m += (x);
            remove s -= (p);
            add s += (p);
            have o >= (q);
        } }
        // imap: pattern-bound remove, singleton add, general have; iset: singleton remove
        // and add, general have
        transition! { infinite(k: int, v: int, w: IMap<int, int>, e: ISet<int>) {
            remove im -= [k => let old];
            add im += [k => old + v];
            have im >= (w);
            remove is -= set {k};
            have is >= (e);
            add is += set {k};
        } }
        // imap, iset and option: general remove and add; set: singleton have, remove and add
        transition! { general_infinite(w: IMap<int, int>, e: ISet<int>, q: Option<int>, a: int, b: int) {
            remove im -= (w);
            add im += (w);
            remove is -= (e);
            add is += (e);
            remove o -= (q);
            add o += (q);
            have s >= set {a};
            remove s -= set {b};
            add s += set {b};
        } }
        // pattern-bound option and imap haves, singleton iset have, general set have
        transition! { peek(k: int, p: Set<int>) {
            have o >= Some(let y);
            have im >= [k => let u];
            have is >= set {k};
            have s >= (p);
            require(y == u);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(rm_have)] fn rm_have_inductive(pre: Self, post: Self, a: int, b: int) {}
        #[inductive(add_have)] fn add_have_inductive(pre: Self, post: Self, a: int, b: int) {}
        #[inductive(branch_have)] fn branch_have_inductive(pre: Self, post: Self, c: bool, a: int, b: int) {}
        #[inductive(general)] fn general_inductive(pre: Self, post: Self, x: Map<int, int>, y: Map<int, int>, p: Set<int>, q: Option<int>) {}
        #[inductive(infinite)] fn infinite_inductive(pre: Self, post: Self, k: int, v: int, w: IMap<int, int>, e: ISet<int>) {}
        #[inductive(peek)] fn peek_inductive(pre: Self, post: Self, k: int, p: Set<int>) {}
        #[inductive(general_infinite)] fn general_infinite_inductive(pre: Self, post: Self, w: IMap<int, int>, e: ISet<int>, q: Option<int>, a: int, b: int) {}
    }
}

pub mod chains {
    use vstd::prelude::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::PCM;
    use vstd::resource::tsm::Machine;
    use vstd::resource::tsm_calculus::*;
    use vstd::resource::tsm_collections::*;
    use super::C1::{Fragment, Protocol, State};

    // ---- per machine: the configuration is the conjunction of the fields'
    pub proof fn cfg_split(o: Fragment, h: Fragment, z: Fragment, s: State)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(s),
        ensures
            cfg(o.m, h.m, z.m, map_frag(s.m.to_imap())),
            cfg(o.im, h.im, z.im, map_frag(s.im)),
            cfg(o.s, h.s, z.s, set_frag(s.s.to_iset())),
            cfg(o.is, h.is, z.is, set_frag(s.is)),
            cfg(o.o, h.o, z.o, option_frag(s.o)),
    {
        cfg_iff(o.m, h.m, z.m, map_frag(s.m.to_imap()));
        cfg_iff(o.im, h.im, z.im, map_frag(s.im));
        cfg_iff(o.s, h.s, z.s, set_frag(s.s.to_iset()));
        cfg_iff(o.is, h.is, z.is, set_frag(s.is));
        cfg_iff(o.o, h.o, z.o, option_frag(s.o));
    }

    pub proof fn cfg_join(o: Fragment, h: Fragment, z: Fragment, s: State)
        requires
            cfg(o.m, h.m, z.m, map_frag(s.m.to_imap())),
            cfg(o.im, h.im, z.im, map_frag(s.im)),
            cfg(o.s, h.s, z.s, set_frag(s.s.to_iset())),
            cfg(o.is, h.is, z.is, set_frag(s.is)),
            cfg(o.o, h.o, z.o, option_frag(s.o)),
        ensures
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(s),
    {
        cfg_iff(o.m, h.m, z.m, map_frag(s.m.to_imap()));
        cfg_iff(o.im, h.im, z.im, map_frag(s.im));
        cfg_iff(o.s, h.s, z.s, set_frag(s.s.to_iset()));
        cfg_iff(o.is, h.is, z.is, set_frag(s.is));
        cfg_iff(o.o, h.o, z.o, option_frag(s.o));
    }

    // Each chain: from the completion `op(op(o, h), z) == embed(pre)` and the generated
    // ownership condition, the enabling condition, the strong relation to the chain's
    // post-state, and the output configuration of the chain's final fragment. The
    // fragments are the ownership compiler's terms (`__tsm_set_f(o, ..)`).

    pub open spec fn rm_have_new(o: Fragment, a: int) -> Fragment {
        let o1 = o.__tsm_set_m(map_remove_many(o.m, IMap::empty().insert(a, 1int).dom()));
        o1.__tsm_set_m(MapFragment::op(o1.m, map_frag(IMap::empty().insert(a, 3int))))
    }

    pub proof fn rm_have(o: Fragment, h: Fragment, z: Fragment, pre: State, a: int, b: int)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::rm_have_owners_enabled(pre, o, h, a, b),
        ensures
            State::rm_have_enabled(pre, a, b),
            ({
                let post = State { m: pre.m.remove(a).insert(a, 3), ..pre };
                State::rm_have_strong(pre, post, a, b) && Fragment::op(Fragment::op(rm_have_new(o, a), h), z)
                    == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        map_remove_one(o.m, h.m, z.m, pre.m, a, 1);
        let o1 = o.__tsm_set_m(map_remove_many(o.m, IMap::empty().insert(a, 1int).dom()));
        let vm = pre.m.remove(a);
        map_have_one(o1.m, h.m, z.m, vm, b, 2);
        map_add_one(o1.m, h.m, z.m, vm, a, 3);
        cfg_join(rm_have_new(o, a), h, z, State { m: vm.insert(a, 3), ..pre });
    }

    pub open spec fn add_have_new(o: Fragment, a: int) -> Fragment {
        let x = o.o->Some_0->Exclusive_0;
        let o1 = o.__tsm_set_o(option_remove_operand(o.o, Some(x)));
        let o2 = o1.__tsm_set_m(map_remove_many(o1.m, IMap::empty().insert(a, x).dom()));
        let o3 = o2.__tsm_set_m(MapFragment::op(o2.m, map_frag(IMap::empty().insert(a, x + 1))));
        o3.__tsm_set_o(OptionFragment::op(o3.o, option_frag(Some(x))))
    }

    pub proof fn add_have(o: Fragment, h: Fragment, z: Fragment, pre: State, a: int, b: int)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::add_have_owners_enabled(pre, o, h, a, b),
            // the `require`, at the owned value
            o.o->Some_0->Exclusive_0 > 0,
        ensures
            State::add_have_enabled(pre, a, b),
            ({
                let x = o.o->Some_0->Exclusive_0;
                let post = State { m: pre.m.remove(a).insert(a, x + 1), o: Some(x), ..pre };
                State::add_have_strong(pre, post, a, b) && Fragment::op(Fragment::op(add_have_new(o, a), h), z)
                    == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        let x = o.o->Some_0->Exclusive_0;
        opt_remove_some(o.o, h.o, z.o, pre.o, x);
        let o1 = o.__tsm_set_o(option_remove_operand(o.o, Some(x)));
        map_remove_one(o1.m, h.m, z.m, pre.m, a, x);
        let o2 = o1.__tsm_set_m(map_remove_many(o1.m, IMap::empty().insert(a, x).dom()));
        let vm = pre.m.remove(a);
        map_add_one(o2.m, h.m, z.m, vm, a, x + 1);
        let o3 = o2.__tsm_set_m(MapFragment::op(o2.m, map_frag(IMap::empty().insert(a, x + 1))));
        map_have_one(o3.m, h.m, z.m, vm.insert(a, x + 1), b, 2);
        opt_add_some(o3.o, h.o, z.o, None, x);
        cfg_join(add_have_new(o, a), h, z, State { m: vm.insert(a, x + 1), o: Some(x), ..pre });
    }

    pub open spec fn branch_have_new(o: Fragment, c: bool, a: int) -> Fragment {
        if c {
            let o1 = o.__tsm_set_m(map_remove_many(o.m, IMap::empty().insert(a, 1int).dom()));
            o1.__tsm_set_m(MapFragment::op(o1.m, map_frag(IMap::empty().insert(a, 0int))))
        } else {
            let o1 = o.__tsm_set_s(set_remove_many(o.s, ISet::empty().insert(a)));
            o1.__tsm_set_s(SetFragment::op(o1.s, set_frag(ISet::empty().insert(a))))
        }
    }

    // The arms' (fragment, values) tuples are joined; the have follows once.
    pub proof fn branch_have(o: Fragment, h: Fragment, z: Fragment, pre: State, c: bool, a: int, b: int)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::branch_have_owners_enabled(pre, o, h, c, a, b),
        ensures
            State::branch_have_enabled(pre, c, a, b),
            ({
                let post = if c {
                    State { m: pre.m.remove(a).insert(a, 0), ..pre }
                } else {
                    State { s: pre.s.remove(a).insert(a), ..pre }
                };
                State::branch_have_strong(pre, post, c, a, b) && Fragment::op(
                    Fragment::op(branch_have_new(o, c, a), h),
                    z,
                ) == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        let (o1, vm, vs) = if c {
            map_remove_one(o.m, h.m, z.m, pre.m, a, 1);
            let o1 = o.__tsm_set_m(map_remove_many(o.m, IMap::empty().insert(a, 1int).dom()));
            let vm = pre.m.remove(a);
            map_add_one(o1.m, h.m, z.m, vm, a, 0);
            (o1.__tsm_set_m(MapFragment::op(o1.m, map_frag(IMap::empty().insert(a, 0int)))), vm.insert(a, 0), pre.s)
        } else {
            set_remove_one(o.s, h.s, z.s, pre.s, a);
            let o1 = o.__tsm_set_s(set_remove_many(o.s, ISet::empty().insert(a)));
            let vs = pre.s.remove(a);
            set_add_one(o1.s, h.s, z.s, vs, a);
            (o1.__tsm_set_s(SetFragment::op(o1.s, set_frag(ISet::empty().insert(a)))), pre.m, vs.insert(a))
        };
        map_have_one(o1.m, h.m, z.m, vm, b, 2);
        cfg_join(o1, h, z, State { m: vm, s: vs, ..pre });
    }

    pub open spec fn general_new(o: Fragment, x: Map<int, int>, p: Set<int>) -> Fragment {
        let o1 = o.__tsm_set_m(map_remove_many(o.m, x.to_imap().dom()));
        let o2 = o1.__tsm_set_m(MapFragment::op(o1.m, map_frag(x.to_imap())));
        let o3 = o2.__tsm_set_s(set_remove_many(o2.s, p.to_iset()));
        o3.__tsm_set_s(SetFragment::op(o3.s, set_frag(p.to_iset())))
    }

    pub proof fn general(
        o: Fragment,
        h: Fragment,
        z: Fragment,
        pre: State,
        x: Map<int, int>,
        y: Map<int, int>,
        p: Set<int>,
        q: Option<int>,
    )
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::general_owners_enabled(pre, o, h, x, y, p, q),
        ensures
            State::general_enabled(pre, x, y, p, q),
            ({
                let post = State {
                    m: pre.m.remove_keys(x.dom()).union_prefer_right(x),
                    s: pre.s.difference(p).union(p),
                    ..pre
                };
                State::general_strong(pre, post, x, y, p, q) && Fragment::op(
                    Fragment::op(general_new(o, x, p), h),
                    z,
                ) == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        map_remove(o.m, h.m, z.m, pre.m, x);
        let o1 = o.__tsm_set_m(map_remove_many(o.m, x.to_imap().dom()));
        let vm = pre.m.remove_keys(x.dom());
        map_have(o1.m, h.m, z.m, vm, y);
        assert(vm.dom().disjoint(x.dom()));
        map_add(o1.m, h.m, z.m, vm, x);
        let o2 = o1.__tsm_set_m(MapFragment::op(o1.m, map_frag(x.to_imap())));
        set_remove(o2.s, h.s, z.s, pre.s, p);
        let o3 = o2.__tsm_set_s(set_remove_many(o2.s, p.to_iset()));
        let vs = pre.s.difference(p);
        assert(vs.disjoint(p));
        set_add(o3.s, h.s, z.s, vs, p);
        let o4 = o3.__tsm_set_s(SetFragment::op(o3.s, set_frag(p.to_iset())));
        opt_have(o4.o, h.o, z.o, pre.o, q);
        cfg_join(o4, h, z, State { m: vm.union_prefer_right(x), s: vs.union(p), ..pre });
    }

    pub open spec fn infinite_new(o: Fragment, k: int, v: int) -> Fragment {
        let old = o.im.at(k)->Some_0->Exclusive_0;
        let o1 = o.__tsm_set_im(map_remove_many(o.im, IMap::empty().insert(k, old).dom()));
        let o2 = o1.__tsm_set_im(MapFragment::op(o1.im, map_frag(IMap::empty().insert(k, old + v))));
        let o3 = o2.__tsm_set_is(set_remove_many(o2.is, ISet::empty().insert(k)));
        o3.__tsm_set_is(SetFragment::op(o3.is, set_frag(ISet::empty().insert(k))))
    }

    pub proof fn infinite(
        o: Fragment,
        h: Fragment,
        z: Fragment,
        pre: State,
        k: int,
        v: int,
        w: IMap<int, int>,
        e: ISet<int>,
    )
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::infinite_owners_enabled(pre, o, h, k, v, w, e),
        ensures
            State::infinite_enabled(pre, k, v, w, e),
            ({
                let old = o.im.at(k)->Some_0->Exclusive_0;
                let post = State {
                    im: pre.im.remove(k).insert(k, old + v),
                    is: pre.is.remove(k).insert(k),
                    ..pre
                };
                State::infinite_strong(pre, post, k, v, w, e) && Fragment::op(
                    Fragment::op(infinite_new(o, k, v), h),
                    z,
                ) == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        let old = o.im.at(k)->Some_0->Exclusive_0;
        imap_remove_one(o.im, h.im, z.im, pre.im, k, old);
        let o1 = o.__tsm_set_im(map_remove_many(o.im, IMap::empty().insert(k, old).dom()));
        let vim = pre.im.remove(k);
        imap_add_one(o1.im, h.im, z.im, vim, k, old + v);
        let o2 = o1.__tsm_set_im(MapFragment::op(o1.im, map_frag(IMap::empty().insert(k, old + v))));
        imap_have(o2.im, h.im, z.im, vim.insert(k, old + v), w);
        iset_remove_one(o2.is, h.is, z.is, pre.is, k);
        let o3 = o2.__tsm_set_is(set_remove_many(o2.is, ISet::empty().insert(k)));
        let vis = pre.is.remove(k);
        iset_have(o3.is, h.is, z.is, vis, e);
        iset_add_one(o3.is, h.is, z.is, vis, k);
        cfg_join(infinite_new(o, k, v), h, z, State { im: vim.insert(k, old + v), is: vis.insert(k), ..pre });
    }

    pub open spec fn general_infinite_new(
        o: Fragment,
        w: IMap<int, int>,
        e: ISet<int>,
        q: Option<int>,
        b: int,
    ) -> Fragment {
        let o1 = o.__tsm_set_im(map_remove_many(o.im, w.dom()));
        let o2 = o1.__tsm_set_im(MapFragment::op(o1.im, map_frag(w)));
        let o3 = o2.__tsm_set_is(set_remove_many(o2.is, e));
        let o4 = o3.__tsm_set_is(SetFragment::op(o3.is, set_frag(e)));
        let o5 = o4.__tsm_set_o(option_remove_operand(o4.o, q));
        let o6 = o5.__tsm_set_o(OptionFragment::op(o5.o, option_frag(q)));
        let o7 = o6.__tsm_set_s(set_remove_many(o6.s, ISet::empty().insert(b)));
        o7.__tsm_set_s(SetFragment::op(o7.s, set_frag(ISet::empty().insert(b))))
    }

    pub proof fn general_infinite(
        o: Fragment,
        h: Fragment,
        z: Fragment,
        pre: State,
        w: IMap<int, int>,
        e: ISet<int>,
        q: Option<int>,
        a: int,
        b: int,
    )
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::general_infinite_owners_enabled(pre, o, h, w, e, q, a, b),
        ensures
            State::general_infinite_enabled(pre, w, e, q, a, b),
            ({
                let post = State {
                    im: pre.im.remove_keys(w.dom()).union_prefer_right(w),
                    is: pre.is.difference(e).union(e),
                    o: vstd::state_machine_internal::opt_add(vstd::state_machine_internal::opt_sub(pre.o, q), q),
                    s: pre.s.remove(b).insert(b),
                    ..pre
                };
                State::general_infinite_strong(pre, post, w, e, q, a, b) && Fragment::op(
                    Fragment::op(general_infinite_new(o, w, e, q, b), h),
                    z,
                ) == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        imap_remove(o.im, h.im, z.im, pre.im, w);
        let o1 = o.__tsm_set_im(map_remove_many(o.im, w.dom()));
        let vim = pre.im.remove_keys(w.dom());
        assert(vim.dom().disjoint(w.dom()));
        imap_add(o1.im, h.im, z.im, vim, w);
        let o2 = o1.__tsm_set_im(MapFragment::op(o1.im, map_frag(w)));
        iset_remove(o2.is, h.is, z.is, pre.is, e);
        let o3 = o2.__tsm_set_is(set_remove_many(o2.is, e));
        let vis = pre.is.difference(e);
        assert(vis.disjoint(e));
        iset_add(o3.is, h.is, z.is, vis, e);
        let o4 = o3.__tsm_set_is(SetFragment::op(o3.is, set_frag(e)));
        opt_remove(o4.o, h.o, z.o, pre.o, q);
        let o5 = o4.__tsm_set_o(option_remove_operand(o4.o, q));
        let vo = vstd::state_machine_internal::opt_sub(pre.o, q);
        opt_add(o5.o, h.o, z.o, vo, q);
        let o6 = o5.__tsm_set_o(OptionFragment::op(o5.o, option_frag(q)));
        set_have_one(o6.s, h.s, z.s, pre.s, a);
        set_remove_one(o6.s, h.s, z.s, pre.s, b);
        let o7 = o6.__tsm_set_s(set_remove_many(o6.s, ISet::empty().insert(b)));
        let vs = pre.s.remove(b);
        set_add_one(o7.s, h.s, z.s, vs, b);
        cfg_join(
            general_infinite_new(o, w, e, q, b),
            h,
            z,
            State {
                im: vim.union_prefer_right(w),
                is: vis.union(e),
                o: vstd::state_machine_internal::opt_add(vo, q),
                s: vs.insert(b),
                ..pre
            },
        );
    }

    pub proof fn peek(o: Fragment, h: Fragment, z: Fragment, pre: State, k: int, p: Set<int>)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::peek_owners_enabled(pre, o, h, k, p),
            // the `require`, at the observed values
            Fragment::op(o, h).o->Some_0->Exclusive_0 == Fragment::op(o, h).im.at(k)->Some_0->Exclusive_0,
        ensures
            State::peek_enabled(pre, k, p),
            State::peek_strong(pre, pre, k, p),
    {
        cfg_split(o, h, z, pre);
        let oh = Fragment::op(o, h);
        opt_have_some(o.o, h.o, z.o, pre.o, oh.o->Some_0->Exclusive_0);
        imap_have_one(o.im, h.im, z.im, pre.im, k, oh.im.at(k)->Some_0->Exclusive_0);
        iset_have_one(o.is, h.is, z.is, pre.is, k);
        set_have(o.s, h.s, z.s, pre.s, p);
    }

    // ---- a borrowed singleton token's entry after removals (generic interface)
    pub proof fn token_observed(
        o: MapFragment<int, int>,
        h: MapFragment<int, int>,
        z: MapFragment<int, int>,
        v: IMap<int, int>,
        c: MapFragment<int, int>,
        a: int,
        b: int,
    )
        requires
            cfg(o, h, z, map_frag(v)),
            h == MapFragment::op(map_frag(IMap::empty().insert(b, 2int)), c),
            map_owns(o, IMap::empty().insert(a, 1int)),
        ensures
            v.contains_pair(a, 1),
            v.remove(a).contains_pair(b, 2),
    {
        map_token_observed(o, h, z, v, c, IMap::empty().insert(a, 1int).dom(), b, 2);
        imap_remove_one(o, h, z, v, a, 1);
        imap_have_one(map_remove_many(o, IMap::empty().insert(a, 1int).dom()), h, z, v.remove(a), b, 2);
    }
}

fn main() {}

} // verus!
