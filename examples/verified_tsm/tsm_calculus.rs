//! The statement calculus of `vstd::resource::tsm_calculus`, used by hand on two raw
//! machines: `C1` (map, imap, set, iset and option fields) and `C2` (the persistent
//! collections and option, multiset, count, bool, persistent count and bool, a variable and
//! a constant). Per machine, the configuration is split into and joined from the fields'
//! (`cfg_split`, `cfg_join`); per transition, a chain of step lemmas goes from the generated
//! ownership condition (`State::t_owners_enabled`) and a completion to the frontend's
//! enabling condition (`State::t_enabled`), its strong relation (`State::t_strong`) for the
//! chain's post-state, and the output configuration. Each step lemma of the calculus
//! occurs in one chain (singleton, pattern-bound and general operands; have after add; a
//! branch before a have); the proofs have no quantifier. The machines' generated
//! `local_ready::t::ready` lemmas are proved by the same chains, emitted by the macro.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::multiset::Multiset;

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

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    C2 {
        fields {
            #[sharding(persistent_map)] pub pm: Map<int, int>,
            #[sharding(persistent_imap)] pub pim: IMap<int, int>,
            #[sharding(persistent_set)] pub ps: Set<int>,
            #[sharding(persistent_iset)] pub pis: ISet<int>,
            #[sharding(persistent_option)] pub po: Option<int>,
            #[sharding(multiset)] pub ms: Multiset<int>,
            #[sharding(count)] pub c: nat,
            #[sharding(bool)] pub b: bool,
            #[sharding(bool)] pub b2: bool,
            #[sharding(persistent_count)] pub pc: nat,
            #[sharding(persistent_bool)] pub pb: bool,
            #[sharding(variable)] pub v: int,
            #[sharding(constant)] pub k: int,
        }
        #[invariant] pub fn inv(&self) -> bool { true }
        init! { initialize() {
            init pm = Map::empty(); init pim = IMap::empty(); init ps = Set::empty();
            init pis = ISet::empty(); init po = None; init ms = Multiset::empty(); init c = 0;
            init b = false; init b2 = false; init pc = 0; init pb = false; init v = 0; init k = 1;
        } }
        // persistent maps, sets and options: singleton, pattern-bound and general haves and adds
        transition! { persist(j: int, x: int, a: Map<int, int>, w: IMap<int, int>, sa: Set<int>, e: ISet<int>, q: Option<int>) {
            have pm >= [j => x];
            add pm (union)= [j => x];
            have pm >= (a);
            add pm (union)= (a);
            have pim >= [j => let y];
            add pim (union)= [j => y];
            have pim >= (w);
            add pim (union)= (w);
            have ps >= set {j};
            add ps (union)= set {j};
            have ps >= (sa);
            add ps (union)= (sa);
            have pis >= set {j};
            add pis (union)= set {j};
            have pis >= (e);
            add pis (union)= (e);
            have po >= Some(let u);
            add po (union)= Some(u);
            have po >= (q);
            add po (union)= (q);
        } }
        // multiset, count, bool, persistent count and persistent bool
        transition! { counted(n: nat, x: Multiset<int>, el: int, f: bool) {
            remove ms -= {el};
            remove ms -= (x);
            have ms >= {el};
            have ms >= (x);
            add ms += {el};
            add ms += (x);
            remove c -= (n);
            have c >= (n);
            add c += (n);
            have b >= true;
            remove b -= true;
            add b += true;
            have b2 >= (f);
            remove b2 -= (f);
            add b2 += (f);
            have pc >= (n);
            add pc (union)= (n);
            have pb >= true;
            add pb (union)= true;
            have pb >= (f);
            add pb (union)= (f);
        } }
        // a variable updated from a constant
        transition! { bump() {
            require(pre.k > 0);
            update v = pre.v + pre.k;
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(persist)] fn persist_inductive(pre: Self, post: Self, j: int, x: int, a: Map<int, int>, w: IMap<int, int>, sa: Set<int>, e: ISet<int>, q: Option<int>) {}
        #[inductive(counted)] fn counted_inductive(pre: Self, post: Self, n: nat, x: Multiset<int>, el: int, f: bool) {}
        #[inductive(bump)] fn bump_inductive(pre: Self, post: Self) {}
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

pub mod chains2 {
    use vstd::prelude::*;
    use vstd::multiset::Multiset;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::PCM;
    use vstd::resource::tsm::{CountRA, Machine};
    use vstd::resource::tsm_bool::*;
    use vstd::resource::tsm_calculus::*;
    use vstd::resource::tsm_collections::*;
    use vstd::resource::tsm_finite_multiset::*;
    use vstd::resource::tsm_persistent::*;
    use vstd::resource::exclusive::ExclusiveRA;
    use vstd::resource::agree::AgreementRA;
    use vstd::state_machine_internal as smi;
    use super::C2::{Fragment, Protocol, State};

    pub proof fn cfg_split(o: Fragment, h: Fragment, z: Fragment, s: State)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(s),
        ensures
            cfg(o.pm, h.pm, z.pm, persistent_map_frag(s.pm.to_imap())),
            cfg(o.pim, h.pim, z.pim, persistent_map_frag(s.pim)),
            cfg(o.ps, h.ps, z.ps, persistent_set_frag(s.ps.to_iset())),
            cfg(o.pis, h.pis, z.pis, persistent_set_frag(s.pis)),
            cfg(o.po, h.po, z.po, persistent_option_frag(s.po)),
            cfg(o.ms, h.ms, z.ms, finite_multiset_frag(s.ms)),
            cfg(o.c, h.c, z.c, CountRA { count: s.c }),
            cfg(o.b, h.b, z.b, bool_frag(s.b)),
            cfg(o.b2, h.b2, z.b2, bool_frag(s.b2)),
            cfg(o.pc, h.pc, z.pc, PersistentCountRA { count: s.pc }),
            cfg(o.pb, h.pb, z.pb, persistent_bool_frag(s.pb)),
            cfg(o.v, h.v, z.v, Some(ExclusiveRA::Exclusive(s.v))),
            cfg(o.k, h.k, z.k, Some(AgreementRA::Agree(s.k))),
    {
        cfg_iff(o.pm, h.pm, z.pm, persistent_map_frag(s.pm.to_imap()));
        cfg_iff(o.pim, h.pim, z.pim, persistent_map_frag(s.pim));
        cfg_iff(o.ps, h.ps, z.ps, persistent_set_frag(s.ps.to_iset()));
        cfg_iff(o.pis, h.pis, z.pis, persistent_set_frag(s.pis));
        cfg_iff(o.po, h.po, z.po, persistent_option_frag(s.po));
        cfg_iff(o.ms, h.ms, z.ms, finite_multiset_frag(s.ms));
        cfg_iff(o.c, h.c, z.c, CountRA { count: s.c });
        cfg_iff(o.b, h.b, z.b, bool_frag(s.b));
        cfg_iff(o.b2, h.b2, z.b2, bool_frag(s.b2));
        cfg_iff(o.pc, h.pc, z.pc, PersistentCountRA { count: s.pc });
        cfg_iff(o.pb, h.pb, z.pb, persistent_bool_frag(s.pb));
        cfg_iff(o.v, h.v, z.v, Some(ExclusiveRA::Exclusive(s.v)));
        cfg_iff(o.k, h.k, z.k, Some(AgreementRA::Agree(s.k)));
    }

    pub proof fn cfg_join(o: Fragment, h: Fragment, z: Fragment, s: State)
        requires
            cfg(o.pm, h.pm, z.pm, persistent_map_frag(s.pm.to_imap())),
            cfg(o.pim, h.pim, z.pim, persistent_map_frag(s.pim)),
            cfg(o.ps, h.ps, z.ps, persistent_set_frag(s.ps.to_iset())),
            cfg(o.pis, h.pis, z.pis, persistent_set_frag(s.pis)),
            cfg(o.po, h.po, z.po, persistent_option_frag(s.po)),
            cfg(o.ms, h.ms, z.ms, finite_multiset_frag(s.ms)),
            cfg(o.c, h.c, z.c, CountRA { count: s.c }),
            cfg(o.b, h.b, z.b, bool_frag(s.b)),
            cfg(o.b2, h.b2, z.b2, bool_frag(s.b2)),
            cfg(o.pc, h.pc, z.pc, PersistentCountRA { count: s.pc }),
            cfg(o.pb, h.pb, z.pb, persistent_bool_frag(s.pb)),
            cfg(o.v, h.v, z.v, Some(ExclusiveRA::Exclusive(s.v))),
            cfg(o.k, h.k, z.k, Some(AgreementRA::Agree(s.k))),
        ensures
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(s),
    {
        cfg_iff(o.pm, h.pm, z.pm, persistent_map_frag(s.pm.to_imap()));
        cfg_iff(o.pim, h.pim, z.pim, persistent_map_frag(s.pim));
        cfg_iff(o.ps, h.ps, z.ps, persistent_set_frag(s.ps.to_iset()));
        cfg_iff(o.pis, h.pis, z.pis, persistent_set_frag(s.pis));
        cfg_iff(o.po, h.po, z.po, persistent_option_frag(s.po));
        cfg_iff(o.ms, h.ms, z.ms, finite_multiset_frag(s.ms));
        cfg_iff(o.c, h.c, z.c, CountRA { count: s.c });
        cfg_iff(o.b, h.b, z.b, bool_frag(s.b));
        cfg_iff(o.b2, h.b2, z.b2, bool_frag(s.b2));
        cfg_iff(o.pc, h.pc, z.pc, PersistentCountRA { count: s.pc });
        cfg_iff(o.pb, h.pb, z.pb, persistent_bool_frag(s.pb));
        cfg_iff(o.v, h.v, z.v, Some(ExclusiveRA::Exclusive(s.v)));
        cfg_iff(o.k, h.k, z.k, Some(AgreementRA::Agree(s.k)));
    }

    pub open spec fn persist_new(
        o: Fragment,
        h: Fragment,
        j: int,
        x: int,
        a: Map<int, int>,
        w: IMap<int, int>,
        sa: Set<int>,
        e: ISet<int>,
        q: Option<int>,
    ) -> Fragment {
        let oh = Fragment::op(o, h);
        let y = oh.pim.at(j)->Some_0->Agree_0;
        let u = oh.po->Some_0->Agree_0;
        Fragment {
            pm: PersistentMapFragment::op(
                PersistentMapFragment::op(o.pm, persistent_map_frag(IMap::empty().insert(j, x))),
                persistent_map_frag(a.to_imap()),
            ),
            pim: PersistentMapFragment::op(
                PersistentMapFragment::op(o.pim, persistent_map_frag(IMap::empty().insert(j, y))),
                persistent_map_frag(w),
            ),
            ps: PersistentSetFragment::op(
                PersistentSetFragment::op(o.ps, persistent_set_frag(ISet::empty().insert(j))),
                persistent_set_frag(sa.to_iset()),
            ),
            pis: PersistentSetFragment::op(
                PersistentSetFragment::op(o.pis, persistent_set_frag(ISet::empty().insert(j))),
                persistent_set_frag(e),
            ),
            po: PersistentOptionFragment::op(
                PersistentOptionFragment::op(o.po, persistent_option_frag(Some(u))),
                persistent_option_frag(q),
            ),
            ..o
        }
    }

    // Persistent haves before adds (the haves make the adds safe).
    pub proof fn persist(
        o: Fragment,
        h: Fragment,
        z: Fragment,
        pre: State,
        j: int,
        x: int,
        a: Map<int, int>,
        w: IMap<int, int>,
        sa: Set<int>,
        e: ISet<int>,
        q: Option<int>,
    )
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::persist_owners_enabled(pre, o, h, j, x, a, w, sa, e, q),
        ensures
            State::persist_enabled(pre, j, x, a, w, sa, e, q),
            ({
                let oh = Fragment::op(o, h);
                let y = oh.pim.at(j)->Some_0->Agree_0;
                let u = oh.po->Some_0->Agree_0;
                let post = State {
                    pm: pre.pm.insert(j, x).union_prefer_right(a),
                    pim: pre.pim.insert(j, y).union_prefer_right(w),
                    ps: pre.ps.insert(j).union(sa),
                    pis: pre.pis.insert(j).union(e),
                    po: smi::opt_add(Some(u), q),
                    ..pre
                };
                State::persist_strong(pre, post, j, x, a, w, sa, e, q) && Fragment::op(
                    Fragment::op(persist_new(o, h, j, x, a, w, sa, e, q), h),
                    z,
                ) == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        let oh = Fragment::op(o, h);
        // persistent_map: the haves (in the fragments `o` only grows by the adds; the
        // haves observe `op(o, h)` before them)
        pmap_have_one(o.pm, h.pm, z.pm, pre.pm, j, x);
        pmap_add_one(o.pm, h.pm, z.pm, pre.pm, j, x);
        let opm = PersistentMapFragment::op(o.pm, persistent_map_frag(IMap::empty().insert(j, x)));
        let vpm = pre.pm.insert(j, x);
        assert(PersistentMapFragment::op(opm, h.pm) == PersistentMapFragment::op(oh.pm, persistent_map_frag(IMap::empty().insert(j, x)))) by {
            PersistentMapFragment::associative(o.pm, persistent_map_frag(IMap::empty().insert(j, x)), h.pm);
            PersistentMapFragment::commutative(persistent_map_frag(IMap::empty().insert(j, x)), h.pm);
            PersistentMapFragment::associative(o.pm, h.pm, persistent_map_frag(IMap::empty().insert(j, x)));
        };
        pmap_have(opm, h.pm, z.pm, vpm, a);
        pmap_add(opm, h.pm, z.pm, vpm, a);
        // persistent_imap: pattern-bound
        let y = oh.pim.at(j)->Some_0->Agree_0;
        pimap_have_one(o.pim, h.pim, z.pim, pre.pim, j, y);
        pimap_add_one(o.pim, h.pim, z.pim, pre.pim, j, y);
        let opim = PersistentMapFragment::op(o.pim, persistent_map_frag(IMap::empty().insert(j, y)));
        pimap_have(opim, h.pim, z.pim, pre.pim.insert(j, y), w);
        pimap_add(opim, h.pim, z.pim, pre.pim.insert(j, y), w);
        // persistent sets
        pset_have_one(o.ps, h.ps, z.ps, pre.ps, j);
        pset_add_one(o.ps, h.ps, z.ps, pre.ps, j);
        let ops = PersistentSetFragment::op(o.ps, persistent_set_frag(ISet::empty().insert(j)));
        pset_have(ops, h.ps, z.ps, pre.ps.insert(j), sa);
        pset_add(ops, h.ps, z.ps, pre.ps.insert(j), sa);
        piset_have_one(o.pis, h.pis, z.pis, pre.pis, j);
        piset_add_one(o.pis, h.pis, z.pis, pre.pis, j);
        let opis = PersistentSetFragment::op(o.pis, persistent_set_frag(ISet::empty().insert(j)));
        piset_have(opis, h.pis, z.pis, pre.pis.insert(j), e);
        piset_add(opis, h.pis, z.pis, pre.pis.insert(j), e);
        // persistent_option: pattern-bound
        let u = oh.po->Some_0->Agree_0;
        popt_have_some(o.po, h.po, z.po, pre.po, u);
        popt_add_some(o.po, h.po, z.po, pre.po, u);
        let opo = PersistentOptionFragment::op(o.po, persistent_option_frag(Some(u)));
        popt_have(opo, h.po, z.po, Some(u), q);
        popt_add(opo, h.po, z.po, Some(u), q);
        cfg_join(
            persist_new(o, h, j, x, a, w, sa, e, q),
            h,
            z,
            State {
                pm: vpm.union_prefer_right(a),
                pim: pre.pim.insert(j, y).union_prefer_right(w),
                ps: pre.ps.insert(j).union(sa),
                pis: pre.pis.insert(j).union(e),
                po: smi::opt_add(Some(u), q),
                ..pre
            },
        );
    }

    pub open spec fn counted_new(o: Fragment, n: nat, x: Multiset<int>, el: int, f: bool) -> Fragment {
        let one = Multiset::empty().insert(el);
        Fragment {
            ms: finite_multiset_frag(finite_multiset_frag(finite_multiset_frag(finite_multiset_frag(
                o.ms.values.sub(one)).values.sub(x)).values.add(one)).values.add(x)),
            c: CountRA { count: CountRA { count: (o.c.count - n) as nat }.count + n },
            b: CountRA { count: CountRA { count: (o.b.count - bool_count(true)) as nat }.count + bool_count(true) },
            b2: CountRA { count: CountRA { count: (o.b2.count - bool_count(f)) as nat }.count + bool_count(f) },
            pc: PersistentCountRA::op(o.pc, PersistentCountRA { count: n }),
            pb: PersistentCountRA::op(PersistentCountRA::op(o.pb, persistent_bool_frag(true)), persistent_bool_frag(f)),
            ..o
        }
    }

    // Multiset, count, bool, persistent count and persistent bool.
    pub proof fn counted(o: Fragment, h: Fragment, z: Fragment, pre: State, n: nat, x: Multiset<int>, el: int, f: bool)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            State::counted_owners_enabled(pre, o, h, n, x, el, f),
        ensures
            State::counted_enabled(pre, n, x, el, f),
            ({
                let post = State {
                    ms: pre.ms.remove(el).sub(x).insert(el).add(x),
                    c: (((pre.c - n) as nat) + n) as nat,
                    b: true,
                    b2: (pre.b2 && !f) || f,
                    pc: smi::nat_max(pre.pc, n),
                    pb: true || f,
                    ..pre
                };
                State::counted_strong(pre, post, n, x, el, f) && Fragment::op(
                    Fragment::op(counted_new(o, n, x, el, f), h),
                    z,
                ) == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        // multiset
        mset_remove_one(o.ms, h.ms, z.ms, pre.ms, el);
        let o1 = finite_multiset_frag(o.ms.values.sub(Multiset::empty().insert(el)));
        let v1 = pre.ms.remove(el);
        mset_remove(o1, h.ms, z.ms, v1, x);
        let o2 = finite_multiset_frag(o1.values.sub(x));
        let v2 = v1.sub(x);
        mset_have_one(o2, h.ms, z.ms, v2, el);
        mset_have(o2, h.ms, z.ms, v2, x);
        mset_add_one(o2, h.ms, z.ms, v2, el);
        let o3 = finite_multiset_frag(o2.values.add(Multiset::empty().insert(el)));
        mset_add(o3, h.ms, z.ms, v2.insert(el), x);
        // count
        count_remove(o.c, h.c, z.c, pre.c, n);
        let oc = CountRA { count: (o.c.count - n) as nat };
        count_have(oc, h.c, z.c, (pre.c - n) as nat, n);
        count_add(oc, h.c, z.c, (pre.c - n) as nat, n);
        // bool: `true` operands
        bool_have_true(o.b, h.b, z.b, pre.b);
        bool_remove_true(o.b, h.b, z.b, pre.b);
        let ob = CountRA { count: (o.b.count - bool_count(true)) as nat };
        bool_add_true(ob, h.b, z.b, false);
        // bool: general operands
        bool_have(o.b2, h.b2, z.b2, pre.b2, f);
        bool_remove(o.b2, h.b2, z.b2, pre.b2, f);
        let ob2 = CountRA { count: (o.b2.count - bool_count(f)) as nat };
        bool_add(ob2, h.b2, z.b2, pre.b2 && !f, f);
        // persistent count and bool
        pcount_have(o.pc, h.pc, z.pc, pre.pc, n);
        pcount_add(o.pc, h.pc, z.pc, pre.pc, n);
        pbool_have_true(o.pb, h.pb, z.pb, pre.pb);
        pbool_add_true(o.pb, h.pb, z.pb, pre.pb);
        let opb = PersistentCountRA::op(o.pb, persistent_bool_frag(true));
        pbool_have(opb, h.pb, z.pb, true, f);
        pbool_add(opb, h.pb, z.pb, true, f);
        cfg_join(
            counted_new(o, n, x, el, f),
            h,
            z,
            State {
                ms: v2.insert(el).add(x),
                c: (((pre.c - n) as nat) + n) as nat,
                b: true,
                b2: (pre.b2 && !f) || f,
                pc: smi::nat_max(pre.pc, n),
                pb: true || f,
                ..pre
            },
        );
    }

    // A variable update from a constant: the reads agree with the fragments.
    pub proof fn bump(o: Fragment, h: Fragment, z: Fragment, pre: State)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            o.v is Some && o.v->Some_0 is Exclusive,
            Fragment::op(o, h).k is Some && Fragment::op(o, h).k->Some_0 is Agree,
            Fragment::op(o, h).k->Some_0->Agree_0 > 0,
        ensures
            State::bump_enabled(pre),
            ({
                let post = State { v: pre.v + pre.k, ..pre };
                State::bump_strong(pre, post) && Fragment::op(
                    Fragment::op(Fragment { v: Some(ExclusiveRA::Exclusive(pre.v + pre.k)), ..o }, h),
                    z,
                ) == <Protocol as Machine>::embed(post)
            }),
    {
        cfg_split(o, h, z, pre);
        const_read(o.k, h.k, z.k, pre.k);
        var_read(o.v, h.v, z.v, pre.v);
        var_update(o.v, h.v, z.v, pre.v, pre.v + pre.k);
        cfg_join(Fragment { v: Some(ExclusiveRA::Exclusive(pre.v + pre.k)), ..o }, h, z, State { v: pre.v + pre.k, ..pre });
    }
}

fn main() {}

} // verus!
