//! The statement calculus of `vstd::resource::tsm_calculus`, used by hand: a machine's
//! configuration split into and joined from its fields' (`cfg_split`, `cfg_join`), and
//! chains of step lemmas that establish the frontend's enabling condition and strong
//! relation of transitions with every statement form the lemmas cover (map, imap, set,
//! iset and option fields; singleton, pattern-bound and general operands; remove, have and
//! add; have after add), with no quantifier in the proofs.
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
        transition! { rm_have(a: int, b: int) {
            remove m -= [a => 1];
            have m >= [b => 2];
            add m += [a => 3];
        } }
        transition! { add_have(a: int, b: int) {
            remove o -= Some(let x);
            require(x > 0);
            remove m -= [a => x];
            add m += [a => x + 1];
            have m >= [b => 2];
            add o += Some(x);
        } }
        transition! { general(x: Map<int, int>, y: Map<int, int>, p: Set<int>, q: Option<int>) {
            remove m -= (x);
            have m >= (y);
            add m += (x);
            remove s -= (p);
            add s += (p);
            have o >= (q);
        } }
        transition! { infinite(k: int, v: int, w: IMap<int, int>, e: ISet<int>) {
            remove im -= [k => let old];
            add im += [k => old + v];
            have im >= (w);
            remove is -= set {k};
            have is >= (e);
            add is += set {k};
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(rm_have)] fn rm_have_inductive(pre: Self, post: Self, a: int, b: int) {}
        #[inductive(add_have)] fn add_have_inductive(pre: Self, post: Self, a: int, b: int) {}
        #[inductive(general)] fn general_inductive(pre: Self, post: Self, x: Map<int, int>, y: Map<int, int>, p: Set<int>, q: Option<int>) {}
        #[inductive(infinite)] fn infinite_inductive(pre: Self, post: Self, k: int, v: int, w: IMap<int, int>, e: ISet<int>) {}
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

    // ---- remove -> have -> add of one map field, to the strong relation and the output
    //      configuration
    pub proof fn rm_have(o: Fragment, h: Fragment, z: Fragment, pre: State, a: int, b: int)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            map_owns(o.m, IMap::empty().insert(a, 1int)),
            map_owns(
                MapFragment::op(map_remove_many(o.m, IMap::empty().insert(a, 1int).dom()), h.m),
                IMap::empty().insert(b, 2int),
            ),
        ensures
            State::rm_have_enabled(pre, a, b),
            State::rm_have_strong(pre, State { m: pre.m.remove(a).insert(a, 3), ..pre }, a, b),
            Fragment::op(
                Fragment::op(
                    Fragment {
                        m: MapFragment::op(
                            map_remove_many(o.m, IMap::empty().insert(a, 1int).dom()),
                            map_frag(IMap::empty().insert(a, 3int)),
                        ),
                        ..o
                    },
                    h,
                ),
                z,
            ) == <Protocol as Machine>::embed(State { m: pre.m.remove(a).insert(a, 3), ..pre }),
    {
        cfg_split(o, h, z, pre);
        map_remove_one(o.m, h.m, z.m, pre.m, a, 1);
        let om1 = map_remove_many(o.m, IMap::empty().insert(a, 1int).dom());
        let vm1 = pre.m.remove(a);
        map_have_one(om1, h.m, z.m, vm1, b, 2);
        map_add_one(om1, h.m, z.m, vm1, a, 3);
        let post = State { m: vm1.insert(a, 3), ..pre };
        cfg_join(Fragment { m: MapFragment::op(om1, map_frag(IMap::empty().insert(a, 3int))), ..o }, h, z, post);
    }

    // ---- a pattern-bound option value, and a have after an add of the same field
    pub proof fn add_have(o: Fragment, h: Fragment, z: Fragment, pre: State, a: int, b: int)
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            option_contains_operand(o.o, Some(o.o->Some_0->Exclusive_0)),
            o.o->Some_0->Exclusive_0 > 0,
            map_owns(o.m, IMap::empty().insert(a, o.o->Some_0->Exclusive_0)),
            map_owns(
                MapFragment::op(
                    MapFragment::op(
                        map_remove_many(o.m, IMap::empty().insert(a, o.o->Some_0->Exclusive_0).dom()),
                        map_frag(IMap::empty().insert(a, o.o->Some_0->Exclusive_0 + 1)),
                    ),
                    h.m,
                ),
                IMap::empty().insert(b, 2int),
            ),
        ensures
            State::add_have_enabled(pre, a, b),
    {
        cfg_split(o, h, z, pre);
        let x = o.o->Some_0->Exclusive_0;
        opt_remove_some(o.o, h.o, z.o, pre.o, x);
        map_remove_one(o.m, h.m, z.m, pre.m, a, x);
        let om = map_remove_many(o.m, IMap::empty().insert(a, x).dom());
        let vm = pre.m.remove(a);
        // the add's safety condition guards the rest of the chain
        if !vm.dom().contains(a) {
            map_add_one(om, h.m, z.m, vm, a, x + 1);
            let om = MapFragment::op(om, map_frag(IMap::empty().insert(a, x + 1)));
            map_have_one(om, h.m, z.m, vm.insert(a, x + 1), b, 2);
        }
    }

    // ---- general operands of map, set and option fields
    pub proof fn general(
        o: Fragment, h: Fragment, z: Fragment, pre: State,
        x: Map<int, int>, y: Map<int, int>, p: Set<int>, q: Option<int>,
    )
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            map_owns(o.m, x.to_imap()),
            map_owns(MapFragment::op(map_remove_many(o.m, x.to_imap().dom()), h.m), y.to_imap()),
            set_owns(o.s, p.to_iset()),
            option_contains_operand(OptionFragment::op(o.o, h.o), q),
        ensures
            State::general_enabled(pre, x, y, p, q),
            State::general_strong(
                pre,
                State {
                    m: pre.m.remove_keys(x.dom()).union_prefer_right(x),
                    s: pre.s.difference(p).union(p),
                    ..pre
                },
                x, y, p, q,
            ),
            Fragment::op(
                Fragment::op(
                    Fragment {
                        m: MapFragment::op(map_remove_many(o.m, x.to_imap().dom()), map_frag(x.to_imap())),
                        s: SetFragment::op(set_remove_many(o.s, p.to_iset()), set_frag(p.to_iset())),
                        ..o
                    },
                    h,
                ),
                z,
            ) == <Protocol as Machine>::embed(State {
                m: pre.m.remove_keys(x.dom()).union_prefer_right(x),
                s: pre.s.difference(p).union(p),
                ..pre
            }),
    {
        cfg_split(o, h, z, pre);
        map_remove(o.m, h.m, z.m, pre.m, x);
        let om = map_remove_many(o.m, x.to_imap().dom());
        let vm = pre.m.remove_keys(x.dom());
        map_have(om, h.m, z.m, vm, y);
        assert(vm.dom().disjoint(x.dom()));
        map_add(om, h.m, z.m, vm, x);
        set_remove(o.s, h.s, z.s, pre.s, p);
        let os = set_remove_many(o.s, p.to_iset());
        let vs = pre.s.difference(p);
        assert(vs.disjoint(p));
        set_add(os, h.s, z.s, vs, p);
        opt_have(o.o, h.o, z.o, pre.o, q);
        let post = State { m: vm.union_prefer_right(x), s: vs.union(p), ..pre };
        cfg_join(
            Fragment {
                m: MapFragment::op(om, map_frag(x.to_imap())),
                s: SetFragment::op(os, set_frag(p.to_iset())),
                ..o
            },
            h, z, post,
        );
    }

    // ---- infinite views: a pattern-bound imap value, general imap/iset haves
    pub proof fn infinite(
        o: Fragment, h: Fragment, z: Fragment, pre: State, k: int, v: int, w: IMap<int, int>, e: ISet<int>,
    )
        requires
            Fragment::op(Fragment::op(o, h), z) == <Protocol as Machine>::embed(pre),
            map_owns(o.im, IMap::empty().insert(k, o.im.at(k)->Some_0->Exclusive_0)),
            map_owns(
                MapFragment::op(
                    MapFragment::op(
                        map_remove_many(o.im, IMap::empty().insert(k, o.im.at(k)->Some_0->Exclusive_0).dom()),
                        map_frag(IMap::empty().insert(k, o.im.at(k)->Some_0->Exclusive_0 + v)),
                    ),
                    h.im,
                ),
                w,
            ),
            set_owns(o.is, ISet::empty().insert(k)),
            set_owns(SetFragment::op(set_remove_many(o.is, ISet::empty().insert(k)), h.is), e),
        ensures
            State::infinite_enabled(pre, k, v, w, e),
    {
        cfg_split(o, h, z, pre);
        let old = o.im.at(k)->Some_0->Exclusive_0;
        imap_remove_one(o.im, h.im, z.im, pre.im, k, old);
        let oim = map_remove_many(o.im, IMap::empty().insert(k, old).dom());
        let vim = pre.im.remove(k);
        imap_add_one(oim, h.im, z.im, vim, k, old + v);
        let oim = MapFragment::op(oim, map_frag(IMap::empty().insert(k, old + v)));
        imap_have(oim, h.im, z.im, vim.insert(k, old + v), w);
        iset_remove_one(o.is, h.is, z.is, pre.is, k);
        let ois = set_remove_many(o.is, ISet::empty().insert(k));
        let vis = pre.is.remove(k);
        iset_have(ois, h.is, z.is, vis, e);
        iset_add_one(ois, h.is, z.is, vis, k);
    }

    // ---- the remaining forms on single components
    pub proof fn components(
        om: MapFragment<int, int>, hm: MapFragment<int, int>, zm: MapFragment<int, int>, vm: IMap<int, int>,
        os: SetFragment<int>, hs: SetFragment<int>, zs: SetFragment<int>, vs: ISet<int>,
        oo: OptionFragment<int>, ho: OptionFragment<int>, zo: OptionFragment<int>, vo: Option<int>,
        fm: Map<int, int>, fs: Set<int>, x: IMap<int, int>, t: ISet<int>, u: Option<int>,
    )
        requires
            cfg(om, hm, zm, map_frag(vm)),
            cfg(os, hs, zs, set_frag(vs)),
            cfg(oo, ho, zo, option_frag(vo)),
            map_owns(om, x),
            set_owns(os, t),
            option_contains_operand(oo, u),
    {
        // general imap/iset removals, and the option forms
        imap_remove(om, hm, zm, vm, x);
        iset_remove(os, hs, zs, vs, t);
        opt_remove(oo, ho, zo, vo, u);
        assert(vo is None || u is None || vo == u);
        let oo1 = option_remove_operand(oo, u);
        let vo1 = vstd::state_machine_internal::opt_sub(vo, u);
        if u is Some {
            opt_add(oo1, ho, zo, vo1, u);
            opt_add_some(oo1, ho, zo, vo1, u->Some_0);
        }
        // general imap/iset additions after the removals
        let om1 = map_remove_many(om, x.dom());
        let vm1 = vm.remove_keys(x.dom());
        assert(vm1.dom().disjoint(x.dom()));
        imap_add(om1, hm, zm, vm1, x);
        let os1 = set_remove_many(os, t);
        let vs1 = vs.difference(t);
        assert(vs1.disjoint(t));
        iset_add(os1, hs, zs, vs1, t);
        // a finite set's general have
        if cfg(os, hs, zs, set_frag(fs.to_iset())) && set_owns(SetFragment::op(os, hs), fs.to_iset()) {
            set_have(os, hs, zs, fs, fs);
        }
        // a finite set's singleton have
        if cfg(os, hs, zs, set_frag(fs.to_iset())) && set_owns(SetFragment::op(os, hs), ISet::empty().insert(3int)) {
            set_have_one(os, hs, zs, fs, 3);
            assert(fs.contains(3));
        }
        // a finite map's general have
        if cfg(om, hm, zm, map_frag(fm.to_imap())) && map_owns(MapFragment::op(om, hm), x) && x == fm.to_imap() {
            map_have(om, hm, zm, fm, fm);
        }
        // an option's pattern-bound have
        if option_contains_operand(OptionFragment::op(oo, ho), Some(7int)) {
            opt_have_some(oo, ho, zo, vo, 7);
            assert(vo == Some(7int));
        }
        // a map's singleton have of the borrowed part
        if map_owns(MapFragment::op(om, hm), IMap::empty().insert(1int, 2int)) {
            imap_have_one(om, hm, zm, vm, 1, 2);
            assert(vm.contains_pair(1, 2));
        }
        // iset singleton have
        if set_owns(SetFragment::op(os, hs), ISet::empty().insert(5int)) {
            iset_have_one(os, hs, zs, vs, 5);
            assert(vs.contains(5));
        }
    }

    // ---- a borrowed singleton token's entry after removals (generic interface)
    pub proof fn token_observed(
        o: MapFragment<int, int>, h: MapFragment<int, int>, z: MapFragment<int, int>, v: IMap<int, int>,
        c: MapFragment<int, int>, a: int, b: int,
    )
        requires
            cfg(o, h, z, map_frag(v)),
            h == MapFragment::op(map_frag(IMap::empty().insert(b, 2int)), c),
            map_owns(o, IMap::empty().insert(a, 1int)),
        ensures
            v.contains_pair(a, 1),
            v.remove(a).contains_pair(b, 2),
    {
        map_frag_valid(v);
        map_token_observed(o, h, z, map_frag(v), c, IMap::empty().insert(a, 1int).dom(), b, 2);
        imap_remove_one(o, h, z, v, a, 1);
        imap_have_one(map_remove_many(o, IMap::empty().insert(a, 1int).dom()), h, z, v.remove(a), b, 2);
    }
}

fn main() {}

} // verus!
