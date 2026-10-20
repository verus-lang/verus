//! Every operation of `StorageResource<K, V, P>` (vstd's storage protocol over
//! `IMap<K, V>`), with its `IMap`/`Protocol`-phrased specification
//! (`dom().disjoint`, `union_prefer_right`, `remove_keys`, `submap_of`), on a
//! `Protocol<int, u64>`: a read-only part `ro` (duplicable; fragments agree)
//! and an exclusive part `own`, with the stored map `ro ∪ own`.
use vstd::prelude::*;
use vstd::resource::storage_protocol::*;

verus! {

pub type M = IMap<int, u64>;

pub ghost enum MPr {
    Frag { ro: Option<M>, own: Option<M> },
    Bad,
}

pub open spec fn agree(a: Option<M>, b: Option<M>) -> bool {
    a is None || b is None || a == b
}

pub open spec fn either(a: Option<M>, b: Option<M>) -> Option<M> {
    if a is Some {
        a
    } else {
        b
    }
}

pub open spec fn ro(a: M) -> MPr {
    MPr::Frag { ro: Some(a), own: None }
}

pub open spec fn own(b: M) -> MPr {
    MPr::Frag { ro: None, own: Some(b) }
}

pub open spec fn full(a: M, b: M) -> MPr {
    MPr::Frag { ro: Some(a), own: Some(b) }
}

impl Protocol<int, u64> for MPr {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (MPr::Frag { ro: r1, own: o1 }, MPr::Frag { ro: r2, own: o2 }) => {
                if agree(r1, r2) && (o1 is None || o2 is None) {
                    MPr::Frag { ro: either(r1, r2), own: either(o1, o2) }
                } else {
                    MPr::Bad
                }
            },
            _ => MPr::Bad,
        }
    }

    open spec fn rel(self, s: M) -> bool {
        match self {
            MPr::Frag { ro: Some(a), own: Some(b) } => a.dom().disjoint(b.dom()) && s
                == a.union_prefer_right(b),
            _ => false,
        }
    }

    open spec fn unit() -> Self {
        MPr::Frag { ro: None, own: None }
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

proof fn full_frame(a: M, b: M, q: MPr, t: M)
    requires
        MPr::rel(MPr::op(full(a, b), q), t),
    ensures
        MPr::op(full(a, b), q) == full(a, b),
        a.dom().disjoint(b.dom()),
        t == a.union_prefer_right(b),
{
}

proof fn owner_ro_frame(a: M, b: M, q: MPr, t: M)
    requires
        MPr::rel(MPr::op(MPr::op(own(b), ro(a)), q), t),
    ensures
        MPr::op(own(b), ro(a)) == full(a, b),
        MPr::op(full(a, b), q) == full(a, b),
        a.dom().disjoint(b.dom()),
        t == a.union_prefer_right(b),
{
}

fn main() {
    proof {
        let tracked mut a = M::tracked_empty();
        a.tracked_insert(1, 10u64);
        let tracked mut b = M::tracked_empty();
        b.tracked_insert(2, 20u64);
        let tracked mut d = M::tracked_empty();
        d.tracked_insert(3, 30u64);
        let ghost (ga, gb, gd) = (a, b, d);
        let ghost ab = ga.union_prefer_right(gb);
        let ghost bd = gb.union_prefer_right(gd);
        let ghost abd = ga.union_prefer_right(bd);
        assert(ab.dom() =~= iset![1, 2]);
        assert(bd.dom() =~= iset![2, 3]);
        assert(abd.dom() =~= iset![1, 2, 3]);
        assert(ab.union_prefer_right(gd) =~= abd);

        // alloc
        let tracked mut s = a;
        s.tracked_union_prefer_right(b);
        let tracked r = StorageResource::<int, u64, MPr>::alloc(full(ga, gb), s);
        let ghost loc = r.loc();

        // validate
        let (q, t) = r.validate();
        full_frame(ga, gb, q, t);
        assert(t == ab);

        // split / join
        assert(MPr::op(ro(ga), own(gb)) == full(ga, gb));
        let tracked (fro, fown) = r.split(ro(ga), own(gb));
        assert(MPr::op(ro(ga), ro(ga)) == ro(ga));
        let tracked (fro, fro2) = fro.split(ro(ga), ro(ga));
        let tracked fro = StorageResource::join(fro, fro2);
        assert(fro.loc() == loc && fro.value() == ro(ga));

        // validate_with_shared
        let tracked mut fown = fown;
        let (q, t) = fown.validate_with_shared(&fro);
        owner_ro_frame(ga, gb, q, t);
        assert(t == ab);

        // join_shared, weaken, validate
        let tracked j = fro.join_shared(&fown);
        assert(incl(full(ga, gb), j.value())) by {
            if j.value() is Bad {
                assert(MPr::op(full(ga, gb), MPr::Bad) == j.value());
            } else {
                let c1 = choose|c: MPr| MPr::op(ro(ga), c) == j.value();
                let c2 = choose|c: MPr| MPr::op(own(gb), c) == j.value();
                assert(j.value() == full(ga, gb));
                assert(MPr::op(full(ga, gb), MPr::unit()) == j.value());
            }
        }
        let tracked w = j.weaken(full(ga, gb));
        let (q, t) = w.validate();
        full_frame(ga, gb, q, t);
        assert(t == ab);

        // guard: the read-only fragment guards `a` (`submap_of`).
        assert forall|q: MPr, t: M| #[trigger] MPr::rel(MPr::op(ro(ga), q), t) implies ga.submap_of(
            t,
        ) by {
        }
        let tracked g = StorageResource::guard(&fro, ga);
        assert(g.contains_key(1) && g[1] == 10);

        // exchange_with_shared: deposit `d` beside `&fro`.
        assert(MPr::op(own(bd), ro(ga)) == full(ga, bd));
        assert forall|q: MPr, t1: M| #[trigger]
            MPr::rel(MPr::op(MPr::op(own(gb), ro(ga)), q), t1) implies {
            &&& MPr::rel(
                MPr::op(MPr::op(own(bd), ro(ga)), q),
                t1.union_prefer_right(gd).remove_keys(IMap::<int, u64>::empty().dom()),
            )
            &&& t1.dom().disjoint(gd.dom())
            &&& IMap::<int, u64>::empty().submap_of(t1.union_prefer_right(gd))
        } by {
            owner_ro_frame(ga, gb, q, t1);
            assert(t1.union_prefer_right(gd).remove_keys(IMap::<int, u64>::empty().dom()) =~= abd);
        }
        let tracked (fown, nothing) = StorageResource::exchange_with_shared(
            fown,
            &fro,
            d,
            own(bd),
            IMap::empty(),
        );
        assert(fown.value() == own(bd) && nothing == IMap::<int, u64>::empty());

        // exchange_nondeterministic_with_shared: withdraw `d` again, or not.
        let ghost nv = iset![(own(gb), gd), (own(bd), IMap::<int, u64>::empty())];
        assert forall|q: MPr, t1: M| #[trigger]
            MPr::rel(MPr::op(MPr::op(own(bd), ro(ga)), q), t1) implies exists|p2: MPr, s2: M, t2: M|
            #![all_triggers]
            {
                &&& set_op(nv, ro(ga)).contains((p2, s2))
                &&& MPr::rel(MPr::op(p2, q), t2)
                &&& t1.dom().disjoint(IMap::<int, u64>::empty().dom())
                &&& t2.dom().disjoint(s2.dom())
                &&& t1.union_prefer_right(IMap::empty()) =~= t2.union_prefer_right(s2)
            } by {
            owner_ro_frame(ga, bd, q, t1);
            assert(nv.contains((own(gb), gd)));
            assert(MPr::op(own(gb), ro(ga)) == full(ga, gb));
            assert(set_op(nv, ro(ga)).contains((full(ga, gb), gd)));
            assert(MPr::rel(MPr::op(full(ga, gb), q), ab));
            assert(t1.union_prefer_right(IMap::empty()) =~= ab.union_prefer_right(gd));
        }
        let tracked (fown, got) = StorageResource::exchange_nondeterministic_with_shared(
            fown,
            &fro,
            IMap::tracked_empty(),
            nv,
        );
        assert(nv.contains((fown.value(), got)));
        let ghost cur = if fown.value() == own(gb) {
            gb
        } else {
            bd
        };
        assert(cur == gb || cur == bd);
        assert(fown.value() == own(cur));
        let tracked r = StorageResource::join(fro, fown);
        assert(r.value() == full(ga, cur));
        let ghost acur = ga.union_prefer_right(cur);

        // withdraw / deposit: take the owned map out and put it back.
        assert forall|q: MPr, t1: M| #[trigger] MPr::rel(MPr::op(full(ga, cur), q), t1) implies {
            &&& MPr::rel(MPr::op(full(ga, IMap::empty()), q), t1.remove_keys(cur.dom()))
            &&& cur.submap_of(t1)
        } by {
            full_frame(ga, cur, q, t1);
            assert(t1.remove_keys(cur.dom()) =~= ga.union_prefer_right(IMap::empty()));
        }
        let tracked (r, taken) = r.withdraw(full(ga, IMap::empty()), cur);
        assert(taken == cur);
        assert forall|q: MPr, t1: M| #[trigger] MPr::rel(MPr::op(full(ga, IMap::empty()), q), t1) implies {
            &&& MPr::rel(MPr::op(full(ga, cur), q), t1.union_prefer_right(cur))
            &&& t1.dom().disjoint(cur.dom())
        } by {
            full_frame(ga, IMap::empty(), q, t1);
            assert(t1 =~= ga);
        }
        let tracked r = r.deposit(taken, full(ga, cur));

        // exchange (no shared fragment): swap nothing for nothing.
        assert forall|q: MPr, t1: M| #[trigger] MPr::rel(MPr::op(full(ga, cur), q), t1) implies {
            &&& MPr::rel(
                MPr::op(full(ga, cur), q),
                t1.union_prefer_right(IMap::empty()).remove_keys(IMap::<int, u64>::empty().dom()),
            )
            &&& t1.dom().disjoint(IMap::<int, u64>::empty().dom())
            &&& IMap::<int, u64>::empty().submap_of(t1.union_prefer_right(IMap::empty()))
        } by {
            full_frame(ga, cur, q, t1);
            assert(t1.union_prefer_right(IMap::empty()).remove_keys(IMap::<int, u64>::empty().dom())
                =~= t1);
        }
        let tracked (r, _e) = StorageResource::exchange(
            r,
            IMap::tracked_empty(),
            full(ga, cur),
            IMap::empty(),
        );

        // exchange_nondeterministic (no shared fragment)
        let ghost nv1 = iset![(full(ga, cur), IMap::<int, u64>::empty())];
        assert forall|q: MPr, t1: M| #[trigger] MPr::rel(MPr::op(full(ga, cur), q), t1) implies exists|
            p2: MPr,
            s2: M,
            t2: M,
        |
            #![all_triggers]
            {
                &&& nv1.contains((p2, s2))
                &&& MPr::rel(MPr::op(p2, q), t2)
                &&& t1.dom().disjoint(IMap::<int, u64>::empty().dom())
                &&& t2.dom().disjoint(s2.dom())
                &&& t1.union_prefer_right(IMap::empty()) =~= t2.union_prefer_right(s2)
            } by {
            full_frame(ga, cur, q, t1);
            assert(nv1.contains((full(ga, cur), IMap::<int, u64>::empty())));
            assert(t1.union_prefer_right(IMap::empty()) =~= t1);
        }
        let tracked (r, _e) = StorageResource::exchange_nondeterministic(
            r,
            IMap::tracked_empty(),
            nv1,
        );

        // update
        let tracked r = r.update(full(ga, cur));
        assert(r.loc() == loc && r.value() == full(ga, cur));
    }
}

} // verus!
