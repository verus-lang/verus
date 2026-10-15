//! Whole and infinite sets retain checked separation through bulk operations.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::*;
use vstd::resource::tsm_collections::*;
verus! {

broadcast use vstd::iset::group_iset_lemmas;

pub struct Sets;

impl Machine for Sets {
    type State = ISet<int>;

    type Fragment = SetFragment<int>;

    open spec fn invariant(s: ISet<int>) -> bool {
        true
    }

    open spec fn embed(s: ISet<int>) -> Self::Fragment {
        set_frag(s)
    }
}

proof fn remove_infinite_set() {
    let local = ISet::new(|v: int| v >= 0);
    let rest = local.complement();
    let tracked token = Token::<Sets>::alloc_state(ISet::full());
    set_join(local, rest);
    assert(local.union(rest) =~= ISet::<int>::full());
    let tracked (token, frame) = token.split(set_frag(local), set_frag(rest));
    let owned = token.fragment();
    let after = set_remove_many(owned, local);
    assert(frame_update::<Sets>(owned, after)) by {
        assert forall|f: SetFragment<int>, s: ISet<int>|
            Sets::invariant(s) && SetFragment::op(owned, f) == Sets::embed(s) implies exists|
            post: ISet<int>,
        |
            Sets::invariant(post) && SetFragment::op(after, f) == Sets::embed(post) by {
            set_remove_many_frame(owned, f, s, local);
            let post = s.difference(local);
            assert(Sets::invariant(post));
            assert(SetFragment::op(after, f) == Sets::embed(post));
        };
    }
    let tracked token = token.update(after);
    let tracked full = token.join(frame);
    full.validate();
}

proof fn disjoint_bulk_addition() {
    let local = ISet::empty().insert(0int);
    let frame = ISet::empty().insert(1int);
    let whole = local.union(frame);
    let added = ISet::new(|v: int| v >= 2);
    set_join(local, frame);
    set_add_many_frame(set_frag(local), set_frag(frame), whole, added);
}

proof fn empty_bulk_operations<K>(set: ISet<K>) {
    let owned = set_frag(set);
    owned.op_unit();
    set_remove_many_frame(owned, SetFragment::unit(), set, ISet::empty());
    set_add_many_frame(owned, SetFragment::unit(), set, ISet::empty());
}

proof fn persistent_infinite_observation() {
    let set = ISet::new(|v: int| v >= 0);
    let observed = ISet::new(|v: int| v >= 5);
    persistent_set_frag(set).op_unit();
    persistent_set_have_many_frame(
        persistent_set_frag(set),
        PersistentSetFragment::unit(),
        set,
        observed,
    );
}

fn main() {
    proof {
        remove_infinite_set();
    }
}

} // verus!
