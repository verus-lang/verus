//! A reduced version of `state_machines/counting.rs` and the RefCell tutorial.
//! A variable counter controls a stored PCell permission, and multiset reader
//! fragments guard that permission. All protocol operations below have checked
//! bodies; storage ownership and borrowing use the existing Leaf interface.
use vstd::cell::pcell_maybe_uninit::{PCell, PointsTo};
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::product::ProductRA;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_storage::*;

verus! {

broadcast use {
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
    vstd::multiset::group_multiset_axioms,
    vstd::multiset::group_multiset_properties,
};

pub struct Readers<T> {
    pub values: Multiset<T>,
}

impl<T> ResourceAlgebra for Readers<T> {
    open spec fn valid(self) -> bool {
        true
    }

    open spec fn op(a: Self, b: Self) -> Self {
        Self { values: a.values.add(b.values) }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        assert(a.values.add(b.values.add(c.values)) =~= a.values.add(b.values).add(c.values));
    }

    proof fn commutative(a: Self, b: Self) {
        assert(a.values.add(b.values) =~= b.values.add(a.values));
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

impl<T> PCM for Readers<T> {
    open spec fn unit() -> Self {
        Self { values: Multiset::empty() }
    }

    proof fn op_unit(self) {
        assert(self.values.add(Multiset::empty()) =~= self.values);
    }

    proof fn unit_valid() {
    }
}

type Permission = PointsTo<u64>;

type Counter = Option<(nat, Permission)>;

type Fragment = ProductRA<Option<ExclusiveRA<Counter>>, Readers<Permission>>;

pub ghost struct State {
    pub counter: Counter,
    pub stored: Option<Permission>,
    pub readers: Multiset<Permission>,
}

pub struct RefCounter;

impl Machine for RefCounter {
    type State = State;

    type Fragment = Fragment;

    open spec fn invariant(state: State) -> bool {
        match state.counter {
            None => state.stored is None && state.readers == Multiset::empty(),
            Some((n, p)) => state.stored == Some(p) && state.readers.count(p) == n && (forall|
                other: Permission,
            |
                other != p ==> #[trigger] state.readers.count(other) == 0),
        }
    }

    open spec fn embed(state: State) -> Fragment {
        ProductRA {
            left: Some(ExclusiveRA::Exclusive(state.counter)),
            right: Readers { values: state.readers },
        }
    }
}

impl StorageMachine for RefCounter {
    type Key = int;

    type Value = Permission;

    open spec fn storage(state: State) -> IMap<int, Permission> {
        match state.stored {
            None => IMap::empty(),
            Some(p) => IMap::empty().insert(0, p),
        }
    }
}

pub open spec fn control(counter: Counter) -> Fragment {
    ProductRA {
        left: Some(ExclusiveRA::Exclusive(counter)),
        right: Readers { values: Multiset::empty() },
    }
}

pub open spec fn reader(p: Permission) -> Fragment {
    ProductRA { left: None, right: Readers { values: Multiset::singleton(p) } }
}

pub open spec fn stored(p: Permission) -> IMap<int, Permission> {
    IMap::empty().insert(0, p)
}

/// From possession of the variable field, the untouched frame has no counter.
proof fn control_frame(counter: Counter, frame: Fragment, state: State)
    requires
        RefCounter::invariant(state),
        Fragment::op(control(counter), frame) == RefCounter::embed(state),
    ensures
        state.counter == counter,
        frame.left is None,
        frame.right.values == state.readers,
{
    assert(Multiset::<Permission>::empty().add(frame.right.values) =~= frame.right.values);
}

proof fn initialize_empty() -> (tracked out: StorageToken<RefCounter>)
    ensures
        out.fragment() == control(None),
{
    let state = State { counter: None, stored: None, readers: Multiset::empty() };
    StorageToken::alloc_state(state, IMap::tracked_empty())
}

proof fn deposit(
    tracked token: StorageToken<RefCounter>,
    tracked permission: Permission,
) -> (tracked out: StorageToken<RefCounter>)
    requires
        token.fragment() == control(None),
    ensures
        out.loc() == token.loc(),
        out.fragment() == control(Some((0, permission))),
{
    let p = permission;
    let tracked mut base = IMap::tracked_empty();
    base.tracked_insert(0, permission);
    let new = control(Some((0, p)));
    assert(frame_exchange::<RefCounter>(token.fragment(), base, new, IMap::empty())) by {
        assert forall|frame: Fragment, state: State|
            RefCounter::invariant(state) && Fragment::op(token.fragment(), frame)
                == RefCounter::embed(state) implies {
            &&& RefCounter::storage(state).dom().disjoint(base.dom())
            &&& IMap::<int, Permission>::empty().submap_of(
                RefCounter::storage(state).union_prefer_right(base),
            )
            &&& exists|next: State|
                RefCounter::invariant(next) && Fragment::op(new, frame) == RefCounter::embed(next)
                    && RefCounter::storage(next) == RefCounter::storage(state).union_prefer_right(
                    base,
                ).remove_keys(IMap::<int, Permission>::empty().dom())
        } by {
            control_frame(None, frame, state);
            let next = State { counter: Some((0, p)), stored: Some(p), readers: Multiset::empty() };
            assert(RefCounter::invariant(next));
            assert(RefCounter::storage(next) =~= RefCounter::storage(state).union_prefer_right(
                base,
            ).remove_keys(IMap::<int, Permission>::empty().dom()));
            assert(Fragment::op(new, frame) == RefCounter::embed(next));
        }
    };
    token.exchange(base, new, IMap::empty()).0
}

proof fn new_reader_frame(n: nat, p: Permission)
    ensures
        frame_exchange::<RefCounter>(
            control(Some((n, p))),
            IMap::empty(),
            Fragment::op(control(Some((n + 1, p))), reader(p)),
            IMap::empty(),
        ),
{
    let new_control = control(Some((n + 1, p)));
    let new = Fragment::op(new_control, reader(p));
    let old = control(Some((n, p)));
    assert(frame_exchange::<RefCounter>(old, IMap::empty(), new, IMap::empty())) by {
        assert forall|frame: Fragment, state: State|
            RefCounter::invariant(state) && Fragment::op(old, frame) == RefCounter::embed(
                state,
            ) implies {
            &&& RefCounter::storage(state).dom().disjoint(IMap::<int, Permission>::empty().dom())
            &&& IMap::<int, Permission>::empty().submap_of(
                RefCounter::storage(state).union_prefer_right(IMap::empty()),
            )
            &&& exists|next: State|
                RefCounter::invariant(next) && Fragment::op(new, frame) == RefCounter::embed(next)
                    && RefCounter::storage(next) == RefCounter::storage(state).union_prefer_right(
                    IMap::empty(),
                ).remove_keys(IMap::<int, Permission>::empty().dom())
        } by {
            control_frame(Some((n, p)), frame, state);
            let next = State {
                counter: Some((n + 1, p)),
                stored: state.stored,
                readers: state.readers.insert(p),
            };
            assert(RefCounter::invariant(next));
            assert(RefCounter::storage(next) =~= RefCounter::storage(state).union_prefer_right(
                IMap::empty(),
            ).remove_keys(IMap::<int, Permission>::empty().dom()));
            assert(Multiset::singleton(p).add(frame.right.values) =~= next.readers);
            assert(Fragment::op(new, frame).right.values =~= next.readers);
            assert(Fragment::op(new, frame).left == RefCounter::embed(next).left);
            assert(Fragment::op(new, frame) == RefCounter::embed(next));
        }
    };
}

proof fn new_reader(tracked token: StorageToken<RefCounter>, n: nat, p: Permission) -> (tracked out:
    (StorageToken<RefCounter>, StorageToken<RefCounter>))
    requires
        token.fragment() == control(Some((n, p))),
    ensures
        out.0.loc() == token.loc(),
        out.1.loc() == token.loc(),
        out.0.fragment() == control(Some((n + 1, p))),
        out.1.fragment() == reader(p),
{
    new_reader_frame(n, p);
    let new_control = control(Some((n + 1, p)));
    let new = Fragment::op(new_control, reader(p));
    let tracked token = token.exchange(IMap::tracked_empty(), new, IMap::empty()).0;
    token.split(new_control, reader(p))
}

/// Like Rc's clone operation, this creates a reader while retaining a borrowed
/// reader token. The existing guard on `read` remains usable afterward.
proof fn clone_reader(
    tracked token: StorageToken<RefCounter>,
    tracked read: &StorageToken<RefCounter>,
    n: nat,
    p: Permission,
) -> (tracked out: (StorageToken<RefCounter>, StorageToken<RefCounter>))
    requires
        token.loc() == read.loc(),
        token.fragment() == control(Some((n, p))),
        read.fragment() == reader(p),
    ensures
        out.0.loc() == token.loc(),
        out.1.loc() == token.loc(),
        out.0.fragment() == control(Some((n + 1, p))),
        out.1.fragment() == reader(p),
{
    new_reader_frame(n, p);
    let new_control = control(Some((n + 1, p)));
    let new = Fragment::op(new_control, reader(p));
    frame_exchange_with_extra::<RefCounter>(
        token.fragment(),
        IMap::empty(),
        new,
        IMap::empty(),
        read.fragment(),
    );
    let tracked token = token.exchange_with_shared(
        read,
        IMap::tracked_empty(),
        new,
        IMap::empty(),
    ).0;
    token.split(new_control, reader(p))
}

/// A reader token guards the permission for its own element, including when
/// the variable counter is owned elsewhere.
proof fn reader_guard(tracked token: &StorageToken<RefCounter>, p: Permission) -> (tracked out:
    &IMap<int, Permission>)
    requires
        token.fragment() == reader(p),
    ensures
        *out == stored(p),
{
    assert(frame_guard::<RefCounter>(token.fragment(), stored(p))) by {
        assert forall|frame: Fragment, state: State|
            RefCounter::invariant(state) && Fragment::op(token.fragment(), frame)
                == RefCounter::embed(state) implies stored(p).submap_of(
            RefCounter::storage(state),
        ) by {
            assert(state.readers.count(p) >= 1);
            assert(state.counter is Some);
            let (n, q) = state.counter->Some_0;
            assert(q == p);
        }
    };
    token.guard(stored(p))
}

proof fn drop_reader(
    tracked token: StorageToken<RefCounter>,
    tracked read: StorageToken<RefCounter>,
    n: nat,
    p: Permission,
) -> (tracked out: StorageToken<RefCounter>)
    requires
        token.loc() == read.loc(),
        token.fragment() == control(Some((n, p))),
        read.fragment() == reader(p),
        n >= 1,
    ensures
        out.loc() == token.loc(),
        out.fragment() == control(Some(((n - 1) as nat, p))),
{
    let tracked token = token.join(read);
    let new = control(Some(((n - 1) as nat, p)));
    assert(frame_exchange::<RefCounter>(token.fragment(), IMap::empty(), new, IMap::empty())) by {
        assert forall|frame: Fragment, state: State|
            RefCounter::invariant(state) && Fragment::op(token.fragment(), frame)
                == RefCounter::embed(state) implies {
            &&& RefCounter::storage(state).dom().disjoint(IMap::<int, Permission>::empty().dom())
            &&& IMap::<int, Permission>::empty().submap_of(
                RefCounter::storage(state).union_prefer_right(IMap::empty()),
            )
            &&& exists|next: State|
                RefCounter::invariant(next) && Fragment::op(new, frame) == RefCounter::embed(next)
                    && RefCounter::storage(next) == RefCounter::storage(state).union_prefer_right(
                    IMap::empty(),
                ).remove_keys(IMap::<int, Permission>::empty().dom())
        } by {
            assert(state.counter == Some((n, p)));
            assert(frame.left is None);
            let next = State {
                counter: Some(((n - 1) as nat, p)),
                stored: state.stored,
                readers: frame.right.values,
            };
            assert(next.readers.count(p) == (n - 1) as nat);
            assert forall|q: Permission| q != p implies #[trigger] next.readers.count(q) == 0 by {
                assert(state.readers.count(q) == 0);
            };
            assert(RefCounter::invariant(next));
            assert(RefCounter::storage(next) =~= RefCounter::storage(state).union_prefer_right(
                IMap::empty(),
            ).remove_keys(IMap::<int, Permission>::empty().dom()));
            assert(Multiset::<Permission>::empty().add(frame.right.values) =~= next.readers);
            assert(Fragment::op(new, frame) == RefCounter::embed(next));
        }
    };
    token.exchange(IMap::tracked_empty(), new, IMap::empty()).0
}

proof fn withdraw(tracked token: StorageToken<RefCounter>, p: Permission) -> (tracked out: (
    StorageToken<RefCounter>,
    Permission,
))
    requires
        token.fragment() == control(Some((0, p))),
    ensures
        out.0.loc() == token.loc(),
        out.0.fragment() == control(None),
        out.1 == p,
{
    let new = control(None);
    assert(frame_exchange::<RefCounter>(token.fragment(), IMap::empty(), new, stored(p))) by {
        assert forall|frame: Fragment, state: State|
            RefCounter::invariant(state) && Fragment::op(token.fragment(), frame)
                == RefCounter::embed(state) implies {
            &&& RefCounter::storage(state).dom().disjoint(IMap::<int, Permission>::empty().dom())
            &&& stored(p).submap_of(RefCounter::storage(state).union_prefer_right(IMap::empty()))
            &&& exists|next: State|
                RefCounter::invariant(next) && Fragment::op(new, frame) == RefCounter::embed(next)
                    && RefCounter::storage(next) == RefCounter::storage(state).union_prefer_right(
                    IMap::empty(),
                ).remove_keys(stored(p).dom())
        } by {
            control_frame(Some((0, p)), frame, state);
            assert(state.readers =~= Multiset::empty()) by {
                assert forall|q: Permission| #[trigger] state.readers.count(q) == 0 by {};
            };
            let next = State { counter: None, stored: None, readers: Multiset::empty() };
            assert(RefCounter::invariant(next));
            assert(RefCounter::storage(next) =~= RefCounter::storage(state).union_prefer_right(
                IMap::empty(),
            ).remove_keys(stored(p).dom()));
            assert(Fragment::op(new, frame) == RefCounter::embed(next));
        }
    };
    let tracked (token, mut base) = token.exchange(IMap::tracked_empty(), new, stored(p));
    let tracked permission = base.tracked_remove(0);
    (token, permission)
}

fn main() {
    let (cell, Tracked(mut permission)) = PCell::<u64>::empty();
    cell.put(Tracked(&mut permission), 42);
    let ghost p = permission;
    let tracked token = initialize_empty();
    let tracked token = deposit(token, permission);
    let tracked (token, read1) = new_reader(token, 0, p);

    let tracked guarded = reader_guard(&read1, p);
    let tracked permission_ref = guarded.tracked_borrow(0);
    let first = cell.borrow(Tracked(permission_ref));
    assert(*first == 42);

    // The guard is still live while other tokens perform protocol operations.
    let tracked (token, read2) = clone_reader(token, &read1, 1, p);
    let tracked guarded2 = reader_guard(&read2, p);
    let alias = cell.borrow(Tracked(guarded2.tracked_borrow(0)));
    assert(*alias == *first);
    let tracked token = drop_reader(token, read2, 2, p);
    assert(*first == 42);
    let second = cell.borrow(Tracked(guarded.tracked_borrow(0)));
    assert(*second == 42);

    let tracked token = drop_reader(token, read1, 1, p);
    let tracked (token, mut permission) = withdraw(token, p);
    cell.replace(Tracked(&mut permission), 77);
    let value = cell.take(Tracked(&mut permission));
    assert(value == 77);
}

} // verus!
