//! The generic (default) interface for each sharding strategy: one module per
//! group of strategies, each a machine and a client of its trusted-style API with
//! checked bodies (merged from the former generic_tokens{,_variable,_option,
//! _persistent,_storage_map,_labels}.rs). Covers map/set tokens and a placeholder
//! from `arbitrary()`, variable/constant fields (constants read through the
//! instance's descriptor; an operation that consumes no token), option and
//! storage_option/storage_imap fields, persistent strategies, a machine with one
//! storage_map field, and labeled machines (labels are the operations' first
//! arguments).

// ----------------------------------------------------------------------------
// Checked field tokens over the raw protocol (`#[verified_generic_tokens]`):
// the trusted macro's API and specifications, with checked bodies. Covers
// map/set tokens, a placeholder from `arbitrary()`, bulk initialization,
// deposits/withdrawals over two storage maps, guards, borrowed inputs, and
// an updated `not_tokenized` field.
pub mod map_set {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        #[verified_generic_tokens]
        P {
            fields {
                #[sharding(set)]
                pub unused: Set<int>,

                #[sharding(map)]
                pub owner: Map<int, int>,

                #[sharding(storage_map)]
                pub left: Map<int, int>,

                #[sharding(storage_map)]
                pub right: Map<int, int>,

                #[sharding(not_tokenized)]
                pub count: int,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.left.dom().contains(k)
                &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.right.dom().contains(k)
                &&& forall|k: int| #[trigger] self.owner.dom().contains(k) ==>
                        self.left[k] == self.owner[k] && self.right[k] == self.owner[k]
                &&& forall|k: int| #[trigger] self.unused.contains(k) ==> !self.owner.dom().contains(k)
            }

            init!{
                initialize(free: Set<int>) {
                    init unused = free;
                    init owner = Map::empty();
                    init left = Map::empty();
                    init right = Map::empty();
                    init count = 0;
                }
            }

            transition!{
                insert(k: int, v: int) {
                    remove unused -= set { k };
                    add owner += [k => v];
                    deposit left += [k => v];
                    deposit right += [k => v];
                    update count = pre.count + 1;
                }
            }

            transition!{
                take(k: int) {
                    remove owner -= [k => let v];
                    withdraw left -= [k => v];
                    withdraw right -= [k => v];
                    add unused += set { k };
                }
            }

            transition!{
                two_have(k: int, e: int) {
                    have owner >= [k => let v];
                    have unused >= set { e };
                    require v > 0;
                    assert k != e;
                }
            }

            property!{
                two_prop(k: int, e: int) {
                    have owner >= [k => let v];
                    have unused >= set { e };
                    require v > 0;
                    assert k != e;
                }
            }

            property!{
                peek(k: int) {
                    have owner >= [k => let v];
                    guard left >= [k => v];
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, free: Set<int>) { }

            #[inductive(insert)]
            fn insert_inductive(pre: Self, post: Self, k: int, v: int) { }

            #[inductive(two_have)]
            fn two_have_inductive(pre: Self, post: Self, k: int, e: int) { }

            #[inductive(take)]
            fn take_inductive(pre: Self, post: Self, k: int) { }
        }
    }

    verus! {
    proof fn client() {
        let free = Set::<int>::empty().insert(1).insert(2);
        let tracked (Tracked(inst), Tracked(unused), Tracked(owner)) =
            P::Instance::initialize(free, Map::tracked_empty(), Map::tracked_empty());
        let tracked mut unused = unused;
        assert(unused.set().contains(1));
        let tracked u1 = unused.remove(1);
        let tracked o1 = inst.insert(1, 10, u1, 10, 10);
        assert(o1.key() == 1 && o1.value() == 10);
        let tracked g = inst.peek(1, &o1);
        assert(*g == 10);
        let tracked (Tracked(u1b), Tracked(l), Tracked(r)) = inst.take(1, o1);
        assert(l == 10 && r == 10 && u1b.element() == 1);
        let tracked mut u1b = u1b;
        let tracked u2 = unused.remove(2);
        u1b.unique(&u2);
        assert(u1b.element() != u2.element());
    }
    }
}

// ----------------------------------------------------------------------------
// Checked generic field tokens for `variable` and `constant` fields, in a
// machine without storage: `&mut` token updates, borrowed reads, constants
// read from the instance, a property, and an operation that consumes no
// token (its unit resource comes from the instance).
pub mod variable_constant {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::multiset::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        #[verified_generic_tokens]
        V {
            fields {
                #[sharding(constant)]
                pub limit: int,

                #[sharding(variable)]
                pub value: int,

                #[sharding(variable)]
                pub steps: nat,

                #[sharding(multiset)]
                pub marks: Multiset<int>,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& 0 <= self.value <= self.limit
                &&& forall|m: int| #[trigger] self.marks.count(m) > 0 ==> 0 <= m <= self.limit
            }

            init!{
                initialize(limit: int) {
                    require(limit >= 0);
                    init limit = limit;
                    init value = 0;
                    init steps = 0;
                    init marks = Multiset::empty();
                }
            }

            transition!{
                bump(by: int) {
                    require(by >= 0);
                    require(pre.value + by <= pre.limit);
                    update value = pre.value + by;
                    update steps = pre.steps + 1;
                }
            }

            transition!{
                mark() {
                    // Reads `value` without changing it.
                    require(!(pre.value == pre.limit + 1));
                    add marks += { pre.value };
                }
            }

            transition!{
                mark_zero() {
                    add marks += { 0 };
                }
            }

            property!{
                in_range() {
                    assert(0 <= pre.value <= pre.limit);
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, limit: int) { }

            #[inductive(bump)]
            fn bump_inductive(pre: Self, post: Self, by: int) { }

            #[inductive(mark)]
            fn mark_inductive(pre: Self, post: Self) {
                assert forall|m: int| #[trigger] post.marks.count(m) > 0 implies 0 <= m <= post.limit by {
                    if m != pre.value { assert(pre.marks.count(m) > 0); }
                }
            }

            #[inductive(mark_zero)]
            fn mark_zero_inductive(pre: Self, post: Self) {
                assert forall|m: int| #[trigger] post.marks.count(m) > 0 implies 0 <= m <= post.limit by {
                    if m != 0 { assert(pre.marks.count(m) > 0); }
                }
            }
        }
    }

    verus! {
    proof fn client() {
        let tracked (Tracked(inst), Tracked(value), Tracked(steps), Tracked(marks)) = V::Instance::initialize(10);
        assert(inst.limit() == 10);
        let tracked mut value = value;
        let tracked mut steps = steps;
        inst.bump(3, &mut value, &mut steps);
        assert(value.value() == 3 && steps.value() == 1);
        inst.in_range(&value);
        assert(value.value() <= inst.limit());
        let tracked m = inst.mark(&value);
        assert(m.element() == 3);
        let tracked z = inst.mark_zero();
        assert(z.element() == 0 && z.instance_id() == inst.id());
        let tracked mut all = marks;
        all.insert(m);
        all.insert(z);
        assert(all.multiset().count(3) == 1);
        let tracked mut v2 = value;
        v2.unique(&steps_as_value_impossible());
    }

    // Two `value` tokens of one instance cannot coexist; a placeholder can.
    proof fn steps_as_value_impossible() -> (tracked t: V::value) {
        V::value::arbitrary()
    }
    }
}

// ----------------------------------------------------------------------------
// Checked generic field tokens for `option` fields and the optional and
// infinite-map storage strategies: a `storage_option` cell guarded by an
// `option` token, two `storage_option` fields of one machine (indexed
// storage keys), and a `storage_imap` field with general deposits.
pub mod option_storage {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        #[verified_generic_tokens]
        Cell {
            fields {
                #[sharding(option)]
                pub owner: Option<int>,

                #[sharding(storage_option)]
                pub slot: Option<int>,

                #[sharding(storage_option)]
                pub spare: Option<int>,

                #[sharding(bool)]
                pub empty: bool,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& self.owner is Some <==> self.slot is Some
                &&& self.owner is Some ==> self.slot == self.owner
                &&& self.spare is None
                &&& self.empty <==> self.owner is None
            }

            init!{
                initialize() {
                    init owner = Some(0);
                    init slot = Some(0);
                    init spare = None;
                    init empty = false;
                }
            }

            transition!{
                put(v: int) {
                    remove empty -= true;
                    add owner += Some(v);
                    deposit slot += Some(v);
                }
            }

            transition!{
                take() {
                    remove owner -= Some(let v);
                    withdraw slot -= Some(v);
                    add empty += true;
                }
            }

            property!{
                look(v: int) {
                    have owner >= Some(v);
                    guard slot >= Some(v);
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(put)]
            fn put_inductive(pre: Self, post: Self, v: int) { }

            #[inductive(take)]
            fn take_inductive(pre: Self, post: Self) { }
        }
    }

    verified_tokenized_state_machine! {
        #[verified_generic_tokens]
        Bank {
            fields {
                #[sharding(set)]
                pub free: Set<int>,

                #[sharding(map)]
                pub claims: Map<int, int>,

                #[sharding(storage_imap)]
                pub vault: IMap<int, int>,

                #[sharding(variable)]
                pub epoch: int,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& forall|k: int| #[trigger] self.claims.dom().contains(k) <==> self.vault.dom().contains(k)
                &&& forall|k: int| #[trigger] self.claims.dom().contains(k) ==> self.vault[k] == self.claims[k]
                &&& forall|k: int| #[trigger] self.free.contains(k) ==> !self.claims.dom().contains(k)
            }

            init!{
                initialize(free: Set<int>) {
                    init free = free;
                    init claims = Map::empty();
                    init vault = IMap::empty();
                    init epoch = 0;
                }
            }

            transition!{
                store(m: Map<int, int>) {
                    // A general deposit into a `storage_imap` field is tagged key
                    // by key: its domain is finite.
                    require(m.to_imap().dom().finite());
                    remove free -= (m.dom());
                    add claims += (m);
                    deposit vault += (m.to_imap());
                }
            }

            transition!{
                fetch(k: int) {
                    remove claims -= [k => let v];
                    withdraw vault -= [k => v];
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, free: Set<int>) { }

            #[inductive(store)]
            fn store_inductive(pre: Self, post: Self, m: Map<int, int>) {
                assert forall|k: int| #[trigger] post.claims.dom().contains(k) <==> post.vault.dom().contains(k) by {
                    assert(m.to_imap().dom().contains(k) == m.dom().contains(k));
                }
                assert forall|k: int| #[trigger] post.claims.dom().contains(k) implies post.vault[k] == post.claims[k] by {
                    assert(m.to_imap().dom().contains(k) == m.dom().contains(k));
                }
            }

            #[inductive(fetch)]
            fn fetch_inductive(pre: Self, post: Self, k: int) { }
        }
    }

    verus! {
    proof fn cell_client() {
        let tracked (Tracked(inst), Tracked(owner), Tracked(empty)) = Cell::Instance::initialize(Some(0), None);
        assert(empty is None);
        let tracked o = owner.tracked_unwrap();
        assert(o.value() == 0);
        let tracked (Tracked(v0), Tracked(e)) = inst.take(o);
        assert(v0 == 0);
        let tracked o = inst.put(5, 5, e);
        assert(o.value() == 5);
        let tracked g = inst.look(5, &o);
        assert(*g == 5);
        let tracked (Tracked(v), Tracked(e)) = inst.take(o);
        assert(v == 5);
    }

    proof fn bank_client() {
        let free = Set::<int>::empty().insert(1).insert(2).insert(3);
        let tracked (Tracked(inst), Tracked(free), Tracked(claims), Tracked(epoch)) = Bank::Instance::initialize(free, IMap::tracked_empty());
        let m = Map::<int, int>::empty().insert(1, 10).insert(2, 20);
        let tracked mut deposit = IMap::tracked_empty();
        deposit.tracked_insert(1int, 10int);
        deposit.tracked_insert(2int, 20int);
        assert(deposit == m.to_imap());
        assert(m.dom() <= free.set());
        assert(m.to_imap().dom() =~= m.dom().to_iset());
        vstd::set::lemma_to_iset_finite(m.dom());
        // The operation consumes only a token collection, so it takes a unit.
        let tracked mut epoch = epoch;
        let tracked u = inst.unit_from_epoch(&mut epoch);
        let tracked c = inst.store(m, free, deposit, u);
        assert(c.map() == m);
        let tracked mut c = c;
        let tracked c1 = c.remove(1);
        let tracked v = inst.fetch(1, c1);
        assert(v == 10);
    }
    }
}

// ----------------------------------------------------------------------------
// Checked generic field tokens for persistent strategies (`persistent_map`,
// `persistent_set`, `persistent_option`): tokens are `Copy` knowledge, created
// by `(union)=` and read by `have`, including bulk outputs (`MapToken`,
// `SetToken`) and initial collections.
pub mod persistent {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        #[verified_generic_tokens]
        P {
            fields {
                #[sharding(persistent_map)]
                pub names: Map<int, int>,

                #[sharding(persistent_set)]
                pub seen: Set<int>,

                #[sharding(persistent_option)]
                pub leader: Option<int>,

                #[sharding(variable)]
                pub next: int,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& forall|k: int| #[trigger] self.names.dom().contains(k) ==> k < self.next
                &&& forall|k: int| #[trigger] self.seen.contains(k) ==> k < self.next
                &&& self.leader is Some ==> self.leader == Some(0int) && 0 < self.next
            }

            init!{
                initialize() {
                    init names = Map::empty().insert(-1, 7);
                    init seen = Set::empty().insert(-1);
                    init leader = None;
                    init next = 0;
                }
            }

            transition!{
                register(v: int) {
                    add names (union)= [pre.next => v];
                    add seen (union)= set { pre.next };
                    update next = pre.next + 1;
                }
            }

            transition!{
                register_many(m: Map<int, int>) {
                    require(forall|k: int| #[trigger] m.dom().contains(k) ==> pre.next <= k < pre.next + 10);
                    add names (union)= (m);
                    update next = pre.next + 10;
                }
            }

            transition!{
                elect(k: int) {
                    have seen >= set { k };
                    require(k == 0);
                    add leader (union)= Some(k);
                }
            }

            property!{
                known(k: int, v: int) {
                    have names >= [k => v];
                    have leader >= Some(k);
                    assert(k < pre.next);
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(register)]
            fn register_inductive(pre: Self, post: Self, v: int) { }

            #[inductive(register_many)]
            fn register_many_inductive(pre: Self, post: Self, m: Map<int, int>) { }

            #[inductive(elect)]
            fn elect_inductive(pre: Self, post: Self, k: int) { }
        }
    }

    verus! {
    proof fn client() {
        let tracked (Tracked(inst), Tracked(names), Tracked(seen), Tracked(leader), Tracked(next)) = P::Instance::initialize();
        assert(names.map() == Map::<int, int>::empty().insert(-1, 7));
        assert(seen.set().contains(-1));
        assert(leader is None);
        let tracked mut next = next;
        let tracked (Tracked(n0), Tracked(s0)) = inst.register(42, &mut next);
        assert(n0.key() == 0 && n0.value() == 42 && s0.element() == 0);
        // Persistent tokens are Copy.
        let tracked s0b = s0;
        let tracked l = inst.elect(0, &s0);
        let tracked l2 = l.clone();
        assert(l2.value() == 0 && s0b.element() == 0);
        inst.known(0, 42, &n0, &l, &next);
        let tracked many = inst.register_many(Map::empty().insert(1, 43).insert(2, 44), &mut next);
        assert(many.map().dom().contains(2) && next.value() == 11);
        let tracked n2 = many.into_map().tracked_remove(2);
        assert(n2.value() == 44);
        n0.agree(&n0b_copy(n0));
        let tracked mut names = names;
        let tracked m1 = names.remove(-1);
        assert(m1.value() == 7);
    }

    proof fn n0b_copy(tracked t: P::names) -> (tracked out: P::names) ensures out == t { t }
    }
}

// ----------------------------------------------------------------------------
// Checked generic field tokens for a machine with exactly one `storage_map`
// field: deposits, withdrawals and guards use the field's own key and value
// types (no tagged storage carrier).
pub mod storage_map {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        #[verified_generic_tokens]
        S {
            fields {
                #[sharding(set)]
                pub free: Set<int>,

                #[sharding(map)]
                pub owner: Map<int, int>,

                #[sharding(storage_map)]
                pub store: Map<int, int>,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.store.dom().contains(k)
                &&& forall|k: int| #[trigger] self.owner.dom().contains(k) ==> self.store[k] == self.owner[k]
                &&& forall|k: int| #[trigger] self.free.contains(k) ==> !self.owner.dom().contains(k)
            }

            init!{
                initialize(free: Set<int>) {
                    init free = free;
                    init owner = Map::empty();
                    init store = Map::empty();
                }
            }

            transition!{
                put(k: int, v: int) {
                    remove free -= set { k };
                    add owner += [k => v];
                    deposit store += [k => v];
                }
            }

            transition!{
                take(k: int) {
                    remove owner -= [k => let v];
                    withdraw store -= [k => v];
                    add free += set { k };
                }
            }

            property!{
                peek(k: int) {
                    have owner >= [k => let v];
                    guard store >= [k => v];
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, free: Set<int>) { }

            #[inductive(put)]
            fn put_inductive(pre: Self, post: Self, k: int, v: int) { }

            #[inductive(take)]
            fn take_inductive(pre: Self, post: Self, k: int) { }
        }
    }

    verus! {
    proof fn client() {
        let tracked (Tracked(inst), Tracked(free), Tracked(owner)) =
            S::Instance::initialize(Set::<int>::empty().insert(1).insert(2), Map::tracked_empty());
        let tracked mut free = free;
        let tracked f1 = free.remove(1);
        let tracked o1 = inst.put(1, 10, f1, 10);
        assert(o1.key() == 1 && o1.value() == 10);
        let tracked g = inst.peek(1, &o1);
        assert(*g == 10);
        let tracked (Tracked(f1), Tracked(v)) = inst.take(1, o1);
        assert(v == 10 && f1.element() == 1);
        assert(owner.map() == Map::<int, int>::empty());
    }
    }
}

// ----------------------------------------------------------------------------
// Labeled machines on the generic interface. Init and transition labels are
// ordinary first parameters of the generated relations, so the generated
// operations take them as their first arguments, as in the raw interface
// (`raw_forms_statements.rs`, module `labels`). Labels may have the machine's type parameters.
pub mod labels {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        Labeled {
            fields {
                #[sharding(variable)] pub number: int,
                #[sharding(count)] pub ticks: nat,
            }
            pub struct InitLabel { pub start: int }
            pub enum Label { Add { n: int }, Tick }
            #[invariant] pub fn even(&self) -> bool { self.number % 2 == 0 }
            init! { initialize(label: InitLabel) {
                require(label.start % 2 == 0);
                init number = label.start;
                init ticks = 0;
            } }
            transition! { add(label: Label, n: int) {
                require(label == Label::Add { n } && n % 2 == 0);
                update number = pre.number + n;
            } }
            transition! { tick(label: Label) {
                require(label is Tick);
                add ticks += (1);
            } }
            property! { even_now(label: Label) {
                assert(pre.number % 2 == 0);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self, label: InitLabel) {}
            #[inductive(add)] fn add_inductive(pre: Self, post: Self, label: Label, n: int) {}
            #[inductive(tick)] fn tick_inductive(pre: Self, post: Self, label: Label) {}
        }
    }

    verified_tokenized_state_machine! {
        Cell<T> {
            fields {
                #[sharding(option)] pub owner: Option<T>,
                #[sharding(storage_option)] pub cell: Option<T>,
            }
            pub struct InitLabel<T> { pub v: T }
            pub enum Label<T> { Take { v: T }, Peek }
            #[invariant] pub fn same(&self) -> bool { self.cell == self.owner }
            init! { initialize(label: InitLabel<T>) {
                init owner = Some(label.v);
                init cell = Some(label.v);
            } }
            transition! { take(label: Label<T>, v: T) {
                require(label == Label::Take { v });
                remove owner -= Some(v);
                withdraw cell -= Some(v);
            } }
            property! { peek(label: Label<T>, v: T) {
                require(label is Peek);
                have owner >= Some(v);
                guard cell >= Some(v);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self, label: InitLabel<T>) {}
            #[inductive(take)] fn take_inductive(pre: Self, post: Self, label: Label<T>, v: T) {}
        }
    }
    verus! {

    proof fn labeled_client() {
        let tracked (Tracked(inst), Tracked(number), Tracked(ticks)) = Labeled::Instance::initialize(Labeled::InitLabel { start: 4 });
        let tracked mut number = number;
        inst.add(Labeled::Label::Add { n: 2 }, 2, &mut number);
        assert(number.value() == 6);
        let tracked t = inst.tick(Labeled::Label::Tick);
        assert(t.count() == 1);
        inst.even_now(Labeled::Label::Tick, &number);
    }

    proof fn cell_client<T>(tracked x: T) {
        let ghost v = x;
        let tracked (Tracked(inst), Tracked(owner)) = Cell::Instance::<T>::initialize(Cell::InitLabel { v }, Some(x));
        let tracked o = owner.tracked_unwrap();
        let tracked g = inst.peek(Cell::Label::Peek, v, &o);
        assert(*g == v);
        let tracked y = inst.take(Cell::Label::Take { v }, v, o);
        assert(y == v);
    }
    }
}

fn main() {
}
