#![verifier::loop_isolation(false)]
#![allow(non_snake_case)]

#[path = "rwlock.rs"]
pub mod rwlock;

use vstd::prelude::*;
use vstd::atomic::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::cell::CellId;
use vstd::cell::pcell as pc;
use vstd::invariant::*;
use vstd::tokens::*;
use rwlock::*;

verus!{

type Key = u64;
type Value = u64;

type Row = nat;
type Col = nat;

pub const HEIGHT: usize = 1048576;
pub const WIDTH: usize = 4;

pub closed spec fn hash1(key: Key) -> nat {
    (key as int % HEIGHT as int) as nat
}
pub closed spec fn hash2(key: Key) -> nat {
    let j = (key as int % 1048579) % (HEIGHT - 1);
    ((hash1(key) + j + 1) % HEIGHT as int) as nat
}

#[verifier::external_body]
pub fn rand_u8() -> u8 {
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    let s = std::collections::hash_map::RandomState::new();
    let hasher = s.build_hasher();
    (hasher.finish() & 0xFF) as u8
}


proof fn hash1_ne_hash2(key: Key)
    ensures hash1(key) != hash2(key)
{
}

fn compute_hash1(key: Key) -> (h: usize)
    ensures h == hash1(key) && h < HEIGHT
{
    (key % HEIGHT as u64) as usize
}

fn compute_hash2(key: Key) -> (h: usize)
    ensures h == hash2(key) && h < HEIGHT
{
    let j = (key % 1048579u64) % ((HEIGHT - 1) as u64);
    (compute_hash1(key) + j as usize + 1) % HEIGHT
}

    

tokenized_state_machine!{ Cuckoo {
    fields {
        #[sharding(map)]
        pub frag: Map<Key, Option<Value>>,

        #[sharding(map)]
        pub matrix: Map<Row, Seq<Option<(Key, Value)>>>,
    }

    init!{
        initialize() {
            init frag = Map::new(|key| true, |key| None);
            init matrix = Map::new(
                |p: Row| p < HEIGHT,
                |p: Row| Seq::new(WIDTH as nat, |col| None),
            );
        }
    }

    property!{
        query_none(key: Key) {
            have frag >= [key => let opt_val];
            have matrix >= [hash1(key) => let r1];
            have matrix >= [hash2(key) => let r2];
            require not_in_row(r1, key);
            require not_in_row(r2, key);
            assert opt_val === None;
        }
    }

    property!{
        query_some(key: Key, row: Row, col: Col) {
            have frag >= [key => let opt_val];
            require row < HEIGHT;
            require col < WIDTH;
            have matrix >= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            assert opt_val === Some(entry_value);
        }
    }

    property!{
        hash_is_right(key: Key, row: Row, col: Col) {
            require row < HEIGHT;
            require col < WIDTH;
            have matrix >= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            assert row == hash1(key) || row == hash2(key);
        }
    }

    transition!{
        delete_key_value(key: Key, row: Row, col: Col) {
            remove frag -= [key => let _];
            require row < HEIGHT;
            require col < WIDTH;
            remove matrix -= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            add matrix += [row => r.update(col as int, None)];
            add frag += [key => None];
        }
    }

    transition!{
        update_key_value(key: Key, new_val: Value, row: Row, col: Col) {
            remove frag -= [key => let _];
            require row < HEIGHT;
            require col < WIDTH;
            remove matrix -= [row => let r];
            require let Some((entry_key, entry_value)) = r[col as int];
            require entry_key == key;
            add matrix += [row => r.update(col as int, Some((key, new_val)))];
            add frag += [key => Some(new_val)];
        }
    }

    transition!{
        insert_key_value(key: Key, new_val: Value, row: Row, col: Col) {
            remove frag -= [key => let _];
            require row < HEIGHT;
            require col < WIDTH;
            require row == hash1(key) || row == hash2(key);
            let other_row = if row == hash1(key) { hash2(key) } else { hash1(key) };
            remove matrix -= [row => let r];
            have matrix >= [other_row => let other_r];
            require not_in_row(r, key);
            require not_in_row(other_r, key);
            require r[col as int] === None;
            add matrix += [row => r.update(col as int, Some((key, new_val)))];
            add frag += [key => Some(new_val)];
        }
    }

    transition!{
        swing(key: Key, row: Row, col: Col, row2: Row, col2: Col) {
            require row < HEIGHT;
            require col < WIDTH;
            require row2 < HEIGHT;
            require col2 < WIDTH;
            require row == hash1(key) || row == hash2(key);
            require row2 == hash1(key) || row2 == hash2(key);

            remove matrix -= [row => let r];
            remove matrix -= [row2 => let r2];

            require r[col as int].is_some() && r[col as int].unwrap().0 == key;
            require r2[col2 as int].is_none();

            add matrix += [row => r.update(col as int, None)];
            add matrix += [row2 => r2.update(col2 as int, r[col as int])];
        }
    }

    #[invariant]
    pub spec fn domain_full(&self) -> bool {
        forall |x| self.frag.dom().contains(x)
    }

    #[invariant]
    pub spec fn matrix_domain(&self) -> bool {
        forall |row1| 0 <= row1 < HEIGHT <==> #[trigger] self.matrix.dom().contains(row1)
    }

    #[invariant]
    pub spec fn matrix_col_len(&self) -> bool {
        forall |row1| 0 <= row1 < HEIGHT ==> self.matrix[row1].len() == WIDTH
    }

    #[invariant]
    pub spec fn all_distinct(&self) -> bool {
        forall |row1, col1, row2, col2|
            0 <= row1 < HEIGHT ==>
            0 <= col1 < WIDTH ==>
            0 <= row2 < HEIGHT ==>
            0 <= col2 < WIDTH ==>
            (#[trigger] self.matrix[row1][col1]).is_some() ==>
            (#[trigger] self.matrix[row2][col2]).is_some() ==>
            self.matrix[row1][col1].unwrap().0 == self.matrix[row2][col2].unwrap().0 ==>
            row1 == row2 && col1 == col2
    }

    #[invariant]
    pub spec fn key_in_map_implies_key_in_matrix(&self) -> bool {
        forall |key| (#[trigger] self.frag[key]).is_some() ==>
            exists |row, col|
                0 <= row < HEIGHT && 0 <= col < WIDTH
                    && (#[trigger] self.matrix[row][col]).is_some()
                    && self.matrix[row][col].unwrap().0 == key
    }

    #[invariant]
    pub spec fn pair_in_matrix_implies_pair_in_map(&self) -> bool {
        forall |row, col|
            0 <= row < HEIGHT ==>
            0 <= col < WIDTH ==>
            self.matrix[row][col].is_some() ==>
            self.frag[self.matrix[row][col].unwrap().0]
                == Some(self.matrix[row][col].unwrap().1)
    }

    #[invariant]
    pub spec fn pair_in_matrix_implies_hash_correct(&self) -> bool {
        forall |row, col|
            0 <= row < HEIGHT ==>
            0 <= col < WIDTH ==>
            self.matrix[row][col].is_some() ==>
            (row == hash1(self.matrix[row][col].unwrap().0)
              || row == hash2(self.matrix[row][col].unwrap().0))
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }
   
    #[inductive(delete_key_value)]
    fn delete_key_value_inductive(pre: Self, post: Self, key: Key, row: Row, col: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(false);
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }
   
    #[inductive(update_key_value)]
    fn update_key_value_inductive(pre: Self, post: Self, key: Key, new_val: Value, row: Row, col: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(post.matrix[row][col as int].is_some());
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }
   
    #[inductive(insert_key_value)]
    fn insert_key_value_inductive(pre: Self, post: Self, key: Key, new_val: Value, row: Row, col: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(post.matrix[row][col as int].is_some());
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }
   
    #[inductive(swing)]
    fn swing_inductive(pre: Self, post: Self, key: Key, row: Row, col: Col, row2: Row, col2: Col) {
        assert forall |key0| (#[trigger] post.frag[key0]).is_some() implies
            exists |row0, col0|
                0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                    && (#[trigger] post.matrix[row0][col0]).is_some()
                    && post.matrix[row0][col0].unwrap().0 == key0
        by {
            if key0 == key {
                assert(post.matrix[row2][col2 as int].is_some());
            } else {
                assert(pre.frag[key0].is_some());
                let (row0, col0) = choose |row0, col0|
                    0 <= row0 < HEIGHT && 0 <= col0 < WIDTH
                        && (pre.matrix[row0][col0]).is_some()
                        && pre.matrix[row0][col0].unwrap().0 == key0;
                assert(post.matrix[row0][col0].is_some());
            }
        }
    }
}}

pub open spec fn not_in_row(r: Seq<Option<(Key, Value)>>, key: Key) -> bool {
    forall |i| 0 <= i < r.len() ==> (#[trigger] r[i] matches Some((k, v)) ==> k != key)
}

closed spec fn places_ok(v: Seq<PlaceToFree>, i: int) -> bool {
    0 <= i && i+1 < v.len()
        && 0 <= v[i].row < HEIGHT
        && 0 <= v[i].col < WIDTH
        && v[i].row != v[i+1].row
        && (v[i].row == hash1(v[i].key) || v[i].row == hash2(v[i].key))
        && (v[i+1].row == hash1(v[i].key) || v[i+1].row == hash2(v[i].key))
}

///// Impl

pub const LOCKS_LEN: usize = 1048576;
type LockIdx = nat;

// Doing more than one row per lock would make deadlock more complicated.
// It's mildly annoying, not awful, you have to juggle around tracked handles a bit
// while casing on whether the two rows go to the same lock.
// I'm doing one-row-per-lock to avoid the trouble, I don't know what the optimal thing
// for performance is.
spec fn lock_for_row(row: Row) -> LockIdx {
    row
}

fn compute_lock_for_row(row: usize) -> (l: usize)
    ensures l == lock_for_row(row as nat)
{
    row
}

ghost struct Consts {
    pub ghost instance_id: InstanceId,
    pub ghost cell_ids: Seq<CellId>,
}

tracked struct RowStore {
    pub tracked pt: pc::PointsTo<[Option<(Key, Value)>; WIDTH]>,
    pub tracked token: Cuckoo::matrix,
}

tracked struct LockStore {
    pub tracked rows: Map<Row, RowStore>,
}

ghost struct LockPred {
    consts: Consts,
    lock: nat,
}

spec fn row_store_wf(consts: Consts, store: RowStore, row: Row) -> bool {
    consts.cell_ids.len() == HEIGHT
    && 0 <= row < HEIGHT
    && store.pt.id() == consts.cell_ids[row as int]
    && store.token.instance_id() == consts.instance_id
    && store.token.value() == store.pt.value()@
    && store.token.key() == row
}

impl RwLockPredicate<LockStore> for LockPred {
    closed spec fn inv(self, store: LockStore) -> bool {
        0 <= self.lock < LOCKS_LEN
        && forall |row| 0 <= row < HEIGHT ==>
            self.lock == #[trigger] lock_for_row(row) ==>
                store.rows.dom().contains(row) &&
                    row_store_wf(self.consts, store.rows[row], row)
    }
}

struct TruePred;
impl<A> RwLockPredicate<A> for TruePred {
    closed spec fn inv(self, a: A) -> bool {
        true
    }
}
pub struct MyHashMap {
    consts: Ghost<Consts>,
    instance: Tracked<Cuckoo::Instance>,
    locks: Vec<RwLock<LockStore, LockPred>>,
    matrix: Vec<pc::PCell<[Option<(Key, Value)>; WIDTH]>>,
    main_write_lock: RwLock<(), TruePred>, // doesn't need to be RwLock
}

impl MyHashMap {
    pub closed spec fn wf(&self) -> bool {
        self.instance.id() == self.consts.instance_id
            && self.locks.len() == LOCKS_LEN
            && self.matrix.len() == HEIGHT
            && (forall |i| 0 <= i < self.locks.len() ==> self.locks[i].pred() == LockPred { consts: *self.consts, lock: i as nat })
            && (forall |i| 0 <= i < HEIGHT ==> self.matrix[i].id() == self.consts.cell_ids[i])
    }

    pub closed spec fn id(&self) -> InstanceId {
        self.consts.instance_id
    }
}

pub type MPointsTo = Cuckoo::frag;

proof fn initialize_lock_store_map(j: nat) -> (tracked m: Map<LockIdx, LockStore>)
    ensures forall |i| 0 <= i < j ==> m.dom().contains(i)
        && m[i].rows =~= Map::empty()
    decreases j
{
    if j == 0 {
        Map::tracked_empty()
    } else {
        let tracked mut m = initialize_lock_store_map((j-1) as nat);
        m.tracked_insert((j-1) as nat, LockStore { rows: Map::tracked_empty() });
        m
    }
}

struct PlaceToFree {
    row: usize,
    col: usize,
    key: Key,
}

enum Attempt {
    Free(usize),
    Unfree(usize, Key),
}

impl MyHashMap {
    pub fn new() -> (ret: (Self, Tracked<MapToken<Key, Option<Value>, MPointsTo>>))
        ensures
            ret.0.wf(),
            ret.1.map() =~= Map::new(|key: Key| true, |key: Key| None),
            ret.1.instance_id() == ret.0.id(),
    {
        let mut locks: Vec<RwLock<LockStore, LockPred>> = vec![];
        let mut matrix: Vec<pc::PCell<[Option<(Key, Value)>; WIDTH]>> = vec![];

        let tracked mut lock_stores = initialize_lock_store_map(LOCKS_LEN as nat);
        let ghost mut cell_ids: Seq<CellId> = seq![];
        let tracked (Tracked(instance), Tracked(frag), Tracked(mut matrix_toks)) =
            Cuckoo::Instance::initialize();

        let mut i = 0;
        while i < HEIGHT
            invariant
                0 <= i <= HEIGHT,
                cell_ids.len() == i,
                matrix.len() == i,
                forall |j| i <= j < HEIGHT ==> matrix_toks.map().dom().contains(j),
                forall |j| i <= j < HEIGHT ==> 
                    matrix_toks.map()[j] === Seq::new(WIDTH as nat, |w| None),
                matrix_toks.instance_id() == instance.id(),
                forall |j| 0 <= j < LOCKS_LEN ==> lock_stores.dom().contains(j),
                forall |k: nat| 0 <= k < i ==>
                    lock_stores[#[trigger] lock_for_row(k)].rows.dom().contains(k)
                    && lock_stores[lock_for_row(k)].rows[k].pt.id() == cell_ids[k as int]
                    && lock_stores[lock_for_row(k)].rows[k].pt.value()@ === 
                       lock_stores[lock_for_row(k)].rows[k].token.value()
                    && lock_stores[lock_for_row(k)].rows[k].token.instance_id() == instance.id()
                    && lock_stores[lock_for_row(k)].rows[k].token.key() == k
                    && lock_stores[lock_for_row(k)].rows[k].token.value()
                        === Seq::new(WIDTH as nat, |w| None),
                forall |j| 0 <= j < i ==> cell_ids[j] == matrix[j].id(),
            decreases HEIGHT - i,
        {
            let (pcell, Tracked(pt)) = pc::PCell::new([None; WIDTH]);
            matrix.push(pcell);

            proof {
                let tracked token = matrix_toks.remove(i as nat);
                let tracked row_store = RowStore {
                    pt: pt,
                    token: token,
                };
                let ghost l = lock_for_row(i as nat);
                let tracked mut store = lock_stores.tracked_remove(l);
                store.rows.tracked_insert(i as nat, row_store);
                lock_stores.tracked_insert(l, store);
                cell_ids = cell_ids.push(pcell.id());

                assert(pt.value()@ =~= Seq::new(WIDTH as nat, |w| None));
            }

            i += 1;

            /*assert forall |k: nat| 0 <= k < i implies
                    lock_stores[#[trigger] lock_for_row(k)].rows.dom().contains(k)
                    && lock_stores[lock_for_row(k)].rows[k].pt.id() == cell_ids[k as int]
                    && lock_stores[lock_for_row(k)].rows[k].pt.value()@ === 
                       lock_stores[lock_for_row(k)].rows[k].token.value()
                    && lock_stores[lock_for_row(k)].rows[k].token.instance_id() == instance.id()
                    && lock_stores[lock_for_row(k)].rows[k].token.key() == k
                    && lock_stores[lock_for_row(k)].rows[k].token.value()
                        === Seq::new(WIDTH as nat, |w| None)
            by {
                if k + 1 == i {
                assert(lock_stores.dom().contains(lock_for_row(k)));
                assert(lock_stores[lock_for_row(k)].rows.dom().contains(k));
                assert(lock_stores[lock_for_row(k)].rows[k].pt.id() == cell_ids[k as int]);
                assert(lock_stores[lock_for_row(k)].rows[k].pt.value()@ === 
                       lock_stores[lock_for_row(k)].rows[k].token.value());
                assert(lock_stores[lock_for_row(k)].rows[k].token.instance_id() == instance.id());
                assert(lock_stores[lock_for_row(k)].rows[k].token.key() == k);
                assert(lock_stores[lock_for_row(k)].rows[k].token.value()
                        === Seq::new(WIDTH as nat, |w| None));
                } else {
                assert(lock_stores[lock_for_row(k)].rows.dom().contains(k));
                assert(lock_stores[lock_for_row(k)].rows[k].pt.id() == cell_ids[k as int]);
                assert(lock_stores[lock_for_row(k)].rows[k].pt.value()@ === 
                       lock_stores[lock_for_row(k)].rows[k].token.value());
                assert(lock_stores[lock_for_row(k)].rows[k].token.instance_id() == instance.id());
                assert(lock_stores[lock_for_row(k)].rows[k].token.key() == k);
                assert(lock_stores[lock_for_row(k)].rows[k].token.value()
                        === Seq::new(WIDTH as nat, |w| None));
                }
            }*/
        }

        let ghost consts = Consts {
            instance_id: instance.id(),
            cell_ids,
        };

        let mut i = 0;
        while i < LOCKS_LEN
            invariant
                0 <= i <= LOCKS_LEN,
                forall |j| i <= j < LOCKS_LEN ==> lock_stores.dom().contains(j),
                locks.len() == i,
                forall |j| 0 <= j < i ==> locks[j].pred() == (LockPred { consts, lock: j as nat }),
                forall |k: nat| 0 <= k < HEIGHT ==>
                    lock_stores.dom().contains(lock_for_row(k)) ==>
                    lock_stores[#[trigger] lock_for_row(k)].rows.dom().contains(k)
                    && lock_stores[lock_for_row(k)].rows[k].pt.id() == cell_ids[k as int]
                    && lock_stores[lock_for_row(k)].rows[k].pt.value()@ === 
                       lock_stores[lock_for_row(k)].rows[k].token.value()
                    && lock_stores[lock_for_row(k)].rows[k].token.instance_id() == instance.id()
                    && lock_stores[lock_for_row(k)].rows[k].token.key() == k
                    && lock_stores[lock_for_row(k)].rows[k].token.value()
                        === Seq::new(WIDTH as nat, |w| None)
            decreases LOCKS_LEN - i,
        {
            let tracked mut store = lock_stores.tracked_remove(i as nat);
            let ghost pred = LockPred { consts, lock: i as nat };
            /*proof {
                assert(0 <= pred.lock < LOCKS_LEN);
                assert forall |row| 0 <= row < HEIGHT &&
                    pred.lock == lock_for_row(row) &&
                        store.rows.dom().contains(row) implies
                            row_store_wf(pred.consts, store.rows[row], row)
                by {
                    assert(row_store_wf(pred.consts, store.rows[row], row));
                }
            }*/
            locks.push(RwLock::new(Tracked(store), Ghost(pred)));
            i = i + 1;
        }

        let map = MyHashMap {
            consts: Ghost(consts),
            instance: Tracked(instance),
            locks,
            matrix,
            main_write_lock: RwLock::new(Tracked(()), Ghost(TruePred)),
        };

        (map, Tracked(frag))
    }

    pub fn read(&self, key: Key) -> (value: Option<Value>)
        atomically (au) {
            type ReadPred,
            (mpt: MPointsTo) -> (new_mpt: I<MPointsTo>),
            requires
                key == mpt.key(),
                self.id() == mpt.instance_id(),
            ensures
                new_mpt@ == mpt,

            outer_mask any,
            inner_mask none,
        }
        requires self.wf(),
        ensures value == mpt.value(),
    {
        let mut h1 = compute_hash1(key);
        let mut h2 = compute_hash2(key);
        let l1 = compute_lock_for_row(h1);
        let l2 = compute_lock_for_row(h2);

        // Always take locks in order to avoid deadlock.
        // (Note that Verus doesn't prove deadlock-freedom.)
        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };
        let h1x = if l1 < l2 { h1 } else { h2 };
        let h2x = if l1 < l2 { h2 } else { h1 };

        let handle1x = self.locks[l1x].acquire_read();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                row_store_wf(self.consts@, handle1x@.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] handle1x@.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            //assert(row_store_wf(self.consts@, handle1x@.rows[h1x as nat], h1x as nat));

            let entry = self.matrix[h1x].borrow(
                Tracked(&handle1x.borrow().rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                try_open_atomic_update!(au, mpt => {
                    proof {
                        self.instance.query_some(key, h1x as nat, i as nat,
                            &mpt,
                            &handle1x.borrow().rows.tracked_borrow(h1x as nat).token);
                    }
                    Tracked(I(mpt))
                });

                let value = entry.unwrap().1;
                handle1x.release_read();
                return Some(value);
            }

            i += 1;
        }

        let handle2x = self.locks[l2x].acquire_read();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                row_store_wf(self.consts@, handle2x@.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] handle2x@.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&handle2x.borrow().rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                try_open_atomic_update!(au, mpt => {
                    proof {
                        self.instance.query_some(key, h2x as nat, i as nat,
                            &mpt,
                            &handle2x.borrow().rows.tracked_borrow(h2x as nat).token);
                    }
                    Tracked(I(mpt))
                });

                let value = entry.unwrap().1;
                handle1x.release_read();
                handle2x.release_read();
                return Some(value);
            }

            i += 1;
        }

        try_open_atomic_update!(au, mpt => {
            proof {
                if l1 < l2 {
                    self.instance.query_none(key, &mpt,
                        &handle1x.borrow().rows.tracked_borrow(h1x as nat).token,
                        &handle2x.borrow().rows.tracked_borrow(h2x as nat).token);
                 } else {
                    self.instance.query_none(key, &mpt,
                        &handle2x.borrow().rows.tracked_borrow(h2x as nat).token,
                        &handle1x.borrow().rows.tracked_borrow(h1x as nat).token);
                 }
            }
            Tracked(I(mpt))
        });

        handle1x.release_read();
        handle2x.release_read();
        None
    }

    pub fn delete(&self, key: Key)
        atomically (au) {
            type DeletePred,
            (mpt: MPointsTo) -> (new_mpt: I<MPointsTo>),
            requires
                key == mpt.key(),
                self.id() == mpt.instance_id(),
            ensures
                new_mpt@.instance_id() == mpt.instance_id(),
                new_mpt@.key() == mpt.key(),
                new_mpt@.value() === None,

            outer_mask any,
            inner_mask none,
        }
        requires self.wf(),
    {
        let mut h1 = compute_hash1(key);
        let mut h2 = compute_hash2(key);
        let l1 = compute_lock_for_row(h1);
        let l2 = compute_lock_for_row(h2);

        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };
        let h1x = if l1 < l2 { h1 } else { h2 };
        let h2x = if l1 < l2 { h2 } else { h1 };

        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock1x.rows.tracked_remove(h1x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.delete_key_value(key, h1x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = None;
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                return;
            }

            i += 1;
        }

        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock2x.rows.tracked_remove(h2x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.delete_key_value(key, h2x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = None;
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                return;
            }

            i += 1;
        }

        try_open_atomic_update!(au, mpt => {
            proof {
                if l1 < l2 {
                    self.instance.query_none(key, &mpt,
                        &lock1x.rows.tracked_borrow(h1x as nat).token,
                        &lock2x.rows.tracked_borrow(h2x as nat).token);
                 } else {
                    self.instance.query_none(key, &mpt,
                        &lock2x.rows.tracked_borrow(h2x as nat).token,
                        &lock1x.rows.tracked_borrow(h1x as nat).token);
                 }
            }
            Tracked(I(mpt))
        });

        handle1x.release_write(Tracked(lock1x));
        handle2x.release_write(Tracked(lock2x));
    }

    /// Insert (or update) the given key to the new value
    /// Bool return value indicates success
    pub fn insert(&self, key: Key, new_val: Value) -> (success: bool)
        atomically (au) {
            type InsertPred,
            (mpt: MPointsTo) -> (new_mpt: I<MPointsTo>),
            requires
                key == mpt.key(),
                self.id() == mpt.instance_id(),
            ensures
                new_mpt@.instance_id() == mpt.instance_id(),
                new_mpt@.key() == mpt.key(),
                new_mpt@.value() === Some(new_val) || new_mpt@.value() == mpt.value()

            outer_mask any,
            inner_mask none,
        }
        requires self.wf(),
        ensures success ==> new_mpt@.value() === Some(new_val)
    {
        let mut h1 = compute_hash1(key);
        let mut h2 = compute_hash2(key);
        let l1 = compute_lock_for_row(h1);
        let l2 = compute_lock_for_row(h2);

        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };
        let h1x = if l1 < l2 { h1 } else { h2 };
        let h2x = if l1 < l2 { h2 } else { h1 };

        let (Tracked(_unused), main_handle) = self.main_write_lock.acquire_write();
        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();

        // Update the key, value pair if it already exists

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock1x.rows.tracked_remove(h1x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }
                
                handle1x.release_write(Tracked(lock1x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock2x.rows.tracked_remove(h2x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        // If there's an available spot, insert

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < i ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j].is_some()),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock1x.rows.tracked_remove(h1x as nat);
                        let tracked other_r = lock2x.rows.tracked_borrow(h2x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token, &other_r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < i ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j].is_some()),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock2x.rows.tracked_remove(h2x as nat);
                        let tracked other_r = lock1x.rows.tracked_borrow(h1x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token, &other_r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        /////// Cuckoo procedure

        let r = rand_u8();
        let first_row = if r % 2 == 0 { h1 } else { h2 };
        let first_col = (r >> 1) as usize % WIDTH;
        let first_key = 
            self.matrix[first_row].borrow(
                Tracked(if first_row == h1x { &lock1x.rows.tracked_borrow(h1x as nat).pt } else { &lock2x.rows.tracked_borrow(h2x as nat).pt })
            )[first_col].unwrap().0;
        proof {
            self.instance.hash_is_right(first_key, first_row as nat, first_col as nat,
              if first_row == h1x { &lock1x.rows.tracked_borrow(h1x as nat).token } else { &lock2x.rows.tracked_borrow(h2x as nat).token });
        }

        // We have to release to avoid deadlock.
        // Hash table could be improved by using atomics
        // to avoid having to take so many locks.
        handle1x.release_write(Tracked(lock1x));
        handle2x.release_write(Tracked(lock2x));

        let mut first_place = PlaceToFree { row: first_row, col: first_col, key: first_key };
        let mut path = vec![first_place];

        let mut free_r;
        let mut free_c;

        let mut i = HEIGHT;

        // Find the cuckoo path
        #[verifier::allow_complex_invariants]
        loop
            invariant path.len() > 0,
                forall |i: int| 0 <= i && i+1 < path.len() ==> places_ok(path@, i),
                0 <= path[path.len() - 1].row < HEIGHT,
                0 <= path[path.len() - 1].col < WIDTH,
                path[path.len() - 1].row == hash1(path[path.len() - 1].key)
                  || path[path.len() - 1].row == hash2(path[path.len() - 1].key),
                
            decreases i
        {
            let ghost old_path = path;
            let cur_place = path.last().unwrap();
            proof { hash1_ne_hash2(cur_place.key); }
            let h1 = compute_hash1(cur_place.key);
            let h2 = compute_hash2(cur_place.key);
            let h_other = if h1 == cur_place.row { h2 } else { h1 };
            match self.find_free_space(h_other) {
                Attempt::Free(c) => {
                    free_r = h_other;
                    free_c = c;

                    /*
                    assert(path[path.len() - 1].row != free_r);
                    assert(0 <= path[path.len() - 1].row < HEIGHT);
                    assert(0 <= path[path.len() - 1].col < WIDTH);
                    assert(0 <= free_r < HEIGHT);
                    assert(0 <= free_c < WIDTH);
                    assert(path[path.len() - 1].row == hash1(path[path.len() - 1].key)
                      || path[path.len() - 1].row == hash2(path[path.len() - 1].key));
                    assert(free_r == hash1(path[path.len() - 1].key)
                      || free_r == hash2(path[path.len() - 1].key));
                    */
                    break;
                }
                Attempt::Unfree(c, next_key) => {
                    path.push(PlaceToFree { row: h_other, col: c, key: next_key });
                }
            }
            if i == 0 {
                main_handle.release_write(Tracked(()));
                try_open_atomic_update!(au, mpt => { Tracked(I(mpt)) });
                return false;
            }
            i -= 1;

            proof {
                assert(places_ok(path@, path.len() - 2));
                assert(forall |i: int| 0 <= i && i+1 < old_path.len() ==>
                    places_ok(old_path@, i) ==> places_ok(path@, i));
            }
        }

        // Execute the cuckoo path
        // Genuinely just the most abysmal locking strategy
        while path.len() > 0
            invariant
                forall |i: int| 0 <= i && i+1 < path.len() ==> places_ok(path@, i),
                  path.len() > 0 ==> path[path.len() - 1].row != free_r,
                  path.len() > 0 ==> 0 <= path[path.len() - 1].row < HEIGHT,
                  path.len() > 0 ==> 0 <= path[path.len() - 1].col < WIDTH,
                  path.len() > 0 ==> 0 <= free_r < HEIGHT,
                  path.len() > 0 ==> 0 <= free_c < WIDTH,
                  path.len() > 0 ==>
                       path[path.len() - 1].row == hash1(path[path.len() - 1].key)
                    || path[path.len() - 1].row == hash2(path[path.len() - 1].key),
                  path.len() > 0 ==>
                       free_r == hash1(path[path.len() - 1].key)
                    || free_r == hash2(path[path.len() - 1].key),
            decreases path.len()
        {
            let ghost old_path = path;
            proof {
                assert(path@.len() >= 2 ==> places_ok(path@, path@.len() - 2));
            }
            let place = path.pop().unwrap();
            self.do_swing(place.key, place.row, place.col, free_r, free_c);
            free_r = place.row;
            free_c = place.col;
            proof {
                assert(forall |i: int| 0 <= i && i+1 < path.len() ==>
                    places_ok(old_path@, i) ==> places_ok(path@, i));
            }
        }

        // Finally, add our new pair
        // Ideally we would just go ahead and insert in (free_r, free_c),
        // but it would take a bunch more work
        // to prove that correct, instead I'm just going to repeat the code from the beginning
        // of the function.

        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();

        // Update the key, value pair if it already exists

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock1x.rows.tracked_remove(h1x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }
                
                handle1x.release_write(Tracked(lock1x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_some() && entry.unwrap().0 == key {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock2x.rows.tracked_remove(h2x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.update_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        // If there's an available spot, insert

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l1x as int].inv(lock1x),
                row_store_wf(self.consts@, lock1x.rows[h1x as nat], h1x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h1x].borrow(
                Tracked(&lock1x.rows.tracked_borrow(h1x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock1x.rows.tracked_remove(h1x as nat);
                        let tracked other_r = lock2x.rows.tracked_borrow(h2x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h1x as nat, i as nat, mpt, r.token, &other_r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h1x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h1x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock1x.rows.tracked_insert(h1x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH, self.wf(),
                self.locks[l2x as int].inv(lock2x),
                row_store_wf(self.consts@, lock2x.rows[h2x as nat], h2x as nat),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock1x.rows[h1x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < WIDTH ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j] matches Some((k, _)) ==> k != key),
                forall |j| 0 <= j < i ==> (#[trigger] lock2x.rows[h2x as nat].token.value()[j].is_some()),
            decreases WIDTH - i,
        {
            let entry = self.matrix[h2x].borrow(
                Tracked(&lock2x.rows.tracked_borrow(h2x as nat).pt))[i];
            if entry.is_none() {
                let tracked mut r;
                try_open_atomic_update!(au, mut mpt => {
                    proof {
                        r = lock2x.rows.tracked_remove(h2x as nat);
                        let tracked other_r = lock1x.rows.tracked_borrow(h1x as nat);
                        let tracked (Tracked(mpt0), Tracked(tok0)) =
                            self.instance.insert_key_value(key, new_val, h2x as nat, i as nat, mpt, r.token, &other_r.token);
                        mpt = mpt0;
                        r.token = tok0;
                    }
                    Tracked(I(mpt))
                });

                let mut entry = *self.matrix[h2x].borrow(Tracked(&r.pt));
                entry[i] = Some((key, new_val));
                self.matrix[h2x].write(Tracked(&mut r.pt), entry);

                proof {
                    lock2x.rows.tracked_insert(h2x as nat, r);
                }

                handle1x.release_write(Tracked(lock1x));
                handle2x.release_write(Tracked(lock2x));
                main_handle.release_write(Tracked(()));
                return true;
            }

            i += 1;
        }

        // Again, this shouldn't happen
        try_open_atomic_update!(au, mpt => { Tracked(I(mpt)) });
        false
    }

    fn find_free_space(&self, row: usize) -> (a: Attempt)
        requires self.wf(), 0 <= row < HEIGHT,
        ensures (match a {
            Attempt::Free(c) => 0 <= c < WIDTH,
            Attempt::Unfree(c, key) => 0 <= c < WIDTH
                && (row == hash1(key) || row == hash2(key)),
        })
    {
        let l1x = compute_lock_for_row(row);
        let handle1x = self.locks[l1x].acquire_read();

        let mut i: usize = 0;
        while i < WIDTH
            invariant 0 <= i <= WIDTH,
                row_store_wf(self.consts@, handle1x@.rows[row as nat], row as nat),
                forall |j| 0 <= j < i ==>
                    (#[trigger] handle1x@.rows[row as nat].token.value()[j]).is_some(),
            decreases WIDTH - i,
        {
            let entry = self.matrix[row].borrow(
                Tracked(&handle1x.borrow().rows.tracked_borrow(row as nat).pt))[i];
            if entry.is_none() {
                handle1x.release_read();
                return Attempt::Free(i);
            }
            i += 1;
        }

        let c = rand_u8() as usize % WIDTH;
        let key = self.matrix[row].borrow(
             Tracked(&handle1x.borrow().rows.tracked_borrow(row as nat).pt))[c].unwrap().0;
        proof {
            self.instance.hash_is_right(key, row as nat, c as nat,
              &handle1x.borrow().rows.tracked_borrow(row as nat).token);
        }

        handle1x.release_read();
        Attempt::Unfree(c, key)
    }

    fn do_swing(&self, key: Key, old_row: usize, old_col: usize, new_row: usize, new_col: usize)
        requires self.wf(),
            0 <= old_row < HEIGHT,
            0 <= new_row < HEIGHT,
            0 <= old_col < WIDTH,
            0 <= new_col < WIDTH,
            old_row != new_row,
            old_row == hash1(key) || old_row == hash2(key),
            new_row == hash1(key) || new_row == hash2(key),
    {
        // Note: we should be able to prove this doesn't fail (using the write lock)

        let l1 = compute_lock_for_row(old_row);
        let l2 = compute_lock_for_row(new_row);

        let l1x = if l1 < l2 { l1 } else { l2 };
        let l2x = if l1 < l2 { l2 } else { l1 };

        let (Tracked(lock1x), handle1x) = self.locks[l1x].acquire_write();
        let (Tracked(lock2x), handle2x) = self.locks[l2x].acquire_write();

        let tracked mut lock1;
        let tracked mut lock2;
        let tracked mut r1;
        let tracked mut r2;
        proof {
            if l1 < l2 {
                lock1 = lock1x;
                lock2 = lock2x;
            } else {
                lock1 = lock2x;
                lock2 = lock1x;
            }
            r1 = lock1.rows.tracked_remove(old_row as nat);
            r2 = lock2.rows.tracked_remove(new_row as nat);
        }

        let mut entry1 = *self.matrix[old_row].borrow(Tracked(&r1.pt));
        let mut entry2 = *self.matrix[new_row].borrow(Tracked(&r2.pt));

        // The key might have been deleted since we last took the lock on this entry.
        if entry1[old_col].is_some() && entry1[old_col].unwrap().0 == key && entry2[new_col].is_none() {
            entry2[new_col] = entry1[old_col];
            entry1[old_col] = None;
            
            self.matrix[old_row].write(Tracked(&mut r1.pt), entry1);
            self.matrix[new_row].write(Tracked(&mut r2.pt), entry2);

            proof {
                let tracked (Tracked(tok1), Tracked(tok2)) =
                    self.instance.swing(key, old_row as nat, old_col as nat, new_row as nat, new_col as nat, r1.token, r2.token);
                r1.token = tok1;
                r2.token = tok2;
            }
        }

        proof {
            lock1.rows.tracked_insert(old_row as nat, r1);
            lock2.rows.tracked_insert(new_row as nat, r2);
            if l1 < l2 {
                lock1x = lock1;
                lock2x = lock2;
            } else {
                lock1x = lock2;
                lock2x = lock1;
            }
        }

        handle1x.release_write(Tracked(lock1x));
        handle2x.release_write(Tracked(lock2x));
    }
}

pub type ReadAU = AtomicUpdate<MPointsTo, I<MPointsTo>, ReadPred>;
pub type InsertAU = AtomicUpdate<MPointsTo, I<MPointsTo>, InsertPred>;
pub type DeleteAU = AtomicUpdate<MPointsTo, I<MPointsTo>, DeletePred>;

}

