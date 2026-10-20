//! Full property snippets from state_machines/src/properties.md.
//! The Count companion corrects the guide's variable/Have strategy mismatch.
//! Guard authority pins the requested permission: is_some alone cannot do that.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::{CountRA, Machine};
use vstd::resource::tsm_bool::*;
use vstd::resource::Loc;

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 Waiting {
    fields {
        #[sharding(bool)] pub waiting:bool,
        #[sharding(variable)] pub num_remaining:nat,
    }
    #[invariant] pub fn waiting_positive(self)->bool {
        self.waiting ==> self.num_remaining>0
    }
    #[invariant] pub fn remaining_bounded(self)->bool {self.num_remaining<10}
    init! {initialize(){init waiting=true;init num_remaining=2;}}
    property! {waiting_means_positive(){
        birds_eye let waiting=pre.waiting;
        assert waiting ==> pre.num_remaining>0;
    }}
    // With the declared variable strategy, an ordinary assertion expresses
    // the bound. The guide's Have operand is demonstrated by CountBounds below.
    property! {in_bounds(){assert pre.num_remaining<10;}}
    transition! {complete(){
        remove waiting -= true;
        update num_remaining=(pre.num_remaining-1) as nat;
    }}
    #[inductive(initialize)] fn initialize_inductive(post:Self){}
    #[inductive(complete)] fn complete_inductive(pre:Self,post:Self){}
} }

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 CountBounds {
    fields {#[sharding(count)] pub num_remaining:nat,}
    #[invariant] pub fn remaining_bounded(self)->bool {self.num_remaining<10}
    init! {initialize(){init num_remaining=9;}}
    property! {in_bounds(){have num_remaining >= (10);assert false;}}
    #[inductive(initialize)] fn initialize_inductive(post:Self){}
} }

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 #[verified_local_ready(deposit)] DepositedCell {
    fields {
        #[sharding(bool)] pub deposited:bool,
        #[sharding(variable)] pub deposited_authority:bool,
        #[sharding(constant)] pub authority:PointsTo<u64>,
        #[sharding(storage_option)] pub perm:Option<PointsTo<u64>>,
    }
    #[invariant] pub fn exact_permission(self)->bool {
        self.deposited==self.deposited_authority
        && self.perm == if self.deposited {Some(self.authority)} else {None}
    }
    init! {initialize(p:PointsTo<u64>){init deposited=false;init deposited_authority=false;init authority=p;init perm=None;}}
    transition! {deposit(p:PointsTo<u64>){
        require !pre.deposited_authority;
        require p==pre.authority;
        add deposited += true;
        deposit perm += Some(p);
        update deposited_authority=true;
    }}
    property! {get_perm_ref(x:PointsTo<u64>){
        require pre.authority==x;
        have deposited >= (true);
        guard perm >= Some(x);
    }}
    #[inductive(initialize)] fn initialize_inductive(post:Self,p:PointsTo<u64>){}
    #[inductive(deposit)] fn deposit_inductive(pre:Self,post:Self,p:PointsTo<u64>){}
} }

verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas};

pub struct CounterPredicate;

impl AtomicInvariantPredicate<Loc, u32, Waiting::Token> for CounterPredicate {
    open spec fn atomic_inv(id: Loc, value: u32, token: Waiting::Token) -> bool {
        token.loc() == id && token.fragment() == Waiting::Fragment::field_num_remaining(
            value as nat,
        )
    }
}

pub fn waiting_atomic_demo() -> (remaining: u32)
    ensures
        remaining < 10,
{
    let tracked token = Waiting::Protocol::initialize();
    let ghost id = token.loc();
    let tracked (counter_token, waiting_token) = Waiting::Protocol::take_num_remaining(token);
    let counter = AtomicU32::<Loc, Waiting::Token, CounterPredicate>::new(
        Ghost(id),
        2,
        Tracked(counter_token),
    );
    let tracked waiting_token = waiting_token;
    let previous =
        atomic_with_ghost!(&counter => fetch_sub(1);
        ghost counter_token => {
            let count=counter_token.fragment().num_remaining->Some_0->Exclusive_0;
            let tracked token=counter_token.join(waiting_token);
            let tracked token=Waiting::Protocol::waiting_means_positive(token);
            let tracked token=Waiting::Protocol::in_bounds(token);
            token.facts(count>0 && count<10);
            let tracked token=Waiting::Protocol::complete(token);
            counter_token=token;
        }
    );
    let remaining =
        atomic_with_ghost!(&counter => load();ghost token => {
        token.facts(token.fragment().num_remaining->Some_0->Exclusive_0<10);
    });
    remaining
}

/// The contradiction property is invoked with a shared Count token. Two
/// aliases denote the same count observation, not twice its resources.
pub proof fn establish_count_bound(tracked token: &CountBounds::Token)
    ensures
        token.fragment().num_remaining.count < 10,
{
    if token.fragment().num_remaining.count >= 10 {
        let tracked empty = token.empty();
        let old = empty.fragment();
        let shared = token.fragment();
        CountBounds::Fragment::op_unit(shared);
        CountBounds::Fragment::commutative(old, shared);
        assert(CountBounds::Protocol::in_bounds_shared_requires(old, shared));
        let tracked impossible = CountBounds::Protocol::in_bounds_with_shared(empty, token);
        assert(false);
    }
}

pub proof fn count_bound_demo() {
    let tracked token = CountBounds::Protocol::initialize();
    let tracked (a, b) = token.split(
        CountBounds::Fragment { num_remaining: CountRA { count: 2 } },
        CountBounds::Fragment { num_remaining: CountRA { count: 7 } },
    );
    establish_count_bound(&a);
    establish_count_bound(&b);
    assert(a.fragment().num_remaining.count == 2 && b.fragment().num_remaining.count == 7);
}

pub fn guarded_cell_demo() -> (value: u64)
    ensures
        value == 42,
{
    let (cell, Tracked(permission)) = PCell::new(42u64);
    let ghost p = permission;
    // The machine's storage is one `IMap<__StorageKey, __StorageValue>`;
    // `__pack_perm` tags the `Option` of the `storage_option` field and
    // `__borrow_perm` borrows its value.
    let tracked token = DepositedCell::Protocol::initialize(IMap::tracked_empty(), p);
    let tracked deposit = DepositedCell::__pack_perm(Some(permission));
    let tracked token = DepositedCell::Protocol::deposit_local(token, deposit, p);
    let tracked guard = DepositedCell::Protocol::get_perm_ref(&token, p);
    let value = *cell.borrow(Tracked(DepositedCell::__borrow_perm(guard).tracked_unwrap()));
    assert(value == 42);
    value
}

pub fn demonstration() {
    let remaining = waiting_atomic_demo();
    assert(remaining < 10);
    let value = guarded_cell_demo();
    assert(value == 42);
    proof {
        count_bound_demo();
    }
}

} // verus!
fn main() {
    let remaining = waiting_atomic_demo();
    assert_eq!(remaining, 1);
    let value = guarded_cell_demo();
    assert_eq!(value, 42);
    demonstration();
}
