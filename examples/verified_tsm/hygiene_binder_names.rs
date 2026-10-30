//! Hygiene of the generated binders: transition parameters and user binders named like the
//! parameters, binders and return values of the generated operations (`owned`, `h`, `z`,
//! `out`, `new`, `shared`, `result`, `outputs`) neither collide with nor capture them, in the
//! raw and the generic interface and for every kind of transition: `init!`, `transition!`,
//! `readonly!`, `property!`, guards, deposits and withdrawals. (These names were reserved
//! until the generated binders became hygienic, see `state_machines_macros/src/hygiene.rs`;
//! the binder cases are regressions of e94a6a9ce.) The clients call every operation with
//! arguments of these names.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::pcm::PCM;

verus! {

pub struct Tok {
    pub v: int,
}

// ----------------------------------------------------------------------------
// Every name as a parameter of every kind of transition.
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    RawParams {
        fields {
            #[sharding(variable)] pub v: int,
            #[sharding(map)] pub m: Map<int, int>,
            #[sharding(variable)] pub val: Option<Tok>,
            #[sharding(storage_option)] pub s: Option<Tok>,
        }
        #[invariant] pub fn mirror(&self) -> bool { self.s == self.val }
        init! { initialize(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            init v = owned + h + z + out + new + shared + result + outputs;
            init m = Map::empty().insert(owned, h);
            init val = None;
            init s = None;
        } }
        transition! { t(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            remove m -= [owned => h];
            add m += [owned => h + z];
            update v = out + new + shared + result + outputs;
        } }
        readonly! { r(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            require(out + new == shared + result + outputs);
            have m >= [owned => h + z];
        } }
        property! { p(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            require(pre.v == out + new + shared + result + outputs);
            have m >= [owned => h + z];
        } }
        transition! { deposit(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {
            require(pre.val is None && t.v == owned + h + z);
            deposit s += Some(t);
            update val = Some(t);
            update v = out + new + shared + result + outputs;
        } }
        property! { guard(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {
            require(pre.val == Some(t) && t.v == owned + h + z && pre.v == out + new + shared + result + outputs);
            guard s >= Some(t);
        } }
        transition! { withdraw(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {
            require(pre.val == Some(t) && t.v == owned + h + z);
            withdraw s -= Some(t);
            update val = None;
            update v = out + new + shared + result + outputs;
        } }
        #[inductive(initialize)]
        fn initialize_inductive(post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {}
        #[inductive(t)]
        fn t_inductive(pre: Self, post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {}
        #[inductive(deposit)]
        fn deposit_inductive(pre: Self, post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {}
        #[inductive(withdraw)]
        fn withdraw_inductive(pre: Self, post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {}
    }
}

verified_tokenized_state_machine! {
    GenParams {
        fields {
            #[sharding(variable)] pub v: int,
            #[sharding(map)] pub m: Map<int, int>,
            #[sharding(variable)] pub val: Option<Tok>,
            #[sharding(storage_option)] pub s: Option<Tok>,
        }
        #[invariant] pub fn mirror(&self) -> bool { self.s == self.val }
        init! { initialize(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            init v = owned + h + z + out + new + shared + result + outputs;
            init m = Map::empty().insert(owned, h);
            init val = None;
            init s = None;
        } }
        transition! { t(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            remove m -= [owned => h];
            add m += [owned => h + z];
            update v = out + new + shared + result + outputs;
        } }
        readonly! { r(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            require(out + new == shared + result + outputs);
            have m >= [owned => h + z];
        } }
        property! { p(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {
            require(pre.v == out + new + shared + result + outputs);
            have m >= [owned => h + z];
        } }
        transition! { deposit(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {
            require(pre.val is None && t.v == owned + h + z);
            deposit s += Some(t);
            update val = Some(t);
            update v = out + new + shared + result + outputs;
        } }
        property! { guard(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {
            require(pre.val == Some(t) && t.v == owned + h + z && pre.v == out + new + shared + result + outputs);
            guard s >= Some(t);
        } }
        transition! { withdraw(owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {
            require(pre.val == Some(t) && t.v == owned + h + z);
            withdraw s -= Some(t);
            update val = None;
            update v = out + new + shared + result + outputs;
        } }
        #[inductive(initialize)]
        fn initialize_inductive(post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {}
        #[inductive(t)]
        fn t_inductive(pre: Self, post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int) {}
        #[inductive(deposit)]
        fn deposit_inductive(pre: Self, post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {}
        #[inductive(withdraw)]
        fn withdraw_inductive(pre: Self, post: Self, owned: int, h: int, z: int, out: int, new: int, shared: int, result: int, outputs: int, t: Tok) {}
    }
}

// ----------------------------------------------------------------------------
// Every name as a `let` or pattern binder: `let`, a `have`'s and a `remove`'s value
// pattern, a `match` arm, and a withdrawal's pattern, around token and storage operations
// (deposits and guards bind by `let`).
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    RawBinders {
        fields {
            #[sharding(variable)] pub v: int,
            #[sharding(map)] pub m: Map<int, int>,
            #[sharding(variable)] pub val: Option<Tok>,
            #[sharding(storage_option)] pub s: Option<Tok>,
        }
        #[invariant] pub fn mirror(&self) -> bool { self.s == self.val }
        init! { initialize() { init v = 0; init m = Map::empty().insert(1, 2).insert(2, 3); init val = None; init s = None; } }
        transition! { lets(k: int) {
            let owned = k; let h = owned; let z = h; let out = z;
            let new = out; let shared = new; let result = shared; let outputs = result;
            update v = outputs;
        } }
        transition! { patterns(k: int) {
            remove m -= [k => let h];
            have m >= [k + 1 => let owned];
            add m += [k => owned + h];
            match Some(k) {
                Some(z) => { update v = z; }
                None => {}
            }
        } }
        readonly! { observe(k: int) { have m >= [k => let out]; } }
        property! { check(k: int) { let new = k; require(pre.v == new); have m >= [new => let shared]; } }
        transition! { put(t: Tok) {
            let result = t;
            require(pre.val is None);
            deposit s += Some(result);
            update val = Some(result);
        } }
        property! { look(t: Tok) { let outputs = t; require(pre.val == Some(outputs)); guard s >= Some(outputs); } }
        transition! { take() {
            require(pre.val is Some);
            withdraw s -= Some(let owned);
            update val = None;
            update v = owned.v;
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(lets)] fn lets_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(patterns)] fn patterns_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(put)] fn put_inductive(pre: Self, post: Self, t: Tok) {}
        #[inductive(take)] fn take_inductive(pre: Self, post: Self) {}
    }
}

verified_tokenized_state_machine! {
    GenBinders {
        fields {
            #[sharding(variable)] pub v: int,
            #[sharding(map)] pub m: Map<int, int>,
            #[sharding(variable)] pub val: Option<Tok>,
            #[sharding(storage_option)] pub s: Option<Tok>,
        }
        #[invariant] pub fn mirror(&self) -> bool { self.s == self.val }
        init! { initialize() { init v = 0; init m = Map::empty().insert(1, 2).insert(2, 3); init val = None; init s = None; } }
        transition! { lets(k: int) {
            let owned = k; let h = owned; let z = h; let out = z;
            let new = out; let shared = new; let result = shared; let outputs = result;
            update v = outputs;
        } }
        transition! { patterns(k: int) {
            remove m -= [k => let h];
            have m >= [k + 1 => let owned];
            add m += [k => owned + h];
            match Some(k) {
                Some(z) => { update v = z; }
                None => {}
            }
        } }
        readonly! { observe(k: int) { have m >= [k => let out]; } }
        property! { check(k: int) { let new = k; require(pre.v == new); have m >= [new => let shared]; } }
        transition! { put(t: Tok) {
            let result = t;
            require(pre.val is None);
            deposit s += Some(result);
            update val = Some(result);
        } }
        property! { look(t: Tok) { let outputs = t; require(pre.val == Some(outputs)); guard s >= Some(outputs); } }
        transition! { take() {
            require(pre.val is Some);
            withdraw s -= Some(let owned);
            update val = None;
            update v = owned.v;
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(lets)] fn lets_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(patterns)] fn patterns_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(put)] fn put_inductive(pre: Self, post: Self, t: Tok) {}
        #[inductive(take)] fn take_inductive(pre: Self, post: Self) {}
    }
}

// ----------------------------------------------------------------------------
// Clients.
proof fn raw_params_client(tracked tok: Tok)
    requires
        tok.v == 6,
{
    let (owned, h, z, out, new, shared, result, outputs) =
        (1int, 2int, 3int, 10int, 11int, 5int, 7int, 9int);
    assert forall|s: RawParams::State|
        RawParams::State::initialize_strong(s, owned, h, z, out, new, shared, result, outputs)
        implies IMap::<RawParams::__StorageKey, RawParams::__StorageValue>::empty() == s.__storage() by {
        assert(IMap::<RawParams::__StorageKey, RawParams::__StorageValue>::empty() =~= s.__storage());
    }
    let tracked token = RawParams::Protocol::initialize(
        IMap::tracked_empty(), owned, h, z, out, new, shared, result, outputs);
    let tracked token = RawParams::local_ready::t::run(token, owned, h, z, out, new, shared, result, outputs);
    let tracked token = RawParams::local_ready::r::run(token, owned, h, z, out, new, shared, result, outputs);
    let tracked token = RawParams::local_ready::p::run(token, owned, h, z, out, new, shared, result, outputs);
    let ghost t = tok;
    let tracked mut deposit = IMap::tracked_empty();
    deposit.tracked_insert(RawParams::__StorageKey::s, RawParams::__StorageValue::s(tok));
    let tracked token = RawParams::local_ready::deposit::run(
        token, deposit, owned, h, z, out, new, shared, result, outputs, t);
    let tracked guarded = RawParams::local_ready::guard::run(
        &token, owned, h, z, out, new, shared, result, outputs, t);
    assert(guarded[RawParams::__StorageKey::s] == RawParams::__StorageValue::s(t));
    let tracked (token, mut withdrawn) = RawParams::local_ready::withdraw::run(
        token, owned, h, z, out, new, shared, result, outputs, t);
    let tracked back = RawParams::__unwrap_s(withdrawn.tracked_remove(RawParams::__StorageKey::s));
    assert(back == t);
    // A plain raw operation, whose precondition quantifies over completions.
    let tracked mut deposit = IMap::tracked_empty();
    deposit.tracked_insert(RawParams::__StorageKey::s, RawParams::__StorageValue::s(back));
    RawParams::local_ready::deposit::ready(
        token.fragment(), RawParams::Fragment::unit(), deposit, owned, h, z, out, new, shared, result, outputs, t);
    let tracked token = RawParams::Protocol::deposit(
        token, deposit, owned, h, z, out, new, shared, result, outputs, t);
}

proof fn gen_params_client(tracked tok: Tok)
    requires
        tok.v == 6,
{
    let (owned, h, z, out, new, shared, result, outputs) =
        (1int, 2int, 3int, 10int, 11int, 5int, 7int, 9int);
    let ghost t = tok;
    let tracked (Tracked(inst), Tracked(mut v), Tracked(mut m), Tracked(mut val)) =
        GenParams::Instance::initialize(owned, h, z, out, new, shared, result, outputs, None);
    let tracked entry = m.remove(owned);
    let tracked entry = inst.t(owned, h, z, out, new, shared, result, outputs, &mut v, entry);
    // (`readonly!` transitions have no `Instance` method, as in the trusted macro.)
    inst.p(owned, h, z, out, new, shared, result, outputs, &v, &entry);
    inst.deposit(owned, h, z, out, new, shared, result, outputs, t, &mut v, &mut val, tok);
    let tracked guarded = inst.guard(owned, h, z, out, new, shared, result, outputs, t, &v, &val);
    assert(*guarded == t);
    let tracked back = inst.withdraw(owned, h, z, out, new, shared, result, outputs, t, &mut v, &mut val);
    assert(back == t);
}

proof fn raw_binders_client(tracked tok: Tok) {
    assert forall|s: RawBinders::State| RawBinders::State::initialize_strong(s)
        implies IMap::<RawBinders::__StorageKey, RawBinders::__StorageValue>::empty() == s.__storage() by {
        assert(IMap::<RawBinders::__StorageKey, RawBinders::__StorageValue>::empty() =~= s.__storage());
    }
    let (owned, h) = (1int, 2int);
    let tracked token = RawBinders::Protocol::initialize(IMap::tracked_empty());
    let tracked token = RawBinders::local_ready::lets::run(token, owned);
    let tracked token = RawBinders::local_ready::patterns::run(token, owned);
    let tracked token = RawBinders::local_ready::observe::run(token, h);
    let tracked token = RawBinders::local_ready::check::run(token, owned);
    let ghost t = tok;
    let tracked mut deposit = IMap::tracked_empty();
    deposit.tracked_insert(RawBinders::__StorageKey::s, RawBinders::__StorageValue::s(tok));
    let tracked token = RawBinders::local_ready::put::run(token, deposit, t);
    let tracked shared = RawBinders::local_ready::look::run(&token, t);
    let tracked (token, mut withdrawn) = RawBinders::local_ready::take::run(token);
    let tracked result = RawBinders::__unwrap_s(withdrawn.tracked_remove(RawBinders::__StorageKey::s));
    assert(result == t);
}

proof fn gen_binders_client(tracked tok: Tok) {
    let (owned, h) = (1int, 2int);
    let ghost t = tok;
    let tracked (Tracked(inst), Tracked(mut v), Tracked(mut m), Tracked(mut val)) =
        GenBinders::Instance::initialize(None);
    inst.lets(owned, &mut v);
    let tracked one = m.remove(owned);
    let tracked two = m.remove(h);
    let tracked one = inst.patterns(owned, &mut v, one, &two);
    inst.check(owned, &v, &one);
    inst.put(t, &mut val, tok);
    let tracked shared = inst.look(t, &val);
    assert(*shared == t);
    let tracked out = inst.take(&mut v, &mut val);
    // `update v = owned.v` reads the user's binder `owned` (the withdrawn value).
    assert(v.value() == out.v);
}

fn main() {}

} // verus!
