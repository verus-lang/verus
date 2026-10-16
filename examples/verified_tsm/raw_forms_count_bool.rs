//! Raw backend statement forms: sequences of `remove`, `have` and `add` on one
//! `count` or `bool` field (in the trusted order remove, have, add), each
//! checked as one combined resource update.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Counts {
        fields {
            #[sharding(variable)] pub total: nat,
            #[sharding(count)] pub c: nat,
        }
        #[invariant] pub fn same(&self) -> bool { self.total == self.c }
        init! { initialize() { init total = 10; init c = 10; } }
        transition! { take_two_steps(a: nat, b: nat) {
            remove c -= (a);
            remove c -= (b);
            update total = (pre.total - a - b) as nat;
        } }
        transition! { give_two_steps(a: nat, b: nat) {
            add c += (a);
            add c += (b);
            update total = pre.total + a + b;
        } }
        transition! { exchange(a: nat, b: nat, k: nat) {
            remove c -= (a);
            have c >= (k);
            have c >= (k);
            add c += (b);
            update total = (pre.total - a + b) as nat;
        } }
        transition! { exchange_many(a: nat, a2: nat, b: nat, b2: nat) {
            remove c -= (a);
            remove c -= (a2);
            add c += (b);
            add c += (b2);
            update total = (pre.total - a - a2 + b + b2) as nat;
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(take_two_steps)] fn take_two_steps_inductive(pre: Self, post: Self, a: nat, b: nat) {}
        #[inductive(give_two_steps)] fn give_two_steps_inductive(pre: Self, post: Self, a: nat, b: nat) {}
        #[inductive(exchange)] fn exchange_inductive(pre: Self, post: Self, a: nat, b: nat, k: nat) {}
        #[inductive(exchange_many)] fn exchange_many_inductive(pre: Self, post: Self, a: nat, a2: nat, b: nat, b2: nat) {}
    }
}
proof fn count_history() {
    let tracked token = Counts::Protocol::initialize();
    let tracked token = Counts::Protocol::take_two_steps(token, 3, 4);
    let tracked token = Counts::Protocol::give_two_steps(token, 1, 2);
    let tracked token = Counts::Protocol::exchange_many(token, 1, 1, 5, 5);
    assert(token.fragment().total->Some_0->Exclusive_0 == 14);
}
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Flags {
        fields {
            #[sharding(variable)] pub on: bool,
            #[sharding(bool)] pub flag: bool,
            #[sharding(bool)] pub other: bool,
        }
        #[invariant] pub fn same(&self) -> bool { self.on == self.flag && self.other == !self.flag }
        init! { initialize() { init on = true; init flag = true; init other = false; } }
        transition! { toggle_off() {
            remove flag -= true;
            add other += true;
            update on = false;
        } }
        transition! { cycle() {
            remove flag -= true;
            add flag += true;
        } }
        transition! { cycle_general(x: bool) {
            require(x);
            remove flag -= (x);
            add flag += (x);
        } }
        transition! { general_twice(x: bool, y: bool) {
            require(x && !y);
            remove flag -= (x);
            remove flag -= (y);
            add flag += (y);
            add flag += (x);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(toggle_off)] fn toggle_off_inductive(pre: Self, post: Self) {}
        #[inductive(cycle)] fn cycle_inductive(pre: Self, post: Self) {}
        #[inductive(cycle_general)] fn cycle_general_inductive(pre: Self, post: Self, x: bool) {}
        #[inductive(general_twice)] fn general_twice_inductive(pre: Self, post: Self, x: bool, y: bool) {}
    }
}
proof fn flag_history() {
    let tracked token = Flags::Protocol::initialize();
    let tracked token = Flags::Protocol::cycle(token);
    let tracked token = Flags::Protocol::cycle_general(token, true);
    let tracked token = Flags::Protocol::general_twice(token, true, false);
    let tracked token = Flags::Protocol::toggle_off(token);
    assert(token.fragment().on->Some_0->Exclusive_0 == false);
}
fn main() {}

} // verus!
