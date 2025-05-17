use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use vstd::prelude::*;

#[verifier::verify]
pub enum ThreadState {
    Idle,
    SetFlag,
    Waiting,
    Critical,
}

tokenized_state_machine! { Petersons<T> {
    fields {
        #[sharding(variable)] pub flag_0: bool,
        #[sharding(variable)] pub flag_1: bool,
        #[sharding(variable)] pub turn: int,

        #[sharding(variable)] pub thread_0: ThreadState,
        #[sharding(variable)] pub thread_1: ThreadState,

        #[sharding(storage_option)] pub storage: Option<T>,
    }

    #[invariant]
    pub spec fn the_inv(&self) -> bool {
        &&& (self.thread_0 === ThreadState::Idle) <==> !self.flag_0
        &&& (self.thread_1 === ThreadState::Idle) <==> !self.flag_1
        &&& !(self.thread_0 === ThreadState::Critical && self.thread_1 === ThreadState::Critical)
        &&& self.storage.is_Some() <==>
            (self.thread_0 !== ThreadState::Critical && self.thread_1 !== ThreadState::Critical)
        &&& self.thread_0 === ThreadState::Critical && self.turn == 1 ==> self.thread_1 === ThreadState::Idle || self.thread_1 === ThreadState::SetFlag
        &&& self.thread_1 === ThreadState::Critical && self.turn == 0 ==> self.thread_0 === ThreadState::Idle || self.thread_0 === ThreadState::SetFlag
        &&& self.turn == 0 || self.turn == 1
    }

    init!{
        initialize(t: T) {
            init flag_0 = false;
            init flag_1 = false;
            init turn = 0;
            init thread_0 = ThreadState::Idle;
            init thread_1 = ThreadState::Idle;
            init storage = Option::Some(t);
        }
    }

    //// Thread 0 transitions

    transition!{
        t0_set_flag() {
            require pre.thread_0 === ThreadState::Idle;
            update thread_0 = ThreadState::SetFlag;

            update flag_0 = true;
        }
    }

    transition!{
        t0_set_turn() {
            require pre.thread_0 === ThreadState::SetFlag;
            update thread_0 = ThreadState::Waiting;
            update turn = 1;
        }
    }

    transition!{
        t0_enter_via_flag() {
            require pre.thread_0 === ThreadState::Waiting;
            require pre.flag_1 == false;
            update thread_0 = ThreadState::Critical;
            withdraw storage -= Some(let _);
        }
    }

    transition!{
        t0_enter_via_turn() {
            require pre.thread_0 === ThreadState::Waiting;
            require pre.turn != 1;
            update thread_0 = ThreadState::Critical;
            withdraw storage -= Some(let _);
        }
    }

    transition!{
        t0_done(t: T) {
            require pre.thread_0 === ThreadState::Critical;
            update thread_0 = ThreadState::Idle;
            update flag_0 = false;
            deposit storage += Some(t);
        }
    }

    //// Thread 1 transitions

    transition!{
        t1_set_flag() {
            require pre.thread_1 === ThreadState::Idle;
            update thread_1 = ThreadState::SetFlag;

            update flag_1 = true;
        }
    }

    transition!{
        t1_set_turn() {
            require pre.thread_1 === ThreadState::SetFlag;
            update thread_1 = ThreadState::Waiting;
            update turn = 0;
        }
    }

    transition!{
        t1_enter_via_flag() {
            require pre.thread_1 === ThreadState::Waiting;
            require pre.flag_0 == false;
            update thread_1 = ThreadState::Critical;
            withdraw storage -= Some(let _);
        }
    }

    transition!{
        t1_enter_via_turn() {
            require pre.thread_1 === ThreadState::Waiting;
            require pre.turn != 0;
            update thread_1 = ThreadState::Critical;
            withdraw storage -= Some(let _);
        }
    }

    transition!{
        t1_done(t: T) {
            require pre.thread_1 === ThreadState::Critical;
            update thread_1 = ThreadState::Idle;
            update flag_1 = false;
            deposit storage += Some(t);
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, t: T) { }

    #[inductive(t0_set_flag)]
    fn t0_set_flag_inductive(pre: Self, post: Self) { }

    #[inductive(t0_set_turn)]
    fn t0_set_turn_inductive(pre: Self, post: Self) { }

    #[inductive(t0_enter_via_flag)]
    fn t0_enter_via_flag_inductive(pre: Self, post: Self) { }

    #[inductive(t0_enter_via_turn)]
    fn t0_enter_via_turn_inductive(pre: Self, post: Self) { }

    #[inductive(t0_done)]
    fn t0_done_inductive(pre: Self, post: Self, t: T) { }

    #[inductive(t1_set_flag)]
    fn t1_set_flag_inductive(pre: Self, post: Self) { }

    #[inductive(t1_set_turn)]
    fn t1_set_turn_inductive(pre: Self, post: Self) { }

    #[inductive(t1_enter_via_flag)]
    fn t1_enter_via_flag_inductive(pre: Self, post: Self) { }

    #[inductive(t1_enter_via_turn)]
    fn t1_enter_via_turn_inductive(pre: Self, post: Self) { }

    #[inductive(t1_done)]
    fn t1_done_inductive(pre: Self, post: Self, t: T) { }
}}

fn main() {}
