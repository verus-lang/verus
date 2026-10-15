// EXPECTED-ERROR: postcondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub enum Choice {
    A(int),
    B,
}

verified_tokenized_state_machine! {
Matching {
 fields {
  #[sharding(variable)] pub choice: Choice,
  #[sharding(variable)] pub score: int,
 }
 #[invariant] pub fn related(&self)->bool {
  match self.choice { Choice::A(value)=>self.score==value, Choice::B=>self.score==0 }
 }
 init! { initialize(value:int) { init choice=Choice::A(value); init score=value; } }
 transition! { next() {
  match pre.choice {
   Choice::A(value) => { update choice=Choice::A(value+1); update score=value; },
   Choice::B => { update choice=Choice::B; update score=0; },
  }
 } }
 #[inductive(initialize)] fn initialize_inductive(post: Self,value:int){}
 #[inductive(next)] fn next_inductive(pre:Self,post:Self){}
}}

fn main() {
}

} // verus!
