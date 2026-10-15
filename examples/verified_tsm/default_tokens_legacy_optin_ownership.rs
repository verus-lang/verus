use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub enum Choice {
    A(int),
    B,
}

verified_tokenized_state_machine! { #[verified_field_tokens]
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
   Choice::A(value) => { update choice=Choice::A(value+1); update score=value+1; },
   Choice::B => { update choice=Choice::B; update score=0; },
  }
 } }
 #[inductive(initialize)] fn initialize_inductive(post: Self,value:int){}
 #[inductive(next)] fn next_inductive(pre:Self,post:Self){}
}}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut choice), Tracked(mut score)) =
            Matching::Instance::initialize(7);
        inst.next(&mut choice, &mut score);
        assert(score.value() == 8 && choice.value() == Choice::A(8));
        inst.next(&mut choice, &mut score);
        assert(score.value() == 9 && choice.value() == Choice::A(9));
    }
}

} // verus!
