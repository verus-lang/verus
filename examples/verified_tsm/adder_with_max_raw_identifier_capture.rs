use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {

 GenericHidden<r#__tsm_hidden_observation_minimum> {
 fields {
  #[sharding(variable)] pub number: r#__tsm_hidden_observation_minimum,
  #[sharding(not_tokenized)] pub minimum: r#__tsm_hidden_observation_minimum,
 }
 init! { initialize(value: r#__tsm_hidden_observation_minimum) {
   init number = value; init minimum = value;
 } }
 transition! { reset() {
   birds_eye let r#__tsm_hidden_observation_minimum = pre.minimum;
   update number = r#__tsm_hidden_observation_minimum;
 } }
 }
}
verus! {

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut number)) = GenericHidden::Instance::<
            int,
        >::initialize(7int);
        instance.reset(&mut number);
        assert(number.value() == 7int);
    }
}

} // verus!
