use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {

 GenericHidden<__tsm_hidden_observation_minimum> {
 fields {
  #[sharding(variable)] pub number: __tsm_hidden_observation_minimum,
  #[sharding(not_tokenized)] pub minimum: __tsm_hidden_observation_minimum,
 }
 init! { initialize(value: __tsm_hidden_observation_minimum) {
   init number = value; init minimum = value;
 } }
 transition! { reset() {
   birds_eye let __tsm_hidden_observation_minimum = pre.minimum;
   update number = __tsm_hidden_observation_minimum;
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
