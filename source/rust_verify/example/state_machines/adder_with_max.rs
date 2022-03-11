#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::concurrent_state_machine;

concurrent_state_machine!{
    AdderWithMax {
        fields {
            #[sharding(constant)]
            pub maximum: int,
            
            #[sharding(variable)]
            pub number: int,

            #[sharding(not_tokenized)]
            pub minimum: int,
        }

        #[init]
        fn initialize(m: int) {
            require(m >= 0);
            init(number, 0);
            init(minimum, 0);
            init(maximum, m);
        }

        #[transition]
        fn add(&self, n: int) {
            require(n >= 0);
            require(self.number + n <= self.maximum);
            update(number, self.number + n);
        }

        #[transition]
        fn change_to_minimum(&self) {
            #[birds_eye] let min = self.minimum;
            update(number, min);
        }

        #[invariant]
        pub fn is_bounded_below(&self) -> bool {
            self.number >= self.minimum
        }

        #[invariant]
        pub fn is_bounded_above(&self) -> bool {
            self.number <= self.maximum
        }

        #[inductive(initialize)]
        fn init_preserves(post: AdderWithMax, m: int) {
        }

        #[inductive(add)]
        fn add_preserves(self: AdderWithMax, post: AdderWithMax, n: int) {
        }

        #[inductive(change_to_minimum)]
        fn change_to_minimum_inductive(self: AdderWithMax, post: AdderWithMax) { }
    }
}

fn main() { }
