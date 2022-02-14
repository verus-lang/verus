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
        }

        #[init]
        fn initialize(&self, m: int) {
            require(m >= 0);
            update(number, 0);
            update(maximum, m);
        }

        #[transition]
        fn add(&self, n: int) {
            require(self.number + n <= self.maximum);
            update(number, self.number + n);
        }

        #[invariant]
        pub fn is_bounded(&self) -> bool {
            self.number <= self.maximum
        }

        #[inductive(initialize)]
        fn init_preserves(post: AdderWithMax, m: int) {
        }

        #[inductive(add)]
        fn add_preserves(self: AdderWithMax, post: AdderWithMax, n: int) {
        }
    }
}

fn main() { }
