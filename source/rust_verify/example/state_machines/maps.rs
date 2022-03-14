#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::map::*;

use state_machines_macros::concurrent_state_machine;

concurrent_state_machine!(
    X {
        fields {
            #[sharding(map)]
            pub bool_map: Map<int, bool>,

        }

        #[init]
        fn initialize(cond: bool) {
            init(bool_map, Map::empty().insert(5, true));
        }

        #[transition]
        fn add(&self, n: int) {
            remove_kv(bool_map, n, true);
            add_kv(bool_map, n, false);
        }

        #[transition]
        fn add_have(&self, n: int) {
            remove_kv(bool_map, n, false);
            have_kv(bool_map, 19, false);
            add_kv(bool_map, n, true);
        }

   
        #[inductive(initialize)]
        fn initialize_inductive(post: X, cond: bool) { }
   
        #[inductive(add)]
        fn add_inductive(self: X, post: X, n: int) { }
   
        #[inductive(add_have)]
        fn add_have_inductive(self: X, post: X, n: int) { }
    }
);

fn main() { }
