//! Names of generated binders in user code that the checked macro accepts (regressions of
//! e94a6a9ce): a `let` or pattern binding `owned`, `h`, `z`, `shared`, `outputs` or
//! `result` inside a transition (raw and generic interfaces), a generic transition parameter
//! `result`, and `init!` parameters `new`, `z` and `shared`.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Raw {
        fields {
            #[sharding(variable)] pub v: int,
            #[sharding(variable)] pub w: Option<int>,
            #[sharding(map)] pub m: Map<int, int>,
            #[sharding(map)] pub n: Map<int, int>,
            #[sharding(option)] pub o: Option<int>,
            #[sharding(multiset)] pub ms: Multiset<int>,
            #[sharding(count)] pub c: nat,
        }
        init! { initialize(new: int, z: int, shared: int) {
            init v = new + z + shared; init w = None; init m = Map::empty(); init n = Map::empty();
            init o = None; init ms = Multiset::empty(); init c = 0;
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, new: int, z: int, shared: int) {}
        transition! { names_let(k: int) { let owned = k; let outputs = 1int; remove ms -= {owned}; add ms += {outputs}; update v = owned; } }
        transition! { names_have(k: int) { have m >= [k => let owned]; have o >= Some(let shared); add c += (1); update v = owned + shared; } }
        transition! { names_match(k: int) {
            match pre.w {
                Some(z) => { remove m -= [z => let h]; add m += [z => h]; update v = z; }
                None => { let owned = k; remove n -= [owned => let x]; add n += [owned => x]; }
            }
        } }
        transition! { names_result(k: int) { let result = k; remove m -= [k => let out]; add m += [k => result + out]; update v = result; } }
        #[inductive(names_let)] fn names_let_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(names_have)] fn names_have_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(names_match)] fn names_match_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(names_result)] fn names_result_inductive(pre: Self, post: Self, k: int) {}
    }
}

verified_tokenized_state_machine! {
    Gen {
        fields {
            #[sharding(variable)] pub v: int,
            #[sharding(map)] pub m: Map<int, int>,
            #[sharding(multiset)] pub ms: Multiset<int>,
            #[sharding(count)] pub c: nat,
        }
        init! { initialize(new: int, z: int) { init v = new + z; init m = Map::empty(); init ms = Multiset::empty(); init c = 0; } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, new: int, z: int) {}
        transition! { param_result(result: int) { remove m -= [result => 0]; add m += [result => 1]; update v = result; } }
        transition! { names_let(k: int) { let owned = k; remove ms -= {owned}; add ms += {owned}; update v = owned; } }
        transition! { names_have(k: int) { have m >= [k => let owned]; add c += (1); update v = owned; } }
        #[inductive(param_result)] fn param_result_inductive(pre: Self, post: Self, result: int) {}
        #[inductive(names_let)] fn names_let_inductive(pre: Self, post: Self, k: int) {}
        #[inductive(names_have)] fn names_have_inductive(pre: Self, post: Self, k: int) {}
    }
}

fn main() {}

} // verus!
