//! Pure models preserve unsafe weak relations without claiming safety.
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model! {
    Diagnostic {
        fields { pub value:int }
        init! { initialize(value:int) {init value=value;} }
        transition! { ordered(enabled:bool,safe:bool) {
            require enabled;
            assert safe;
            update value=pre.value+1;
        } }
        transition! { impossible() {assert false; update value=pre.value+1;} }
    }
}

pub proof fn exact_relations(
    pre: Diagnostic::State,
    post: Diagnostic::State,
    enabled: bool,
    safe: bool,
)
    ensures
        Diagnostic::State::ordered(pre, post, enabled, safe) == (enabled && (safe ==> post.value
            == pre.value + 1)),
        Diagnostic::State::ordered_strong(pre, post, enabled, safe) == (enabled && safe
            && post.value == pre.value + 1),
        Diagnostic::State::ordered_enabled(pre, enabled, safe) == enabled,
        Diagnostic::State::ordered_enabled_strong(pre, enabled, safe) == (enabled && safe),
        Diagnostic::State::impossible(pre, post),
        !Diagnostic::State::impossible_strong(pre, post),
        Diagnostic::State::impossible_enabled(pre),
        !Diagnostic::State::impossible_enabled_strong(pre),
{
}

pub fn demonstration() {
    proof {
        exact_relations(Diagnostic::State { value: 0 }, Diagnostic::State { value: 1 }, true, true);
        exact_relations(
            Diagnostic::State { value: 0 },
            Diagnostic::State { value: 999 },
            true,
            false,
        );
    }
}

} // verus!
fn main() {
    demonstration();
}
