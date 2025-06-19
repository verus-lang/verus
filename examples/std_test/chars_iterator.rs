use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

verus! {
#[verifier::loop_isolation(false)]
fn test() {
    let s = "abca";
    proof {
        reveal_strlit("abca");
    }
    let mut chars_it = s.chars();
    for c in it: chars_it
    {
        let is_expected_char = c == 'a' || c == 'b' || c == 'c';
        runtime_assert(is_expected_char);
    }
    let mut it2 = s.chars();
    let mut x = it2.next();
    runtime_assert(x == Some('a'));
    x = it2.next();
    runtime_assert(x == Some('b'));
    x = it2.next();
    runtime_assert(x == Some('c'));
    x = it2.next();
    runtime_assert(x == Some('a'));
    x = it2.next();
    runtime_assert(x == None);
}
}