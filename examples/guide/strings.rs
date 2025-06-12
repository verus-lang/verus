// rust_verify/tests/example.rs
use vstd::prelude::*;

verus! {

// ANCHOR: initial
fn get_char() {
    let x = "hello world";
    proof {
        reveal_strlit("hello world");
    }
    assert(x@.len() == 11);
    let val = x.get_char(0);
    assert('h' === val);
}
// ANCHOR_END: initial

// ANCHOR: literal_eq
fn literal_eq() {
    let x = "hello world";
    let y = "hello world";
    assert(x@ == y@);
}
// ANCHOR_END: literal_eq
//
// ANCHOR: literal_view
fn str_view() {
    let x = "hello world";
    let ghost y: Seq<char> = x@;
}
// ANCHOR_END: literal_view

// ANCHOR: pre_substring
fn subrange<'a>(s: &str)
    requires s@ =~= "Hello"@,
{
    proof {
        reveal_strlit("Hello");
        reveal_strlit("H");
    }
    assert(s@.subrange(0, 1) =~= "H"@);
}
// ANCHOR_END: pre_substring

// ANCHOR: substring_ascii
fn test() {
    let a = String::from_str(("ABC"));
    proof {
        reveal_strlit("ABC");
    }
    assert(a.is_ascii());
    let b = a.as_str().substring_ascii(2, 3);
    proof {
        reveal_strlit("C");
    }
    assert(b@ =~= ("C")@);
}
// ANCHOR_END: substring_ascii

} // verus!