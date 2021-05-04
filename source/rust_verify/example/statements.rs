extern crate builtin;
use builtin::*;

fn main() {}

fn test_if(b: bool) {
    let mut x: u32 = 0;
    if b {
        x = 10;
    }
    assert(imply(b, x == 10));
    if b {
        x = x + 3;
        x = x + 4;
    } else {
        x = x + 2;
    }
    assert(imply(b, x == 17));
    assert(imply(!b, x == 2));
    assert(x == if b { 17 } else { 2 });
    if x == 0 {
        assert(false);
    } else if x == 1 {
        assert(false);
    } else if x == 2 {
        assert(!b);
    } else {
        assert(x == 17);
    }
}
