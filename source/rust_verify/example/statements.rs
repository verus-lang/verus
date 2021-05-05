extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

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

fn test_loop() {
    let mut i: u64 = 10;
    let mut b1: u8 = 20;
    let mut b2: u8 = 200;
    let mut b3: u8 = 30;

    while i < 100 {
        invariant([
            10 <= i,
            i <= 100,
            b1 as u64 == i * 2,
        ]);

        assert(b2 as int <= 255);
        i = i + 1;
        b1 = b1 + 2;
        b2 = b2 + 1;
    }

    assert(b1 == 200);
    assert(b3 == 30);
}
