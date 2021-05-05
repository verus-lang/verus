extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

struct Car {
    four_doors: bool,
    passengers: int,
}

enum Vehicle {
    Car(Car),
}

fn main() {}

fn test1() {
    // assert((Car { passengers: p }).passengers == p);
}

fn test2(c: Car, p: int) {
    assume(c.passengers == p);
    assert(c.passengers == p);
    assert(c.passengers != p); // FAILS
}
