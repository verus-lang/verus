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

fn test1(p: int) {
    assert((Car { four_doors: true, passengers: p }).passengers == p);
    assert((Car { passengers: p, four_doors: true }).passengers == p); // fields intentionally out of order
    assert((Car { four_doors: true, passengers: p }).passengers != p); // FAILS
}

fn test2(c: Car, p: int) {
    assume(c.passengers == p);
    assert(c.passengers == p);
    assert(c.passengers != p); // FAILS
}

fn test3(p: int) {
    let c = Car { passengers: p, four_doors: true };
    assert(c.passengers == p);
    assert(!c.four_doors); // FAILS
}

fn test4(passengers: int) {
    assert((Car { passengers, four_doors: true }).passengers == passengers);
}
