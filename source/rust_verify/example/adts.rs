extern crate builtin;
use builtin::{assert, assume, imply, int};

struct Car {
    four_doors: bool,
    passengers: int,

}

enum Vehicle {
    Car(Car),
}

fn main() {}

// fn test1(p: int) {
//     assert((Car { passengers: p }).passengers == p);
// }
