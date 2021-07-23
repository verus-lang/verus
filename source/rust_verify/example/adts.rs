#[macro_use] extern crate builtin_macros;
extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

#[derive(Structural, PartialEq, Eq)]
struct Car<P> {
    four_doors: bool,
    passengers: P,
}

#[derive(Structural, PartialEq, Eq)]
enum Vehicle {
    Car(Car<int>),
    Train(bool),
}

fn test_struct_1(p: int) {
    let c1 = Car { four_doors: true, passengers: p };
    assert(c1.passengers == p);
    assert((Car { passengers: p, four_doors: true }).passengers == p);
}

// fn test_structural_eq(passengers: int) {
//     let c1 = Car { passengers, four_doors: true };
//     let c2 = Car { passengers, four_doors: false };
//     let c3 = Car { passengers, four_doors: true };
// 
//     assert(c1 == c3);
//     assert(c1 != c2);
// 
//     let t = Vehicle::Train(true);
//     let ca = Vehicle::Car(c1);
// 
//     assert(t != ca);
//     // assert(t == ca); // FAILS
// }

fn main() {
}
