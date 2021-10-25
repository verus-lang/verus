extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

#[derive(PartialEq, Eq)]
struct Car {
    four_doors: bool,
    passengers: int,
}

impl Car {
    fn get_passengers(&self) -> int {
        ensures(|result: int| result == self.passengers);
        self.passengers
    }
}

fn main() {
    let c = Car { four_doors: true, passengers: 3 };
    let p = c.get_passengers();
    assert(p < 4);
}
