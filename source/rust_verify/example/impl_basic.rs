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
    fn get_passengers(&self) -> int { // UNSUPPORTED: we need references first
        self.passengers
    }
}

fn main() { }
