use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, option::Option, result::Result};

#[derive(Structural, PartialEq, Eq)]
struct Car<P> {
    four_doors: bool,
    passengers: P,
}

#[derive(Structural, PartialEq, Eq)]
enum Vehicle {
    Car(Car<u64>),
    Train(bool),
}

fn test_struct_1(p: u64) {
    let c1 = Car { four_doors: true, passengers: p };
    assert(c1.passengers == p);
    assert((Car { passengers: p, four_doors: true }).passengers == p);
}

fn test_structural_eq(passengers: u64) {
    let c1 = Car { passengers, four_doors: true };
    let c2 = Car { passengers, four_doors: false };
    let c3 = Car { passengers, four_doors: true };

    assert(c1 == c3);
    assert(c1 != c2);

    let t = Vehicle::Train(true);
    let ca = Vehicle::Car(c1);

    assert(t != ca);
}

#[is_variant] #[derive(Structural, PartialEq, Eq)]
enum Vehicle2<T> {
    Car(Car<T>),
    Train(bool),
}

fn test_is_variant_1(v: Vehicle2<u64>) {
    match v {
        Vehicle2::Car(_) => assert(v.is_Car()),
        Vehicle2::Train(_) => assert(v.is_Train()),
    };
}

fn test_is_variant_2(v: Vehicle2<u64>) {
    requires(v.is_Train() && v.get_Train_0());
}

fn test_option(o: Option<u64>) -> u64 {
    ensures(|res: u64| res == if o.is_Some() { o.get_Some_0() } else { 0 });
    match o {
        Option::Some(v) => v,
        Option::None => 0,
    }
}

fn test_result<E>(r: Result<u64, E>) -> u64 {
    ensures(|res: u64| res == if r.is_Ok() { r.get_Ok_0() } else { 0 });
    match r {
        Result::Ok(v) => v,
        Result::Err(_) => 0,
    }
}

fn if_let_test(r: Result<u64, u64>) -> bool {
    requires(r.is_Ok());
    ensures(|b: bool| b == true);

    if let Result::Ok(r_inner) = r {
        return true;
    }

    false
}

fn main() {
}
