use builtin::*;
use builtin_macros::*;

verus! {

#[derive(PartialEq, Eq)]
struct Car {
    four_doors: bool,
    passengers: u64,
}

impl Car {
    fn new() -> Car {
        ensures(|result: Car| equal(result.passengers, 201));
        Car { four_doors: false, passengers: 201 }
    }

    fn get_passengers(&self) -> u64 {
        ensures(|result: u64| result == self.passengers);
        self.passengers
    }
}

#[derive(PartialEq, Eq)]
struct TemplateCar<V> {
    four_doors: bool,
    passengers: u64,
    the_v: V,
}

impl<V> TemplateCar<V> {
    fn template_new(v: V) -> (result: TemplateCar<V>)
        ensures
            result.passengers == 205 && result.the_v == v,
    {
        TemplateCar::<V> { four_doors: false, passengers: 205, the_v: v }
    }

    fn template_get_passengers(&self) -> (result: u64)
        ensures
            result == self.passengers,
    {
        self.passengers
    }

    fn template_get_v(self) -> (result: V)
        ensures
            result == self.the_v,
    {
        self.the_v
    }
}

fn main() {
    let c = Car { four_doors: true, passengers: 3 };
    let p = c.get_passengers();
    assert(p < 4);
    let c2 = Car::new();
    let p2 = c2.get_passengers();
    assert(p2 == 201);
    let c3 = TemplateCar::<u64>::template_new(5);
    let p3 = c3.template_get_passengers();
    assert(p3 == 205);
    let v = c3.template_get_v();
    assert(v == 5);
}

} // verus!
