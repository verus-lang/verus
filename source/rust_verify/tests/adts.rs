#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const STRUCTS: &str = code_str! {
    #[derive(PartialEq, Eq)]
    struct Car {
        four_doors: bool,
        passengers: int,
    }

    #[derive(PartialEq, Eq)]
    struct CompactCar {
        four_doors: bool,
        passengers: u8,
    }

    #[derive(PartialEq, Eq)]
    enum Vehicle {
        Car(Car),
        Train(bool),
    }

    mod M {
        struct Car {
            four_doors: bool,
        }
    }
};

test_verify_one_file! {
    #[test] test_struct_1 STRUCTS.to_string() + code_str! {
        fn test_struct_1(p: int) {
            assert((Car { four_doors: true, passengers: p }).passengers == p);
            assert((Car { passengers: p, four_doors: true }).passengers == p); // fields intentionally out of order
            assert((Car { four_doors: true, passengers: p }).passengers != p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_2 STRUCTS.to_string() + code_str! {
        fn test_struct_2(c: Car, p: int) {
            assume(c.passengers == p);
            assert(c.passengers == p);
            assert(c.passengers != p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_3 STRUCTS.to_string() + code_str! {
        fn test_struct_3(p: int) {
            let c = Car { passengers: p, four_doors: true };
            assert(c.passengers == p);
            assert(!c.four_doors); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_4 STRUCTS.to_string() + code_str! {
        fn test_struct_4(passengers: int) {
            assert((Car { passengers, four_doors: true }).passengers == passengers);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_enum_1 STRUCTS.to_string() + code_str! {
        #[proof]
        fn test_enum_1(passengers: int) {
            let t = Vehicle::Train(true);
            let c1 = Vehicle::Car(Car { passengers, four_doors: true });
            let c2 = Vehicle::Car(Car { passengers, four_doors: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_enum_struct code! {
        #[derive(PartialEq, Eq)]
        enum Thing {
            One { a: int },
            Two(int),
        }

        fn test(v: int) {
            let t = Thing::One { a: v };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_enum_unit code! {
        #[derive(PartialEq, Eq, Structural)]
        enum AB {
            A,
            B(nat),
        }

        #[spec]
        fn is_a(l: AB) -> bool {
            l == AB::A
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_struct_u8 STRUCTS.to_string() + code_str! {
        fn test_struct_u8(car: CompactCar) {
            assert(car.passengers >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_struct_u8n STRUCTS.to_string() + code_str! {
        fn test_struct_u8(car: CompactCar) {
            assert(car.passengers >= 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_int STRUCTS.to_string() + code_str! {
        fn test_struct_u8(car: Car) {
            assert(car.passengers >= 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_update1 code! {
        struct S2 { u: u64, v: u64 }

        fn test_update() {
            let s2 = S2 { u: 10, v: 20 };
            let s3 = S2 { v: 23, .. s2 };
            assert(s3.u == 10);
            assert(s3.v == 23);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_update2 code! {
        struct S2 { u: u64, v: u64 }

        fn g() -> S2 {
            ensures(|s: S2| s.u == 100);
            S2 { u: 100, v: 200 }
        }

        fn test_update() {
            let s3 = S2 { v: 1 + 22, .. g() };
            assert(s3.u == 100);
            assert(s3.v == 23);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_update2_fails code! {
        struct S2 { u: u64, v: u64 }

        fn g() -> S2 {
            S2 { u: 100, v: 200 }
        }

        fn test_update() {
            let s3 = S2 { v: 1 + 22, .. g() };
            assert(s3.u == 100); // FAILS
            assert(s3.v == 23);
        }
    } => Err(err) => assert_one_fails(err)
}
