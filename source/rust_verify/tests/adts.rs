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
    enum Vehicle {
        Car(Car),
        Train(bool),
    }
};

test_verify_with_pervasive! {
    #[test] test_struct_1 STRUCTS.to_string() + code_str! {
        fn test_struct_1(p: int) {
            assert((Car { four_doors: true, passengers: p }).passengers == p);
            assert((Car { passengers: p, four_doors: true }).passengers == p); // fields intentionally out of order
            assert((Car { four_doors: true, passengers: p }).passengers != p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test_struct_2 STRUCTS.to_string() + code_str! {
        fn test_struct_2(c: Car, p: int) {
            assume(c.passengers == p);
            assert(c.passengers == p);
            assert(c.passengers != p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test_struct_3 STRUCTS.to_string() + code_str! {
        fn test_struct_3(p: int) {
            let c = Car { passengers: p, four_doors: true };
            assert(c.passengers == p);
            assert(!c.four_doors); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test_struct_4 STRUCTS.to_string() + code_str! {
        fn test_struct_4(passengers: int) {
            assert((Car { passengers, four_doors: true }).passengers == passengers);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test_enum_1 STRUCTS.to_string() + code_str! {
        fn test_enum_1(passengers: int) {
            let t = Vehicle::Train(true);
            let c1 = Vehicle::Car(Car { passengers, four_doors: true });
            let c2 = Vehicle::Car(Car { passengers, four_doors: false });
        }
    } => Ok(())
}

test_verify_with_pervasive! {
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

test_verify_with_pervasive! {
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
