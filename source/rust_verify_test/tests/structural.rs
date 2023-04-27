#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const STRUCTS: &str = verus_code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct Car {
        four_doors: bool,
        passengers: u64,
    }

    #[derive(PartialEq, Eq, Structural)]
    enum Vehicle {
        Car(Car),
        Train(bool),
    }
};

test_verify_one_file! {
    #[test] test_structural_eq STRUCTS.to_string() + verus_code_str! {
        fn test_structural_eq(passengers: u64) {
            let c1 = Car { passengers, four_doors: true };
            let c2 = Car { passengers, four_doors: false };
            let c3 = Car { passengers, four_doors: true };

            assert(c1 == c3);
            assert(c1 != c2);

            let t = Vehicle::Train(true);
            let ca = Vehicle::Car(c1);

            assert(t != ca);
            assert(t == ca); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_not_structural_eq code! {
        #[derive(PartialEq, Eq)]
        struct Thing {
            v: bool,
        }

        fn test_not_structural(passengers: u64) {
            let v1 = Thing { v: true };
            let v2 = Thing { v: true };
            assert_(v1 == v2);
        }
    } => Err(err) => assert_vir_error_msg(err, "==/!= for non smt equality types")
}

test_verify_one_file! {
    #[test] test_not_structural_generic verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        struct Thing<V> {
            v: V,
        }

        #[derive(Eq, Structural)]
        struct Other { }

        impl std::cmp::PartialEq for Other {
            fn eq(&self, _: &Self) -> bool { todo!() }
        }

        fn test_not_structural(passengers: u64) {
            let v1 = Thing { v: true };
            let v2 = Thing { v: true };
            assert(v1 == v2);
        }
    } => Err(err) => assert_vir_error_msg(err, "structural impl for non-structural type Other")
}

test_verify_one_file! {
    #[test] test_not_structural_fields verus_code! {
        #[derive(PartialEq, Eq)]
        struct Other { }

        #[derive(PartialEq, Eq, Structural)]
        struct Thing {
            o: Other,
        }
    } => Err(err) => assert_rust_error_msg(err, "the trait bound `Other: builtin::Structural` is not satisfied")
}
