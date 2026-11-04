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
    #[test] test_not_structural_generic verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        struct Thing<V> {
            v: V,
        }

        #[derive(Eq, Structural)]
        struct Other { }

        impl std::cmp::PartialEq for Other {
            fn eq(&self, other: &Self) -> bool { false }
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
    } => Err(err) => assert_rust_error_msg(err, "the trait bound `Other: verus_builtin::Structural` is not satisfied")
}

test_verify_one_file! {
    #[test] test_structural_ghost_field verus_code! {
        #[derive(PartialEq, Structural)]
        struct S { ghost g: bool }
    } => Err(err) => assert_vir_error_msg(err, "`Structural` types cannot have ghost or tracked fields")
}

test_verify_one_file_with_options! {
    #[test] test_structural_spoofed_derived_partial_eq ["no-auto-import-verus_builtin"] => code_str! {
        #![feature(structural_match)]
        use vstd::prelude::*;
    }.to_string() + verus_code_str! {
        #[derive(Structural)]
        struct T(u8);

        #[automatically_derived]
        impl core::marker::StructuralPartialEq for T {}

        impl vstd::std_specs::cmp::PartialEqSpecImpl for T {
            open spec fn obeys_eq_spec() -> bool { false }
            open spec fn eq_spec(&self, other: &T) -> bool { false }
        }

        #[automatically_derived]
        impl PartialEq for T {
            fn eq(&self, other: &T) -> bool { false }
        }
    } => Err(err) => assert_vir_error_msg(err, "`Structural` requires a built-in derived `PartialEq` implementation")
}

test_verify_one_file! {
    #[test] test_structural_enum_with_values verus_code! {
        #[derive(PartialEq, Structural)]
        pub enum ValueStatus {
          Valid = 0,
          Invalid = 1,
        }
    } => Ok(())
}

test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/178
    #[test] test_result_is_structural verus_code! {
        use vstd::prelude::*;

        fn eq_generic<T: PartialEq + Structural>(a: &T, b: &T) -> (r: bool)
            ensures r == (a == b),
        {
            a == b
        }

        fn test_result(a: Result<u32, u32>, b: Result<u32, u32>) {
            let r = eq_generic(&a, &b);
            assert(r == (a == b));
        }
    } => Ok(())
}

test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/178
    #[test] test_tuple_is_structural verus_code! {
        use vstd::prelude::*;

        fn eq_generic<T: PartialEq + Structural>(a: &T, b: &T) -> (r: bool)
            ensures r == (a == b),
        {
            a == b
        }

        fn test_tuple(a: (u32, bool), b: (u32, bool)) {
            let r = eq_generic(&a, &b);
            assert(r == (a == b));
        }
    } => Ok(())
}

test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/178
    #[test] test_array_is_structural verus_code! {
        use vstd::prelude::*;

        fn eq_generic<T: PartialEq + Structural>(a: &T, b: &T) -> (r: bool)
            ensures r == (a == b),
        {
            a == b
        }

        fn test_array(a: [u32; 3], b: [u32; 3]) {
            let r = eq_generic(&a, &b);
            assert(r == (a == b));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_structural_trait_bound ["exec_allows_no_decreases_clause"] => verus_code! {
        use vstd::prelude::*;

        // Structural required for Rust eq to connect to SMT ==
        pub struct VecMap<Key,Value>
        where Key: View + Eq + Structural
        {
            v: Vec<(Key,Value)>
        }

        impl<Key,Value> VecMap<Key,Value>
        where Key: View + Eq + Structural
        {
            pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
            {
                let mut i: usize = 0;
                while i < self.v.len()
                {
                    if &self.v[i].0 == k {
                        return Some(&self.v[i].1)
                    }
                }
                None
            }
        }

    } => Ok(())
}
