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

test_verify_one_file! {
    #[test] test_spec_adt_ctor code! {
        #[spec]
        struct SpecStruct { a: nat }

        fn test() {
            let s = SpecStruct { a: 12 }; // FAILS
            assert(s.a == 12);
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_enum_adt_mod code! {
        mod A {
            use builtin::*;
            pub enum E {
                A { a: u64 },
                B(u64)
            }
        }

        mod B {
            use crate::pervasive::*;
            use crate::A::*;
            fn test() {
                let e = E::A { a: 12 };
                assert(match e { E::A { a } => a == 12, _ => false });
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_complex_arg code! {
        pub struct Value {
            pub v: u64,
        }

        pub fn add1(a: u64) -> u64 {
            requires(a < 10);
            ensures(|res: u64| res == a + 1);
            a + 1
        }

        fn test0() {
            let mut v = Value { v: 2 };
            v.v = add1(v.v);
            assert(v.v == 3);
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_no_empty_enums code! {
        enum Empty {
        }
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test_well_founded1 code! {
        enum List {
            Cons(int, Box<List>)
        }
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test_well_founded2 code! {
        enum List {
            Cons1(int, Box<List>),
            Cons2(int, Box<List>),
        }
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test_well_founded3 code! {
        enum List1 {
            Cons(int, Box<List2>)
        }
        enum List2 {
            Cons(int, Box<List1>)
        }
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test_well_founded4 code! {
        enum List {
            Cons(int, (Box<List>, bool))
        }
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test_well_field_unbox code! {
        struct B { b: bool }
        fn foo(s1: Box<B>, s2: &Box<B>, s3: Box<&B>, s4: Box<(bool, bool)>) {
            let z1 = s1.b;
            let z2 = s2.b;
            let z3 = s3.b;
            let z4 = s4.0;
        }
    } => Ok(())
}

const IS_VARIANT_MAYBE: &str = code_str! {
    #[is_variant]
    pub enum Maybe<T> {
        Some(T),
        None,
    }
};

test_verify_one_file! {
    #[test] test_is_variant_pass IS_VARIANT_MAYBE.to_string() + code_str! {
        pub fn test1(m: Maybe<u64>) {
            match m {
                Maybe::Some(_) => assert(m.is_Some()),
                Maybe::None => assert(m.is_None()),
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_is_variant_illegal code! {
        pub enum Maybe<T> {
            Some(T),
            None,
        }

        impl <T> Maybe<T> {
            #[doc(hidden)] #[spec] #[verifier(is_variant)] #[allow(non_snake_case)]
            fn is_Thing(&self) -> bool { ::core::panicking::panic("not implemented") }
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_is_variant_not_enum code! {
        #[is_variant]
        pub struct Maybe<T> {
            t: T,
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_is_variant_get_1 IS_VARIANT_MAYBE.to_string() + code_str! {
        pub fn test1(m: Maybe<u64>) {
            requires(m.is_Some() && m.get_Some_0() > 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_is_variant_get_2 IS_VARIANT_MAYBE.to_string() + code_str! {
        pub fn test1(m: Maybe<u64>) -> bool {
            ensures(|res: bool|
                (m.is_Some() >>= res == (m.get_Some_0() == 3)) &&
                (m.is_None() >>= !res)
            );
            match m {
                Maybe::Some(v) => v == 3,
                Maybe::None => false,
            }
        }

        pub fn test2() {
            let m = Maybe::Some(3);
            let res = test1(m);
            assert(res);
        }

        pub fn test3(v: Maybe<u64>) {
            requires(v.is_Some() && v.get_Some_0() == 5);
            if let Maybe::Some(a) = v {
                assert(a == 5);
            } else {
                unreached::<()>();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_is_variant_get_fail IS_VARIANT_MAYBE.to_string() + code_str! {
        pub fn test1(m: Maybe<u64>) -> u64 {
            requires(m.get_Some_0() == 4);
            if let Maybe::Some(v) = m {
                v
            } else {
                unreached() // FAILS
            }
        }

        pub fn test2() {
            let m = Maybe::None;
            assume(m.get_Some_0() == 4);
            test1(m);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_is_variant_get_named_field code! {
        #[is_variant]
        pub enum Res<T> {
            Ok { t: T },
            Err { v: u64 },
        }

        fn test1(m: Res<bool>) {
            requires(m.is_Err() && m.get_Err_v() == 42);
            match m {
                Res::Ok { .. } => assert(false),
                Res::Err { v } => assert(v == 42),
            };
        }

        fn test2(m: &Res<bool>) -> bool {
            ensures(|res: bool| equal(res, m.is_Ok() && m.get_Ok_t()));
            match m {
                Res::Ok { t } if *t => true,
                _ => false,
            }
        }

        fn caller() {
            let r = test2(&Res::Ok { t: false });
            assert(!r);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_is_variant_no_field IS_VARIANT_MAYBE.to_string() + code_str! {
        fn test1(v: Maybe<u64>) {
            assert(v.get_Some_1() == 3);
        }
    } => Err(_) // type-checking error
}
