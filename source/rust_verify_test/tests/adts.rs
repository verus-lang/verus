#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const STRUCTS: &str = verus_code_str! {
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
    #[test] test_struct_1 STRUCTS.to_string() + verus_code_str! {
        fn test_struct_1(p: int) {
            assert((Car { four_doors: true, passengers: p }).passengers == p);
            assert((Car { passengers: p, four_doors: true }).passengers == p); // fields intentionally out of order
            assert((Car { four_doors: true, passengers: p }).passengers != p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_2 STRUCTS.to_string() + verus_code_str! {
        fn test_struct_2(c: Car, p: int) {
            assume(c.passengers == p);
            assert(c.passengers == p);
            assert(c.passengers != p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_3 STRUCTS.to_string() + verus_code_str! {
        fn test_struct_3(p: int) {
            let c = Car { passengers: p, four_doors: true };
            assert(c.passengers == p);
            assert(!c.four_doors); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_4 STRUCTS.to_string() + verus_code_str! {
        fn test_struct_4(passengers: int) {
            assert((Car { passengers, four_doors: true }).passengers == passengers);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_enum_1 STRUCTS.to_string() + verus_code_str! {
        proof fn test_enum_1(passengers: int) {
            let t = Vehicle::Train(true);
            let c1 = Vehicle::Car(Car { passengers, four_doors: true });
            let c2 = Vehicle::Car(Car { passengers, four_doors: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_enum_struct verus_code! {
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
    #[test] test_enum_unit verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        enum AB {
            A,
            B(nat),
        }

        spec fn is_a(l: AB) -> bool {
            l == AB::A
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_struct_u8 STRUCTS.to_string() + verus_code_str! {
        fn test_struct_u8(car: CompactCar) {
            assert(car.passengers >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_struct_u8n STRUCTS.to_string() + verus_code_str! {
        fn test_struct_u8(car: CompactCar) {
            assert(car.passengers >= 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_struct_int STRUCTS.to_string() + verus_code_str! {
        fn test_struct_u8(car: Car) {
            assert(car.passengers >= 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_update1 verus_code! {
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
    #[test] test_update2 verus_code! {
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
    #[test] test_update2_fails verus_code! {
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
    #[test] test_spec_adt_ctor verus_code! {
        #[verifier::spec]
        struct SpecStruct { a: nat }

        fn test() {
            let s = SpecStruct { a: 12 }; // FAILS
            assert(s.a == 12);
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test_enum_adt_mod verus_code! {
        mod A {
            use builtin::*;
            pub enum E {
                A { a: u64 },
                B(u64)
            }
        }

        mod B {
            use crate::A::*;
            fn test() {
                let e = E::A { a: 12 };
                assert(match e { E::A { a } => a == 12, _ => false });
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_complex_arg verus_code! {
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
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_no_empty_enums verus_code! {
        enum Empty {
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] test_well_founded1 verus_code! {
        enum List {
            Cons(int, Box<List>)
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] test_well_founded2 verus_code! {
        enum List {
            Cons1(int, Box<List>),
            Cons2(int, Box<List>),
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] test_well_founded3 verus_code! {
        enum List1 {
            Cons(int, Box<List2>)
        }
        enum List2 {
            Cons(int, Box<List1>)
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] test_well_founded4 verus_code! {
        enum List {
            Cons(int, (Box<List>, bool))
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] test_well_field_unbox verus_code! {
        struct B { b: bool }
        fn foo(s1: Box<B>, s2: &Box<B>, s3: Box<&B>, s4: Box<(bool, bool)>) {
            let z1 = s1.b;
            let z2 = s2.b;
            let z3 = s3.b;
            let z4 = s4.0;
        }
    } => Ok(())
}

const IS_VARIANT_MAYBE: &str = verus_code_str! {
    #[is_variant]
    pub enum Maybe<T> {
        Some(T),
        None,
    }
};

test_verify_one_file! {
    #[test] test_is_variant_pass IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        pub fn test1(m: Maybe<u64>) {
            match m {
                Maybe::Some(_) => assert(m.is_Some()),
                Maybe::None => assert(m.is_None()),
            };
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] test_is_variant_illegal verus_code! {
        pub enum Maybe<T> {
            Some(T),
            None,
        }

        impl <T> Maybe<T> {
            #[doc(hidden)] #[verifier(is_variant)] /* vattr */ #[allow(non_snake_case)]
            spec fn is_Thing(&self) -> bool { ::core::panicking::panic("not implemented") }
        }
    } => Err(e) => assert_vir_error_msg(e, "unrecognized verifier attribute")
}

test_verify_one_file! {
    #[test] test_builtin_is_variant_invalid IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        proof fn foo(a: Maybe<nat>)
            requires a.is_None()
        {
            assert(builtin::is_variant(a, "Null"));
        }
    } => Err(err) => assert_vir_error_msg(err, "no variant `Null` for this datatype")
}

test_verify_one_file! {
    #[test] test_builtin_get_variant_field_invalid_1 IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        proof fn foo(a: Maybe<nat>)
            requires a == Maybe::Some(10nat),
        {
            assert(builtin::get_variant_field::<_, u64>(a, "Some", "0") == 10);
        }
    } => Err(err) => assert_vir_error_msg(err, "field has the wrong type")
}

test_verify_one_file! {
    #[test] test_builtin_get_variant_field_invalid_2 IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        proof fn foo(a: Maybe<nat>)
            requires a == Maybe::Some(10nat),
        {
            assert(builtin::get_variant_field::<_, nat>(a, "Some", "1") == 10);
        }
    } => Err(err) => assert_vir_error_msg(err, "no field `1` for this variant")
}

test_verify_one_file! {
    #[test] test_builtin_get_variant_field_invalid_3 IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        struct T { }
        proof fn test_fail(tracked u: Maybe<T>) {
            let tracked j = get_variant_field::<_, T>(u, "Some", "0");
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] test_is_variant_not_enum verus_code! {
        #[is_variant]
        pub struct Maybe<T> {
            t: T,
        }
    } => Err(err) => assert_vir_error_msg(err, "#[is_variant] is only allowed on enums")
}

test_verify_one_file! {
    #[test] test_is_variant_get_1 IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        pub fn test1(m: Maybe<u64>) {
            requires(m.is_Some() && m.get_Some_0() > 10);
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] test_is_variant_get_2 IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        pub fn test1(m: Maybe<u64>) -> (res: bool)
            ensures
                m.is_Some() ==> res == (m.get_Some_0() == 3),
                m.is_None() ==> !res,
        {
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

        pub fn test3(v: Maybe<u64>)
            requires
                v.is_Some() && v.get_Some_0() == 5,
        {
            if let Maybe::Some(a) = v {
                assert(a == 5);
            } else {
                vstd::pervasive::unreached::<()>();
            }
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] test_is_variant_get_fail IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        pub fn test1(m: Maybe<u64>) -> u64 {
            requires(m.get_Some_0() == 4);
            if let Maybe::Some(v) = m {
                v
            } else {
                vstd::pervasive::unreached() // FAILS
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
    #[test] test_is_variant_get_named_field verus_code! {
        #[is_variant]
        pub enum Res<T> {
            Ok { t: T },
            Err { v: u64 },
        }

        fn test1(m: Res<bool>)
            requires
                m.is_Err(),
                m.get_Err_v() == 42,
        {
            match m {
                Res::Ok { .. } => assert(false),
                Res::Err { v } => assert(v == 42),
            };
        }

        fn test2(m: &Res<bool>) -> (res: bool)
            ensures res <==> m.is_Ok() && m.get_Ok_t()
        {
            match m {
                Res::Ok { t } if *t => true,
                _ => false,
            }
        }

        fn caller() {
            let r = test2(&Res::Ok { t: false });
            assert(!r);
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] test_is_variant_no_field IS_VARIANT_MAYBE.to_string() + verus_code_str! {
        fn test1(v: Maybe<u64>) {
            assert(v.get_Some_1() == 3);
        }
    } => Err(err) => assert_rust_error_msg(err, "no method named `get_Some_1` found for enum `Maybe` in the current scope")
}

test_verify_one_file! {
    #[test] test_regression_tuple_1 verus_code! {
        struct B(bool);

        fn test1(b: B) {
            let z = b.0;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_enum_field_visibility verus_code! {
        #[is_variant]
        enum E {
            One(u64),
            Two(u64),
        }

        impl E {
            pub closed spec fn is_One_le(self, v: u64) -> bool {
                self.is_One() && self.get_One_0() <= v
            }
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] test_spec verus_code! {
        use vstd::modes::*;

        struct S {
            a: u8,
            b: Ghost<int>,
        }

        impl Clone for S {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl Copy for S {}

        impl S {
            fn equals(&self, rhs: &S) -> (b: bool)
                ensures
                    b == (self.a == rhs.a),
            {
                self.a == rhs.a
            }
        }

        fn test() -> (s: (S, S))
            ensures
                s.0 === s.1,
        {

            let s1 = S { a: 10, b: Ghost(20) };
            let s2 = s1;
            assert(s1.b@ == s2.b@);
            let b = s1.equals(&s2); assert(b);
            (s1, s2)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_spec_fails verus_code! {
        use vstd::modes::*;

        struct S {
            a: u8,
            b: Ghost<int>,
        }

        fn test() {
            let s1 = S { a: 10, b: Ghost(20) };
            let s2 = S { a: 10, b: Ghost(30) };
            assert(s1 === s2); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

const FIELD_UPDATE: &str = verus_code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct S {
        a: usize,
        b: i32,
    }
};

test_verify_one_file! {
    #[test] test_field_update_1_pass FIELD_UPDATE.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: 10, b: -10 };
            s.a = s.a + 1;
            s.b = s.b + 1;
            assert(s.a == 11 && s.b as int == -9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_1_fail FIELD_UPDATE.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: 10, b: -10 };
            s.a = s.a + 1;
            s.b = s.b + 1;
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_field_update_1_call_pass FIELD_UPDATE.to_string() + verus_code_str! {
        fn add1(a: i32) -> i32 {
            requires(a < 30);
            ensures(|ret: i32| ret == a + 1);
            a + 1
        }

        fn test() {
            let mut s = S { a: 10, b: -10 };
            s.a = s.a + 1;
            s.b = add1(s.b);
            assert(s.a == 11);
            assert(s.b == -9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_poly_pass verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        struct S<A> {
            a: A,
            b: i32,
        }

        fn test() {
            let mut s: S<usize> = S { a: 10, b: -10 };
            s.a = s.a + 1;
            s.b = s.b + 1;
            assert(s.a == 11 && s.b == -9);
        }
    } => Ok(())
}

const FIELD_UPDATE_2: &str = verus_code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct T {
        s: S,
        c: bool,
    }
};

test_verify_one_file! {
    #[test] test_field_update_2_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + verus_code_str! {
        fn test() {
            let mut t = T { s: S { a: 10, b: -10 }, c: false };
            t.s.a = t.s.a + 1;
            t.s.b = t.s.b + 1;
            assert(t == T { s: S { a: 11, b: -9 as i32 }, c: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_2_fails FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + verus_code_str! {
        fn test() {
            let mut t = T { s: S { a: 10, b: -10 }, c: false };
            t.s.a = t.s.a + 1;
            t.s.b = t.s.b + 1;
            t.c = true;
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_field_update_param_1_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + verus_code_str! {
        fn test(t: &mut T)
            requires
                old(t).s.a < 30,
                old(t).s.b < 30,
            ensures
                *t == (T { s: S { a: (old(t).s.a + 1) as usize, b: (old(t).s.b + 1) as i32 }, ..*old(t) })
        {
            t.s.a = t.s.a + 1;
            t.s.b = t.s.b + 1;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_param_1_fail FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + verus_code_str! {
        fn test(t: &mut T)
            requires
                old(t).s.a < 30,
                old(t).s.b < 30,
            ensures
                *t == (T { s: S { a: (old(t).s.a + 1) as usize, b: (old(t).s.b + 1) as i32 }, ..*old(t) })
        {
            t.s.a = t.s.a + 1;
            t.s.b = t.s.b + 1;
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_field_update_param_2_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + verus_code_str! {
        fn test(t: &mut T, v: usize)
            requires old(t).s.a < 30, v < 30
            ensures *t == (T { s: S { a: (old(t).s.a + v) as usize, ..old(t).s }, ..*old(t) })
        {
            t.s.a = t.s.a + v;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_param_mut_ref_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + verus_code_str! {
        fn foo(s: &mut S, v: usize)
            requires old(s).a < 30, v < 30
            ensures *s == (S { a: (old(s).a + v) as usize, ..*old(s) })
        {
            s.a = s.a + v;
        }

        fn test() {
            let mut t = T { s: S { a: 12, b: 12 }, c: false };
            foo(&mut t.s, 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    // TODO(utaal) fix this
    #[ignore] #[test] test_field_update_mode_fail_1 FIELD_UPDATE.to_string() + verus_code_str! {
        fn test(s: Ghost<S>) {
            proof {
                s@.a = (s@.a + 1) as usize;
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot assign to non-mut parameter")
}

test_verify_one_file! {
    // TODO(utaal) fix this
    #[ignore] #[test] test_field_update_mode_fail_2 FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + verus_code_str! {
        fn test(t: Ghost<T>) {
            proof {
                t@.s.a = (t@.s.a + 1) as usize;
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot assign to non-mut parameter")
}

const FIELD_UPDATE_MODES: &str = verus_code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct S {
        ghost a: nat,
        b: i32,
    }

    #[derive(PartialEq, Eq, Structural)]
    struct T {
        tracked s: S,
        c: bool,
    }
};

test_verify_one_file! {
    #[test] test_field_update_field_mode_pass_1 FIELD_UPDATE_MODES.to_string() + verus_code_str! {
        fn test(t: T) {
            t.s.a = t.s.a;
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot assign to non-mut parameter")
}

const ENUM_S: &str = verus_code_str! {
    #[is_variant]
    enum S {
        V1,
        V2,
    }
};

test_verify_one_file! {
    #[test] test_match_exhaustiveness_regression_127 ENUM_S.to_string() + verus_code_str! {
        fn f(s: S) {
            match s {
                S::V1 => assert(true),
            };
        }
    } => Err(err) => assert_rust_error_msg(err, "non-exhaustive patterns: `S::V2` not covered")
}

test_verify_one_file! {
    #[test] test_match_empty_branch ENUM_S.to_string() + verus_code_str! {
        fn f(s: Ghost<S>) {
            proof {
                match s@ {
                    S::V1 => assert(s@.is_V1()),
                    S::V2 => (),
                };
            }
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    // TODO(utaal) fix this
    #[ignore] #[test] test_if_is_variant_regression_125 verus_code! {
        use vstd::option::*;

        proof fn foo() {
            let x: int = (if (Option::<int>::Some(5int)).is_Some() { 0 } else { 1 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_if_is_variant_underscore_in_name_regression verus_code! {
        #[is_variant]
        #[allow(non_camel_case_types)]
        enum Has_Underscores {
            #[allow(non_camel_case_types)]
            More_Underscores,
            #[allow(non_camel_case_types)]
            A_Couple_More(nat),
        }

        proof fn test(h: Has_Underscores)
            requires
                h.is_A_Couple_More(),
                match h {
                    Has_Underscores::More_Underscores => false,
                    Has_Underscores::A_Couple_More(x) => x == 10,
                },
        {
            assert(h.get_A_Couple_More_0() == 10);
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] type_alias_basic verus_code!{
        struct Foo {
            u: u64,
        }

        type X = Foo;

        fn test1(x: X)
            requires x.u == 5
        {
            let u = x.u;
            assert(u == 5);
        }

        struct Bar<T> {
            u: T,
        }

        type Y<T> = Bar<T>;

        fn test2<T>(x: Y<T>, t: T)
            requires equal(x.u, t)
        {
            let u = x.u;
            assert(equal(u, t));
        }

        fn test3<S>(x: Y<S>, t: S)
            requires equal(x.u, t)
        {
            let u = x.u;
            assert(equal(u, t));
        }


        fn test4<T>(x: Y<u64>)
            requires x.u == 5
        {
            let u = x.u;
            assert(u == 5);
        }

        fn test5(x: Y<Bar<u64>>, b: Bar<u64>)
            requires equal(x.u, b)
        {
            let u = x.u;
            assert(equal(u, b));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] is_variant_with_attribute_regression_480 verus_code! {
        #[is_variant]
        #[verifier::reject_recursive_types(T)]
        enum X<T> {
            ZZ(T),
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] resolve_ctors_for_struct_syntax verus_code!{
        pub struct Animal {
            num_legs: u8,
        }

        pub type Ani = Animal;

        fn mk_animal() {
            let y = Ani { num_legs: 3 };
            let Ani { num_legs } = y;
            assert(num_legs == 3);
        }

        impl Animal {
            fn new() {
                let y = Self { num_legs: 4 };
                let Self { num_legs } = y;
                assert(num_legs == 4);
            }
        }



        pub enum Direction {
          Left{},
          Right{},
        }

        pub type Node = Direction;

        fn mk_node() {
            let y = Node::Left { };
            match y {
                Node::Left { } => {
                }
                Node::Right { } => {
                    assert(false);
                }
            }
        }

        impl Direction {
            fn new() {
                let y = Self::Left { };
                match y {
                    Self::Left { } => {
                    }
                    Self::Right { } => {
                        assert(false);
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] resolve_ctors_for_function_syntax verus_code!{
        pub struct Animal(u8);

        pub type Ani = Animal;

        fn mk_animal() {
            // Looks like Rust doesn't support using a type alias `Ani` in this scenario
            //let y = Ani(3);
            //let Ani(num_legs) = y;
            //assert(num_legs == 3);
        }

        impl Animal {
            fn new() {
                let y = Self(4);
                let Self(num_legs) = y;
                assert(num_legs == 4);
            }
        }

        pub enum Direction {
          Left(u8),
          Right(u8),
        }

        pub type Node = Direction;

        fn mk_node() {
            let y = Node::Left(12);
            match y {
                Node::Left(z) => {
                    assert(z == 12);
                }
                Node::Right(z) => {
                    assert(false);
                }
            }
        }

        impl Direction {
            fn new() {
                let y = Self::Left(5);
                match y {
                    Self::Left(z) => {
                        assert(z == 5);
                    }
                    Self::Right(z) => {
                        assert(false);
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] resolve_ctors_for_unit_syntax verus_code!{
        pub struct Animal;

        pub type Ani = Animal;

        fn mk_animal() {
            // Looks like Rust doesn't support using a type alias `Ani` in this scenario
            //let y = Ani;
            //let Ani = y;
        }

        impl Animal {
            fn new() {
                let y = Self;
                let Self = y;
                assert(false); // FAILS
            }
        }



        pub enum Direction {
          Left,
          Right,
        }

        pub type Node = Direction;

        fn mk_node() {
            let y = Node::Left;
            match y {
                Node::Left => {
                }
                Node::Right => {
                }
            }
        }

        impl Direction {
            fn new() {
                let y = Self::Left;
                match y {
                    Self::Left => {
                    }
                    Self::Right => {
                        assert(false);
                    }
                }
            }
        }
    } => Err(err) => assert_one_fails(err)
}

const IS_GET_SYNTAX_COMMON: &'static str = verus_code_str! {
    enum ThisOrThat {
        This(nat),
        That { v: int },
    }
};

test_verify_one_file! {
    #[test] is_syntax_pass IS_GET_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn uses_is(t: ThisOrThat) {
            match t {
                ThisOrThat::This(..) => assert(t is This),
                ThisOrThat::That {..} => assert(t is That),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] is_syntax_valid_fail IS_GET_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn uses_is(t: ThisOrThat) {
            match t {
                ThisOrThat::This(..) => assert(t is That), // FAILS
                ThisOrThat::That {..} => assert(t is That),
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] is_syntax_invalid IS_GET_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn uses_is(t: ThisOrThat) {
            assert(t is Unknown);
        }
    } => Err(err) => assert_vir_error_msg(err, "no variant `Unknown` for this datatype")
}

test_verify_one_file! {
    #[test] is_syntax_precedence IS_GET_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn uses_is(t: ThisOrThat)
            requires t is This,
        {
            assert(t is This != t is That);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] is_syntax_implies IS_GET_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn uses_is(t: ThisOrThat)
            requires t is This,
        {
            assert(t is This ==> true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_syntax_with_numeric_field_names verus_code! {
        #[is_variant]
        enum Foo {
            Bar(u32, u32),
            Qux,
        }

        fn test() {
            let b = Foo::Bar { 1: 30, 0: 20 };
            assert(b.get_Bar_0() == 20);
            assert(b.get_Bar_1() == 30);
        }

        fn test2() {
            let b = Foo::Bar { 1: 30, 0: 20 };
            assert(b.get_Bar_1() == 20); // FAILS
        }


        fn test_pat(foo: Foo) {
            let foo = Foo::Bar(20, 40);
            match foo {
                Foo::Bar { 1: a, 0: b } => {
                    assert(b == 20);
                    assert(a == 40);
                }
                Foo::Qux => { assert(false); }
            }
        }

        fn test_pat2(foo: Foo) {
            let foo = Foo::Bar(20, 40);
            match foo {
                Foo::Bar { 1: a, 0: b } => {
                    assert(b == 40); // FAILS
                }
                Foo::Qux => { }
            }
        }

        fn test_pat_not_all_fields(foo: Foo) {
            let foo = Foo::Bar(20, 40);
            match foo {
                Foo::Bar { 1: a, .. } => {
                    assert(a == 40);
                }
                Foo::Qux => { assert(false); }
            }
        }

        fn test_pat_not_all_fields2(foo: Foo) {
            let foo = Foo::Bar(20, 40);
            match foo {
                Foo::Bar { 1: a, .. } => {
                    assert(a == 20); // FAILS
                }
                Foo::Qux => { }
            }
        }

        spec fn sfn(foo: Foo) -> (u32, u32) {
            match foo {
                Foo::Bar { 1: a, 0: b } => (b, a),
                Foo::Qux => (0, 0),
            }
        }

        proof fn test_sfn(foo: Foo) {
            assert(sfn(Foo::Bar(20, 30)) == (20u32, 30u32));
            assert(sfn(Foo::Qux) == (0u32, 0u32));
        }

        proof fn test_sfn2(foo: Foo) {
            assert(sfn(Foo::Bar(20, 30)).0 == 30); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] get_syntax_1 IS_GET_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn test1(t: ThisOrThat)
            requires t is That && t->v == 3
        {
            match t {
                ThisOrThat::This(_) => (),
                ThisOrThat::That { v } => { assert(v == 3); }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] get_syntax_2_pass verus_code! {
        tracked enum S<T> {
            This(T),
            That { v: int },
            Other { t: T },
        }

        proof fn test1(t: S<nat>)
            requires ({
                &&& t is That ==> t->v == 3
                &&& t is This ==> t->0 == 2
            })
        {
            match t {
                S::This(a) => {
                    assert(a == 2);
                }
                S::That { v } => {
                    assert(v == 3);
                }
                _ => (),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] get_syntax_2_fail verus_code! {
        tracked enum S<T> {
            This(T),
            That { v: int },
            Other { t: T },
        }

        proof fn test1(t: S<nat>)
            requires ({
                &&& t is That ==> t->v == 3
                &&& t is This ==> t->0 == 2
            })
        {
            match t {
                S::This(a) => {
                    assert(a == 3); // FAILS
                }
                _ => (),
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] get_syntax_3_fail_1 verus_code! {
        tracked enum S {
            This { v: int },
            That { v: int },
        }

        proof fn test1(t: S)
            requires t is That ==> t->v == 3 { }
    } => Err(err) => assert_vir_error_msg(err, "this field is present in multiple variants")
}

test_verify_one_file! {
    #[test] get_syntax_3_fail_2 verus_code! {
        tracked enum S {
            This(int),
            That(int),
        }

        proof fn test1(t: S)
            requires t is That ==> t->0 == 3 { }
    } => Err(err) => assert_vir_error_msg(err, "this field is present in multiple variants")
}

test_verify_one_file! {
    #[test] get_syntax_3_fail_3 verus_code! {
        tracked enum S<T> {
            This { v: T },
            That { v: T },
        }

        proof fn test1(t: S<nat>)
            requires t is That ==> t->v == 3 { }
    } => Err(err) => assert_vir_error_msg(err, "this field is present in multiple variants")
}

test_verify_one_file! {
    #[test] get_syntax_3_fail_4 verus_code! {
        tracked enum S<T> {
            This { v: nat },
            That { v: T },
        }

        proof fn test1(t: S<nat>)
            requires t is That ==> t->v == 3 { }
    } => Err(err) => {
        assert_rust_error_msg(err.clone(), "no method named `arrow_v`");
        assert!(err.warnings.iter().find(|w| w.message.contains("field `v` has inconsistent type or visibility in different variants")).is_some())
    }
}

test_verify_one_file! {
    #[test] get_syntax_3_fail_5 verus_code! {
        #[allow(inconsistent_fields)]
        tracked enum S<T> {
            This { v: nat },
            That { v: T },
        }

        proof fn test1(t: S<nat>)
            requires t is That ==> t->v == 3 { }
    } => Err(err) => {
        assert_rust_error_msg(err.clone(), "no method named `arrow_v`");
        assert_eq!(err.warnings.len(), 0);
    }
}

const MATCHES_SYNTAX_COMMON: &str = verus_code_str! {
    tracked enum S {
        This(nat),
        That { v: int },
        Other { v: int },
    }
};

test_verify_one_file! {
    #[test] matches_syntax_1_pass MATCHES_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn test1(t: S)
            requires ({
                &&& t matches S::That { v: a } ==> a == 3
                &&& t matches S::This(v) ==> v == 4
            })
        {
            match t {
                S::This(v) => assert(v == 4),
                S::That { v: a } => assert(a == 3),
                _ => (),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] matches_syntax_1_fails MATCHES_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn test1(t: S)
            requires ({
                &&& t matches S::That { v: a } ==> a == 3
                &&& t matches S::This(v) ==> v == 4
            })
        {
            match t {
                S::This(v) => assert(v == 3), // FAILS
                _ => (),
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] matches_syntax_2 MATCHES_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn test1(t: S)
            requires ({
                &&& t matches S::That { v: _ }
            })
        {
            assert(t is That);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] matches_syntax_3 MATCHES_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn test1(t: S)
            requires ({
                && t matches S::That { v: a }
                && a == 3
            })
        {
            assert(t is That);
            assert(match t {
                S::That { v } => v == 3,
                _ => false,
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] matches_syntax_4 MATCHES_SYNTAX_COMMON.to_string() + verus_code_str! {
        proof fn test1(t: S)
            requires ({
                &&& t matches S::That { v: a }
                &&& a > 3
                &&& a < 5
            })
        {
            assert(t is That);
            assert(match t {
                S::That { v } => v == 4,
                _ => false,
            });
        }
    } => Ok(())
}

const MATCHES_PRECEDENCE_COMMON: &str = verus_code_str! {
    tracked enum A {
        A1 { v: nat },
        A2 { v: nat },
    }

    enum B {
        B1(A),
        B2 { a: A },
    }

};

test_verify_one_file! {
    #[test] matches_syntax_precedence_1 MATCHES_PRECEDENCE_COMMON.to_string() + verus_code_str! {
        proof fn test(b: B)
            requires b matches B::B1(a) ==> a matches A::A1 { v } ==> v == 3,
        {
            match b {
                B::B1(A::A1 { v }) => assert(v == 3),
                _ => (),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] matches_syntax_precedence_2 MATCHES_PRECEDENCE_COMMON.to_string() + verus_code_str! {
        proof fn test(b: B)
            requires
                b matches B::B1(a) ==> a matches A::A1 { v } ==> v == 3,
                b matches B::B2 { a: x } ==> x matches A::A1 { v } ==> v == 3,
        {
            match b {
                B::B1(A::A1 { v }) => assert(v == 3),
                B::B2 { a: A::A1 { v } } => assert(v == 3),
                _ => (),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] matches_syntax_precedence_3 verus_code! {
        enum E { A, B }
        proof fn test1() {
            assert((E::A matches E::B ==> true) <==> false); // FAILS
        }
        proof fn test2() {
            assert(E::A matches E::B ==> true <==> false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] matches_syntax_assoc_1 MATCHES_PRECEDENCE_COMMON.to_string() + verus_code_str! {
        proof fn test1() {
            let a = A::A1 { v: 3 };
            assert(a matches A::A1 { v } && v == 3);
            assert(a matches A::A1 { v } && v == 3 && v == 3);
            assert(a matches A::A1 { v } && v == 3 && (v == 3 || v == 4));
            assert(a matches A::A1 { v } && (v == 3 || v == 4));
            assert(!(a matches A::A1 { v } && (v == 2 || v == 4)));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] matches_syntax_assoc_fail_1 MATCHES_PRECEDENCE_COMMON.to_string() + verus_code_str! {
        proof fn test1() {
            let a = A::A1 { v: 3 };
            assert(a matches A::A1 { v } && v == 3 || v == 4);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot find value `v` in this scope")
}

fn matches_syntax_context(expr: &str) -> String {
    r#"
    builtin_macros::verus! {
        enum E { A, B }
        proof fn test1() {
            assert("#
        .to_string()
        + expr
        + r#");
        }
    }
    "#
}

macro_rules! test_matches_syntax_err {
    ($(#[$attrs:meta])* $name:ident with $code:tt $msg:expr) => {
        test_verify_one_file! {
            $(#[$attrs])* $name matches_syntax_context(code_str! { $code })
            => Err(err) => assert_vir_error_msg(err, $msg)
        }
    }
}

test_matches_syntax_err! {
    #[test] matches_syntax_precedence_4a with (false && E::A matches E::A ==> true)
    "matches with ==> is currently not allowed on the right-hand-side of most binary operators (use parentheses)"
}

test_matches_syntax_err! {
    #[test] matches_syntax_precedence_4b with (false || E::A matches E::A ==> true)
    "matches with ==> is currently not allowed on the right-hand-side of most binary operators (use parentheses)"
}

test_matches_syntax_err! {
    #[test] matches_syntax_precedence_5 with (false == E::A matches E::A && true)
    "matches with && is currently not allowed on the right-hand-side of most binary operators (use parentheses)"
}

test_matches_syntax_err! {
    #[test] matches_syntax_precedence_6 with (false <==> E::A matches E::A ==> true)
    "matches with ==> is currently not allowed on the right-hand-side of most binary operators (use parentheses)"
}

test_matches_syntax_err! {
    #[test] matches_syntax_precedence_nonsensical_1 with (3 < E::A matches E::A ==> true)
    "matches with ==> is currently not allowed on the right-hand-side of most binary operators (use parentheses)"
}

test_matches_syntax_err! {
    #[test] matches_syntax_precedence_nonsensical_2 with (3 >> E::A matches E::A ==> true)
    "matches with ==> is currently not allowed on the right-hand-side of most binary operators (use parentheses)"
}

test_verify_one_file! {
    #[test] matches_syntax_precedence_10 verus_code! {
        enum E { A, B }
        proof fn test1() {
            assert(false && false ==> false);
            assert(E::A matches E::B && false ==> false);

            assert(!(false && false == false));
            assert(!(E::A matches E::B && false == false));

            assert(false && true ==> true);
            assert(E::A matches E::B && true ==> true);

            assert(!(true && true ==> false));
            assert(!(E::A matches E::A && true ==> false));

            assert(true && true || false);
            assert(E::A matches E::A && true || false);

            assert(!(false && true || false));
            assert(!(E::A matches E::B && true || false));

            assert(!(true || true ==> false));
            assert(!(E::A matches E::A || true ==> false));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parsing_fail_1 verus_code! {
        enum E { A, B }
        proof fn a() {
            assert({
                E::A matches E::A
                &&& true
            })
        }
    } => Err(err) => assert_vir_error_msg(err, "in &&&, a matches expression needs to be prefixed with &&&")
}

test_verify_one_file! {
    #[test] field_of_unencoded_struct_in_impl_regression_881_1008 verus_code! {
        mod m1 {
            pub trait A {
                spec fn foo(&self) -> u64;
            }

            pub struct S {
                pub f1: u64,
                f2: u64,
            }

            impl A for S {
                open spec fn foo(&self) -> u64 {
                    self.f1
                }
            }
        }

        mod m2 {
            use crate::m1::*;

            fn bar(a: S) {
                let ghost f1 = a.foo();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot access any field of a datatype where one or more fields are private")
}

test_verify_one_file! {
    #[test] field_of_unencoded_struct_in_impl_regression_578 verus_code! {
        use vstd::prelude::*;

        mod log {
            use vstd::prelude::*;
            pub struct Device{
                pub dev: Vec<u8>,
                size: usize,
                head: usize,
                pub tail: usize,
            }

            impl Device {
                pub fn new(size: usize) -> Self
                {
                    Self {
                        dev: Vec::with_capacity(size),
                        size,
                        head: 0,
                        tail: 0,
                    }
                }

                pub fn write_byte(&mut self, dst: usize, byte: u8)
                    requires
                        dst < old(self).dev.len()
                {
                    self.dev.set(dst, byte);
                }
            }
        }

        use crate::log::*;
        fn main() {
            let mut dev = Device::new(4096);
            dev.write_byte(0, 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "in 'requires' clause of public function, cannot access any field of a datatype where one or more fields are private")
}

test_verify_one_file! {
    #[test] test_arrow_with_variant verus_code! {
        #[is_variant]
        pub enum E<T> {
            One { t: T },
            Two { t: T },
            Three(T),
        }

        pub fn test1(e: E<u64>) -> (res: bool)
            ensures
                e is One ==> res == (e->One_t == 3),
                e is Two ==> !res,
                e is Three ==> res == (e->Three_0 == 4),
        {
            match e {
                E::One { t } => t == 3,
                E::Two { t: _ } => false,
                E::Three(t) => t == 4,
            }
        }
    } => Ok(err) => {
        dbg!(&err);
        assert!(err.errors.len() == 0);
        assert!(err.warnings.iter().find(|w| w.message == "`#[is_variant]` is deprecated - use `->` or `matches` instead").is_some());
    }
}

test_verify_one_file! {
    #[test] test_mut_ref_fields_generic_adt_nested verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            i: u8,
            j: u8,
        }

        struct Pair<A, B> {
            a: A,
            b: B,
        }

        fn mutate_int(i: &mut u8) { }

        fn test1() {
            let mut t = Pair { a: X { i: 10, j: 8 }, b: Y { i: 100, j: 100 } };
            mutate_int(&mut t.a.j);
        }

        fn mutate_int_2(i: &mut u8)
            requires *old(i) == 19,
            ensures *i == 30,
        {
            *i = 30;
        }

        fn test2() {
            let mut t = Pair { a: X { i: 10, j: 19 }, b: Y { i: 100, j: 100 } };
            mutate_int_2(&mut t.a.j);
            assert(t == Pair { a: X { i: 10, j: 30 }, b: Y { i: 100, j: 100 } });
        }

        fn test3() {
            let mut t = Pair { a: X { i: 10, j: 19 }, b: Y { i: 100, j: 100 } };
            mutate_int_2(&mut t.a.j);
            assert(t == Pair { a: X { i: 10, j: 30 }, b: Y { i: 100, j: 100 } });
            assert(false); // FAILS
        }

        fn test4() {
            let mut t = Pair { a: X { i: 10, j: 19 }, b: Y { i: 100, j: 100 } };
            mutate_int_2(&mut t.a.i); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
