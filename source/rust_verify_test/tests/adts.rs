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
    } => Ok(())
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
    } => Ok(())
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
    } => Ok(())
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
    } => Ok(())
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
    } => Ok(())
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
    } => Ok(())
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
    } => Ok(())
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
    } => Ok(())
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
