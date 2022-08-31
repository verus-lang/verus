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
    #[test] test_struct_int STRUCTS.to_string() + verus_code_str! {
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
    } => Ok(())
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

test_verify_one_file! {
    #[test] test_regression_tuple_1 code! {
        struct B(bool);

        fn test1(b: B) {
            let z = b.0;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_enum_field_visibility code! {
        #[is_variant]
        enum E {
            One(u64),
            Two(u64),
        }

        impl E {
            #[spec]
            pub fn is_One_le(self, v: u64) -> bool {
                self.is_One() && self.get_One_0() <= v
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_spec verus_code! {
        use crate::pervasive::modes::*;

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

            let s1 = S { a: 10, b: ghost(20) };
            let s2 = s1;
            assert(s1.b@ == s2.b@);
            let b = s1.equals(&s2); assert(b);
            (s1, s2)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_spec_fails verus_code! {
        use crate::pervasive::modes::*;

        struct S {
            a: u8,
            b: Ghost<int>,
        }

        fn test() {
            let s1 = S { a: 10, b: ghost(20) };
            let s2 = S { a: 10, b: ghost(30) };
            assert(s1 === s2); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

const FIELD_UPDATE: &str = code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct S {
        a: usize,
        b: i32,
    }
};

test_verify_one_file! {
    #[test] test_field_update_1_pass FIELD_UPDATE.to_string() + code_str! {
        fn test() {
            let mut s = S { a: 10, b: -10 };
            s.a = s.a + 1;
            s.b = s.b + 1;
            assert(s.a == 11 && s.b == -9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_1_fail FIELD_UPDATE.to_string() + code_str! {
        fn test() {
            let mut s = S { a: 10, b: -10 };
            s.a = s.a + 1;
            s.b = s.b + 1;
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_field_update_1_call_pass FIELD_UPDATE.to_string() + code_str! {
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
    #[test] test_field_update_poly_pass code! {
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

const FIELD_UPDATE_2: &str = code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct T {
        s: S,
        c: bool,
    }
};

test_verify_one_file! {
    #[test] test_field_update_2_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + code_str! {
        fn test() {
            let mut t = T { s: S { a: 10, b: -10 }, c: false };
            t.s.a = t.s.a + 1;
            t.s.b = t.s.b + 1;
            assert(t == T { s: S { a: 11, b: -9 }, c: false });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_2_fails FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + code_str! {
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
    #[test] test_field_update_param_1_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + code_str! {
        fn test(t: &mut T) {
            requires([old(t).s.a < 30, old(t).s.b < 30]);
            ensures(*t == T { s: S { a: old(t).s.a + 1, b: old(t).s.b + 1 }, ..*old(t) });
            t.s.a = t.s.a + 1;
            t.s.b = t.s.b + 1;
        }
    } => Ok(())
}

test_verify_one_file! {
    // TODO fix this
    #[ignore] #[test] test_field_update_param_1_fail FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + code_str! {
        fn test(t: &mut T) {
            requires([old(t).s.a < 30, old(t).s.b < 30]);
            ensures(*t == T { s: S { a: old(t).s.a + 1, b: old(t).s.b + 1 }, ..*old(t) });
            t.s.a = t.s.a + 1;
            t.s.b = t.s.b + 1;
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // TODO fix this
    #[ignore] #[test] test_field_update_param_2_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + code_str! {
        fn test(t: &mut T, v: usize) {
            requires(old(t).s.a < 30);
            ensures(*t == T { s: S { a: old(t).s.a + v, ..old(t).s }, ..*old(t) });
            t.s.a = t.s.a + v;
        }
    } => Ok(())
}

test_verify_one_file! {
    // TODO fix this
    #[ignore] #[test] test_field_update_param_mut_ref_pass FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + code_str! {
        fn foo(s: &mut S, v: usize) {
            requires(old(s).a < 30);
            ensures(*s == S { a: old(s).a + v, ..*old(s) });
            s.a = s.a + v;
        }

        fn test() {
            let mut t = T { s: S { a: 12, b: 12 }, c: false };
            foo(&mut t.s, 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_field_update_mode_fail_1 FIELD_UPDATE.to_string() + code_str! {
        fn test(#[spec] s: S) {
            s.a = s.a + 1;
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_field_update_mode_fail_2 FIELD_UPDATE.to_string() + FIELD_UPDATE_2 + code_str! {
        fn test(#[spec] t: T) {
            t.s.a = t.s.a + 1;
        }
    } => Err(e) => assert_vir_error(e)
}

const FIELD_UPDATE_MODES: &str = code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct S {
        #[spec] a: nat,
        b: i32,
    }

    #[derive(PartialEq, Eq, Structural)]
    struct T {
        #[proof] s: S,
        c: bool,
    }
};

test_verify_one_file! {
    #[test] test_field_update_field_mode_pass_1 FIELD_UPDATE_MODES.to_string() + verus_code_str! {
        fn test(t: T) {
            t.s.a = t.s.a;
        }
    } => Err(e) => assert_vir_error(e)
}

const ENUM_S: &str = code_str! {
    #[is_variant]
    enum S {
        V1,
        V2,
    }
};

test_verify_one_file! {
    #[test] test_match_exhaustiveness_regression_127 ENUM_S.to_string() + code_str! {
        fn f(s: S) {
            match s {
                S::V1 => assert(true),
            };
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_match_empty_branch ENUM_S.to_string() + code_str! {
        fn f(#[spec] s: S) {
            match s {
                S::V1 => assert(s.is_V1()),
                S::V2 => (),
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_if_is_variant_regression_125 code! {
        use crate::pervasive::option::*;

        #[proof]
        fn foo() {
            let x = (if (Option::Some(5)).is_Some() { 0 } else { 1 });
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
    #[test] type_alias_basic code!{
        struct Foo {
            u: u64,
        }

        type X = Foo;

        fn test1(x: X) {
            requires(x.u == 5);

            let u = x.u;
            assert(u == 5);
        }

        struct Bar<T> {
            u: T,
        }

        type Y<T> = Bar<T>;

        fn test2<T>(x: Y<T>, t: T) {
            requires(equal(x.u, t));

            let u = x.u;
            assert(equal(u, t));
        }

        fn test3<S>(x: Y<S>, t: S) {
            requires(equal(x.u, t));

            let u = x.u;
            assert(equal(u, t));
        }


        fn test4<T>(x: Y<u64>) {
            requires(x.u == 5);

            let u = x.u;
            assert(u == 5);
        }

        fn test5(x: Y<Bar<u64>>, b: Bar<u64>) {
            requires(equal(x.u, b));

            let u = x.u;
            assert(equal(u, b));
        }
    } => Ok(())
}
