#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Use external_type_specification on an external type from the same crate

test_verify_one_file! {
    #[test] test_basics verus_code! {
        #[verifier(external)]
        struct SomeStruct<T> { t: T }

        #[verifier(external)]
        enum SomeEnum<T> {
            One(T),
            Two,
        }

        #[verifier(external)]
        struct SomeExternalBodyThing<T> { t: T }

        #[verifier(external_type_specification)]
        struct ExSomeStruct<U>(SomeStruct<U>);

        #[verifier(external_type_specification)]
        struct ExSomeEnum<U>(SomeEnum<U>);

        #[verifier(external_type_specification)]
        #[verifier(external_body)]
        #[verifier(reject_recursive_types(U))]
        struct ExSomeExternalBodyThing<U>(SomeExternalBodyThing<U>);

        fn test() {
            let ss = SomeStruct::<u64> { t: 5 };
            assert(ss.t == 5);

            let se = SomeEnum::<u8>::One(9);
            match se {
                SomeEnum::One(x) => { assert(x == 9); }
                SomeEnum::Two => { assert(false); }
            }
        }

        fn test2(y: SomeExternalBodyThing<u8>, z: SomeExternalBodyThing<u8>) {
            assert(y == z); // FAILS
        }

        fn test3() {
            let ss = SomeStruct::<u64> { t: 5 };
            assert(ss.t == 6); // FAILS
        }

        fn test4() {
            let se = SomeEnum::<u8>::One(9);
            match se {
                SomeEnum::One(x) => {
                    assert(false); // FAILS
                }
                SomeEnum::Two => { }
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

// Use external_type_specification on an external type from a different crate

test_verify_one_file! {
    #[test] test_basics2 verus_code! {

        // enum
        #[verifier(external_type_specification)]
        pub struct ExOption<V>(core::option::Option<V>);

        // struct
        #[verifier(external_type_specification)]
        pub struct ExRange<Idx>(core::ops::Range<Idx>);

        // external_body thing
        #[verifier(external_type_specification)]
        #[verifier(external_body)]
        pub struct ExDuration(core::time::Duration);

        fn test() {
            let ss = core::ops::Range::<u8> { start: 5, end: 7 };
            assert(ss.start == 5);

            let se = core::option::Option::Some(5);
            match se {
                Option::Some(x) => { assert(x == 5); }
                Option::None => { assert(false); }
            }
        }

        fn test2(y: core::time::Duration, z: core::time::Duration) {
            assert(y == z); // FAILS
        }

        fn test3() {
            let ss = core::ops::Range::<u8> { start: 5, end: 7 };
            assert(ss.start == 7); // FAILS
        }

        fn test4() {
            let se = core::option::Option::Some(5);
            match se {
                Option::Some(x) => {
                    assert(false); // FAILS
                }
                Option::None => { }
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

// Import specifications from vstd

test_verify_one_file! {
    #[test] test_basics3 verus_code! {
        use vstd::*;

        fn test() {
            let ss = core::ops::Range::<u8> { start: 5, end: 7 };
            assert(ss.start == 5);

            let se = core::option::Option::Some(5);
            match se {
                Option::Some(x) => { assert(x == 5); }
                Option::None => { assert(false); }
            }
        }

        fn test2(y: core::time::Duration, z: core::time::Duration) {
            assert(y == z); // FAILS
        }

        fn test3() {
            let ss = core::ops::Range::<u8> { start: 5, end: 7 };
            assert(ss.start == 7); // FAILS
        }

        fn test4() {
            let se = core::option::Option::Some(5);
            match se {
                Option::Some(x) => {
                    assert(false); // FAILS
                }
                Option::None => { }
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

// Test for overlap

test_verify_one_file! {
    #[test] test_overlap verus_code! {
        #[verifier(external)]
        struct X { }

        #[verifier(external_type_specification)]
        struct ExX(X);

        #[verifier(external_type_specification)]
        struct ExY(X);
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `crate::X`")
}

test_verify_one_file! {
    #[test] test_overlap2 verus_code! {
        #[verifier(external_type_specification)]
        pub struct ExOption1<T>(core::option::Option<T>);

        #[verifier(external_type_specification)]
        pub struct ExOption2<T>(core::option::Option<T>);
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::option::Option`")
}

test_verify_one_file! {
    #[test] test_overlap3 verus_code! {
        use vstd::*;

        // This will conflict with the std::option::Option specification declared in vstd
        #[verifier(external_type_specification)]
        pub struct ExOption1<T>(core::option::Option<T>);
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::option::Option`")
}

// Test sane error message if you try to use a proxy type

test_verify_one_file! {
    #[test] test_use_proxy verus_code! {
        #[verifier(external_type_specification)]
        pub struct ExOption1<T>(core::option::Option<T>);

        pub fn test(a: ExOption1<u8>) { }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type marked `external_type_specification`")
}

test_verify_one_file! {
    #[test] test_use_proxy2 verus_code! {
        pub fn test(a: vstd::std_specs::core::ExOption<u8>) { }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type marked `external_type_specification`")
}

test_verify_one_file! {
    #[test] test_use_proxy3 verus_code! {
        #[verifier(external_type_specification)]
        pub struct ExOption1<T>(core::option::Option<T>);

        pub fn test() {
            let a = ExOption1::<u8>(core::option::Option::<u8>::None);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type marked `external_type_specification`")
}

test_verify_one_file! {
    #[test] test_use_external verus_code! {
        #[verifier(external)]
        struct X { }

        fn test() {
            let x = X { };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type marked `external`")
}

// If you wrongly try to apply a mode

test_verify_one_file! {
    #[test] test_proxy_marked_ghost verus_code! {
        #[verifier(external_type_specification)]
        pub ghost struct ExOption<T>(core::option::Option<T>);
    } => Err(err) => assert_vir_error_msg(err, "external_type_specification can only be used with exec types")
}

test_verify_one_file! {
    #[test] test_proxy_marked_tracked verus_code! {
        #[verifier(external_type_specification)]
        pub tracked struct ExOption<T>(core::option::Option<T>);
    } => Err(err) => assert_vir_error_msg(err, "external_type_specification can only be used with exec types")
}

// Test visibility stuff

test_verify_one_file! {
    #[test] test_visible verus_code! {
        #[verifier(external_type_specification)]
        struct ExOption1<T>(core::option::Option<T>);
    } => Err(err) => assert_vir_error_msg(err, "`external_type_specification` proxy type should be visible to the external type")
}

test_verify_one_file! {
    #[test] test_visible2 verus_code! {
        #[verifier(external)]
        pub struct X { }

        #[verifier(external_type_specification)]
        struct Ex(X);
    } => Err(err) => assert_vir_error_msg(err, "`external_type_specification` proxy type should be visible to the external type")
}

// test the attribute in weird places

test_verify_one_file! {
    #[test] test_attr_on_enum verus_code! {
        #[verifier(external_type_specification)]
        enum Ex {
            Stuff(u8)
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_type_specification` proxy type should use a struct with a single field to declare the external type (even if the external type is an enum)")
}

test_verify_one_file! {
    #[test] test_attr_on_fn verus_code! {
        #[verifier(external_type_specification)]
        pub fn stuff() { }
    } => Err(err) => assert_vir_error_msg(err, "`external_type_specification` attribute not supported here")
}

// Mismatched generics

test_verify_one_file! {
    #[test] mismatch_generics verus_code! {

        #[verifier(external)]
        struct Foo<X, Y> { x: X, y: Y }

        #[verifier(external_type_specification)]
        struct ExFoo<X, Y>(Foo<Y, X>);

    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

test_verify_one_file! {
    #[test] mismatch_generics2 verus_code! {

        #[verifier(external)]
        struct Foo<X, Y> { x: X, y: Y }

        #[verifier(external_type_specification)]
        struct ExFoo<X>(Foo<X, X>);

    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

test_verify_one_file! {
    #[test] mismatch_generics3 verus_code! {

        #[verifier(external)]
        struct Foo<X, Y, 'a, 'b> { x: &'a X, y: &'b Y }

        #[verifier(external_type_specification)]
        struct ExFoo<X, Y, 'a, 'b>(Foo<X, Y, 'b, 'a>);

    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

test_verify_one_file! {
    #[test] mismatch_generics4 verus_code! {

        #[verifier(external)]
        struct Foo<Y, X> { x: X, y: Y }

        #[verifier(external_type_specification)]
        struct ExFoo<X, Y>(Foo<Y, X>);

    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

test_verify_one_file! {
    #[test] mismatch_trait_bounds verus_code! {

        #[verifier(external)]
        struct Foo<X, Y> { x: X, y: Y }

        #[verifier(external_type_specification)]
        struct ExFoo<X: Clone, Y>(Foo<X, Y>);

    } => Err(err) => assert_vir_error_msg(err, "trait bounds should match")
}

test_verify_one_file! {
    #[test] trait_bounds_ok verus_code! {

        #[verifier(external)]
        struct Foo<X: Clone, Y> { x: X, y: Y }

        #[verifier(external_type_specification)]
        struct ExFoo<Y: Clone, X>(Foo<Y, X>);

    } => Ok(())
}

test_verify_one_file! {
    #[test] omit_default_type_param verus_code! {
        struct X { }

        #[verifier(external)]
        struct Foo<A, B = X> {
            a: A,
            b: B,
        }

        #[verifier(external_type_specification)]
        struct Bar<A>(Foo<A>);
    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

// unions unsupported

test_verify_one_file! {
    #[test] union_not_supported verus_code! {
        // MaybeUninit is a union, so unsupported right now
        #[verifier(external_type_specification)]
        struct ExFoo<X>(core::mem::MaybeUninit<X>);
    } => Err(err) => assert_vir_error_msg(err, "external_type_specification: the external type needs to be a struct or enum")
}

// if stuff is private, it needs to be marked external_body

test_verify_one_file! {
    #[test] non_pub_fields_not_supported verus_code! {
        #[verifier(external)]
        pub struct SomeStruct<T> { t: T }

        #[verifier(external_type_specification)]
        pub struct ExSomeStruct<U>(SomeStruct<U>);
    } => Err(err) => assert_vir_error_msg(err,
        "external_type_specification: private fields not supported for transparent datatypes (try 'external_body' instead?)")
}

// external_body

test_verify_one_file! {
    #[test] external_body_is_respected verus_code! {
        #[verifier(external)]
        pub struct SomeStruct<T> { t: T }

        #[verifier(external_type_specification)]
        #[verifier(external_body)]
        #[verifier(reject_recursive_types(U))]
        pub struct ExSomeStruct<U>(SomeStruct<U>);

        fn test() {
            let x = SomeStruct::<u64> { t: 5 };
        }
    } => Err(err) => assert_vir_error_msg(err, "constructor of datatype with inaccessible fields")
}

// positivity

test_verify_one_file! {
    #[test] type_recursion_is_handled verus_code! {
        #[verifier(external_type_specification)]
        #[verifier::reject_recursive_types(U)]
        pub struct ExOption<U>(core::option::Option<U>);

        struct Test {
            t: Box<core::option::Option<Test>>,
        }
    } => Err(err) => assert_vir_error_msg(err, "crate::Test recursively uses type crate::Test in a non-positive position")
}

test_verify_one_file! {
    #[test] polarity_annotation_required_external_body verus_code! {
        #[verifier(external_type_specification)]
        #[verifier(external_body)]
        pub struct ExOption<U>(core::option::Option<U>);
    } => Err(err) => assert_vir_error_msg(err, "in external_body datatype, each type parameter must be one of: #[verifier::reject_recursive_types], #[verifier::reject_recursive_types_in_ground_variants], #[verifier::accept_recursive_types]")
}

// Other

test_verify_one_file! {
    #[test] test_attr_with_external verus_code! {
        #[verifier(external)]
        #[verifier(external_type_specification)]
        struct Foo<X, Y> { x: X, y: Y }
    } => Err(err) => assert_vir_error_msg(err, "a type cannot be marked both `external_type_specification` and `external`")
}

test_verify_one_file! {
    #[test] test_apply_to_builtin verus_code! {
        #[verifier(external_type_specification)]
        pub struct Foo(int);
    } => Err(err) => assert_vir_error_msg(err, "cannot apply `external_type_specification` to Verus builtin types")
}

test_verify_one_file! {
    #[test] error_msg_use_external_type_return_position verus_code! {
        #[verifier(external)]
        struct X { }

        fn stuff() -> X {
            loop { }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type marked `external`")
}
