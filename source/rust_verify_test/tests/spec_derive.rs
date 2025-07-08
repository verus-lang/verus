#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Negative tests for spec_derive macros
// These tests verify that the macros properly reject unsupported features
// and provide helpful error messages.

// Test 1: Union types are not supported
test_verify_one_file! {
    #[test] test_union_not_supported (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub union TestUnion { // FAILS
            field1: u32,
            field2: f32,
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 2: Generic type parameters are not supported (based on validate_input function)
test_verify_one_file! {
    #[test] test_generic_type_params_not_supported (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub struct GenericStruct<T> { // FAILS - generic type parameters not supported
            pub data: T,
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 3: Self-referential types are not supported
test_verify_one_file! {
    #[test] test_self_referential_not_supported (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub struct SelfRef { // FAILS - self-referential
            pub value: u32,
            pub next: Option<SelfRef>,
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 4: Wrong attribute name - using 'skip' instead of 'exclude'
test_verify_one_file! {
    #[test] test_wrong_attribute_name (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type(skip(y))] // FAILS - 'skip' not recognized
        pub struct TestStruct {
            pub x: u32,
            pub y: String,
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 5: Applying make_spec_type to a function (should fail)
test_verify_one_file! {
    #[test] test_macro_on_function (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub fn test_function() -> u32 { // FAILS - not a struct or enum
            42
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 6: Applying make_spec_type to a trait (should fail)
test_verify_one_file! {
    #[test] test_macro_on_trait (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub trait TestTrait { // FAILS - not a struct or enum
            fn test_method(&self) -> u32;
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 7: self_view with attributes (not supported - takes no parameters)
test_verify_one_file! {
    #[test] test_self_view_with_attributes (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[self_view(some_attribute)] // FAILS - self_view takes no parameters
        pub struct TestStruct {
            pub x: u32,
            pub y: String,
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 8: Macro on module (should fail)
test_verify_one_file! {
    #[test] test_macro_on_module (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub mod test_module { // FAILS - not a struct or enum
            pub struct InnerStruct {
                pub x: u32,
            }
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 9: Types that don't implement DeepView (should fail at verification)
test_verify_one_file! {
    #[test] test_missing_deep_view_trait (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        // Custom type that doesn't implement DeepView
        pub struct CustomType {
            value: u32,
        }

        #[make_spec_type]
        pub struct TestStruct {
            pub custom: CustomType, // FAILS - CustomType doesn't implement DeepView
        }
    }).to_string() => Err(e) => assert_rust_error_msg_all(e, "CustomType")
}

// Test 10: Excluding non-existent fields should fail
test_verify_one_file! {
    #[test] test_exclude_nonexistent_field_fails (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type(exclude(nonexistent_field))]
        pub struct TestStruct {
            pub x: u32,
            pub y: String,
        }
    }).to_string() => Err(e) => {
        let errors = e.errors;
        assert!(errors.len() == 1);
        assert!(errors[0].message.contains("Field 'nonexistent_field' does not exist and cannot be excluded"))
    }
}

// POSITIVE TESTS (these should work based on the implementation)

// Test 11: Excluding all fields from a struct should work
test_verify_one_file! {
    #[test] test_exclude_all_fields_works (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type(exclude(x, y))]
        pub struct TestStruct {
            pub x: u32,
            pub y: String,
        }

        verus! {
        fn test_exclude_all() {
            let s = TestStruct { x: 1, y: "test".to_string() };
            let ghost _spec = s.deep_view(); // Should create empty spec struct
        }
        }
    }).to_string() => Ok(())
}

// Test 12: Lifetimes are supported (not generic type parameters)
test_verify_one_file! {
    #[test] test_lifetimes_supported (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub struct LifetimeStruct<'a> {
            pub data: &'a str,
        }

        verus! {
        fn test_lifetimes() {
            let s = LifetimeStruct { data: "test" };
            let ghost _spec = s.deep_view(); // Should work - lifetimes are supported
        }
        }
    }).to_string() => Ok(())
}

// Test 13: Self-referential types don't work even with Box
test_verify_one_file! {
    #[test] test_recursive_with_box_works (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub struct RecursiveStruct {
            pub value: u32,
            pub next: Option<Box<RecursiveStruct>>, // FAILS - self-referential types don't work
        }
    }).to_string() => Err(e) => assert_one_fails(e)
}

// Test 14: self_view on Copy types should work
test_verify_one_file! {
    #[test] test_self_view_copy_works (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[derive(Copy, Clone)]
        #[self_view]
        pub struct CopyStruct {
            pub x: u32,
            pub y: i32,
        }

        verus! {
        fn test_self_view_copy() {
            let s = CopyStruct { x: 1, y: 2 };
            let ghost _view = s.deep_view(); // Should work - Copy types work with *self
        }
        }
    }).to_string() => Ok(())
}

// Test 15: Basic struct with make_spec_type (no exclude)
test_verify_one_file! {
    #[test] test_basic_struct_make_spec_type (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub struct TestStruct1 {
            pub x: u32,
            pub y: String,
        }

        verus! {
        fn test_make_spec_type_struct_no_exclude() {
            let original = TestStruct1 { x: 10, y: "hello".to_string() };
            assert(original@ == TestStruct1Spec { x: 10, y: "hello"@ });
        }
        }
    }).to_string() => Ok(())
}

// Test 16: Complex struct with exclude and lifetimes
test_verify_one_file! {
    #[test] test_complex_struct_with_exclude_and_lifetimes (code_str! {
        use builtin_macros::*;
        use std::collections::HashMap;
        use vstd::prelude::*;

        #[make_spec_type]
        pub enum TestEnum1<'a> {
            UnitVariant,
            TupleVariant(u32, String),
            StructVariant {
                a: u32,
                b: Vec<String>,
            },
            ComplicatedVariant {
                v: &'a Vec<(i32, &'a String)>,
                w: &'a [&'a [TestEnum2]],
            },
        }

        #[self_view]
        pub enum TestEnum2 {
            Variant,
        }

        #[make_spec_type(exclude(y))]
        pub struct TestStruct2<'a> {
            pub x: u32,
            pub y: String,
            pub z: Vec<u8>,
            pub t: &'a i32,
            pub v: &'a Vec<(i32, &'a Vec<String>)>,
            pub w: &'a [&'a [TestEnum1<'a>]],
            pub u: HashMap<&'a str, &'a str>,
        }

        verus! {
        fn test_make_spec_type_struct_with_exclude() {
            let v = vec![1, 2, 3];
            let original = TestStruct2 {
                x: 42,
                y: "excluded".to_string(),
                z: v,
                t: &1,
                v: &vec![(1, &vec!["2".to_string()])],
                w: &[&[TestEnum1::UnitVariant]],
                u: HashMap::new()
            };
            assert(v.deep_view() == seq![1u8, 2u8, 3u8]);
            let ghost spec = TestStruct2Spec {
                x: 42,
                z: seq![1, 2, 3],
                t: 1,
                v: seq![(1, seq!["2"@])],
                w: seq![seq![TestEnum1Spec::UnitVariant]],
                u: map![],
            };
            assert(original.x@ == spec.x);
            assert(original.z.deep_view() == spec.z);
            assert(original.t@ == spec.t);
            assert(original.v.deep_view()[0].0 == 1);
            assert(original.v.deep_view()[0].1 == seq!["2"@]);
            assert(original.v.deep_view() == spec.v);
            assert(original.w.deep_view()[0] == seq![TestEnum1Spec::UnitVariant]);
            assert(original.w.deep_view() == spec.w);
        }

        pub proof fn test_strip_refs<'a>(x: TestStruct2<'a>) -> TestStruct2Spec {
            assert(x@ == TestStruct2Spec {
                x: x.x@,
                z: x.z.deep_view(),
                t: x.t.deep_view(),
                v: x.v.deep_view(),
                w: x.w.deep_view(),
                u: x.u.deep_view(),
            });
            x@
        }
        }
    }).to_string() => Ok(())
}

// Test 19: Enum with make_spec_type - variant testing
test_verify_one_file! {
    #[test] test_enum_make_spec_type_comprehensive (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[make_spec_type]
        pub enum TestEnum2 {
            StructVariant1 { a: u32, b: Vec<u8>, c: String },
            StructVariant2 { a: u32, b: Vec<u8> },
        }

        #[make_spec_type]
        pub enum TestEnum1<'a> {
            UnitVariant,
            TupleVariant(u32, String),
            StructVariant {
                a: u32,
                b: Vec<String>,
            },
            ComplicatedVariant {
                v: &'a Vec<(i32, &'a String)>,
                w: &'a [&'a [TestEnum2]],
            },
        }

        verus! {
        fn test_make_spec_type_enum() {
            let original_unit = TestEnum1::UnitVariant;
            assert(original_unit@ matches TestEnum1Spec::UnitVariant);

            let original_tuple = TestEnum1::TupleVariant(123, "test".to_string());
            assert(original_tuple@ == TestEnum1Spec::TupleVariant(123, "test"@));

            let b = vec!["a".to_string(), "b".to_string(), "c".to_string()];
            let original_struct = TestEnum1::StructVariant { a: 7, b };
            assert(b.deep_view() == seq!["a"@, "b"@, "c"@]);
            assert(original_struct@ == TestEnum1Spec::StructVariant { a: 7, b: seq!["a"@, "b"@, "c"@] });
            assert(original_struct@ == original_struct.deep_view());
        }
        }
    }).to_string() => Ok(())
}

// Test 21: self_view on enum
test_verify_one_file! {
    #[test] test_self_view_enum_comprehensive (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[self_view]
        enum SelfViewEnum {
            A,
            B(u32),
            C { x: i32, y: i32 },
        }

        verus! {
        fn test_self_view_enum_macro() {
            let value_a = SelfViewEnum::A;
            assert(value_a@ == value_a && value_a.deep_view() == value_a);

            let value_b = SelfViewEnum::B(123);
            assert(value_b@ == value_b && value_b.deep_view() == value_b);

            let value_c = SelfViewEnum::C { x: 1, y: 2 };
            assert(value_c@ == value_c && value_c.deep_view() == value_c);
        }
        }
    }).to_string() => Ok(())
}

// Test 22: self_view on struct with complex types
test_verify_one_file! {
    #[test] test_self_view_struct_comprehensive (code_str! {
        use builtin_macros::*;
        use vstd::prelude::*;

        #[self_view]
        struct SelfViewStruct {
            x: u32,
            y: String,
            z: Vec<u8>,
        }

        verus! {
        fn test_self_view_struct_macro() {
            let original = SelfViewStruct { x: 10, y: "hello".to_string(), z: vec![1, 2, 3] };
            assert(original@ == original && original.deep_view() == original);
        }
        }
    }).to_string() => Ok(())
}
