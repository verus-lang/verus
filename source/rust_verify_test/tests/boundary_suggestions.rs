#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests for assume_specification
test_verify_one_file! {
    #[test] test_two_assume_specification_suggestions_made code! {
        use vstd::prelude::*;

        pub fn foo() {}
        pub fn bar() {}

        verus! {
            pub fn main() {
                foo();
                bar();
            }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["bar", "foo"])
}
test_verify_one_file! {
    #[test] test_assume_specification_simple_suggestion_made code! {
        use vstd::prelude::*;

        pub fn foo() {}

        verus! {
            pub fn main() {
                foo();
            }
        }
    } => Err(err) => assert_help_error_msg(err, "pub assume_specification [crate::foo] ();")
}
test_verify_one_file! {
    #[test] test_assume_specification_simple_suggestion_correct code! {
        use vstd::prelude::*;

        pub fn foo() {}

        verus! {
            pub assume_specification [crate::foo] ();
            pub fn main() {
                foo();
            }
        }
    } => Ok(())
}
test_verify_one_file! {
    #[test] test_assume_specification_generics_suggestion_made code! {
        use vstd::prelude::*;

        pub fn foo<X, Y: Eq, Z>(x: X, y: Y) -> Z
        where Z: PartialEq,
        { panic!() }

        verus! {
            pub fn bar<X, Y: Eq, Z: PartialEq>(x: X, y: Y) {
                let z: Z = foo(x, y);
            }
        }
    } => Err(err) => assert_help_error_msg(err, "pub assume_specification<X, Y, Z> [crate::foo] (_0: X, _1: Y) -> Z
           where
           Y: std::cmp::Eq,
           Z: std::cmp::PartialEq,;")
}
test_verify_one_file! {
    #[test] test_assume_specification_generics_suggestion_correct code! {
        use vstd::prelude::*;

        pub fn foo<X, Y: Eq, Z>(x: X, y: Y) -> Z
        where Z: PartialEq,
        { panic!() }

        verus! {
            pub assume_specification<X, Y, Z> [crate::foo] (_0: X, _1: Y) -> Z
            where
            Y: std::cmp::Eq,
            Z: std::cmp::PartialEq,;
            pub fn bar<X, Y: Eq, Z: PartialEq>(x: X, y: Y) {
                let z: Z = foo(x, y);
            }
        }
    } => Ok(())
}
test_verify_one_file! {
    #[test] test_assume_specification_self_suggestion_made code! {
        use vstd::prelude::*;
        verus! {
            pub struct A { x: usize }
        }
        impl A {
            pub fn foo(&self) -> A {
                A { x: self.x + 1 }
            }
        }

        verus! {
            pub fn bar(a: A) {
                let a2 = a.foo();
            }
        }
    } => Err(err) => assert_help_error_msg(err, "pub assume_specification [crate::A::foo] (_0: &crate::A) -> crate::A;")
}
test_verify_one_file! {
    #[test] test_assume_specification_self_suggestion_correct code! {
        use vstd::prelude::*;
        verus! {
            pub struct A { x: usize }
        }
        impl A {
            pub fn foo(&self) -> A {
                A { x: self.x + 1 }
            }
        }

        verus! {
            pub assume_specification [crate::A::foo] (_0: &crate::A) -> crate::A;
            pub fn bar(a: A) {
                let a2 = a.foo();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_assume_specification_foreign_suggestion_made code! {
        use vstd::prelude::*;

        verus! {
            pub fn bar<T>(o: Option<T>)-> Option<T> {
                o.inspect(|_x: &T| {})
            }
        }
    } => Err(err) => assert_help_error_msg(err, "pub assume_specification<T, F> [std::option::Option::<T>::inspect] (_0: std::option::Option<T>, _1: F) -> std::option::Option<T>")
}
test_verify_one_file! {
    #[test] test_assume_specification_foreign_suggestion_correct code! {
        use vstd::prelude::*;

        verus! {
            #[verifier::external_trait_specification]
            pub trait ExDestruct {
                type ExternalTraitSpecificationFor: core::marker::Destruct;
            }

            pub assume_specification<T, F> [std::option::Option::<T>::inspect] (_0: std::option::Option<T>, _1: F) -> std::option::Option<T>
            where
            F: std::ops::FnOnce(&T,) -> () + core::marker::Destruct,;

            pub fn bar<T>(o: Option<T>)-> Option<T> {
                o.inspect(|_x: &T| {})
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_assume_specification_str_eq_suggestion_made code! {
        use vstd::prelude::*;

        verus! {
            fn foo(x: &str, y: &str) -> (res: bool)
            {
                x == y
            }
        }
    } => Err(err) => assert_help_error_msg(err, "pub assume_specification<'a, 'b, A, B> [<&'b A as std::cmp::PartialEq<&B>>::eq] (_0: &&'b A, _1: &&B) -> bool
           where
           A: std::cmp::PartialEq<B> + ?Sized,
           B: ?Sized,;")
}
test_verify_one_file! {
    #[test] test_assume_specification_str_eq_suggestion_correct code! {
        use vstd::prelude::*;

        verus! {
            pub assume_specification<'a, 'b, A, B> [<&'b A as std::cmp::PartialEq<&B>>::eq] (_0: &&'b A, _1: &&B) -> bool
            where
            A: std::cmp::PartialEq<B> + core::marker::PointeeSized,
            B: core::marker::PointeeSized,;


            fn foo(x: &str, y: &str) -> (res: bool)
            {
                x == y
            }
        }
    } => Ok(())
}
test_verify_one_file! {
    #[test] test_assume_specification_format_visibility code! {
        use vstd::prelude::*;

        verus! {
            fn foo(x: &str, y: &str) -> (res: String)
            {
                format!("{}_{}", x, y)
            }
        }
    } => Err(err) => assert_help_error_msgs(err, &["assume_specification", "assume_specification"])
}
test_verify_one_file! {
    #[test] test_assume_specification_const_generics_suggestion_made code! {
        use vstd::prelude::*;
        fn foo<A, const N: usize, const M: usize>(inputs: &[A; N]) -> [A; M] {
            panic!()
        }
        verus! {
            pub fn bar<A>(inputs: &[A; 1]) {
                let a = foo::<A, 1, 2>(inputs);
            }
        }
    } => Err(err) => assert_help_error_msg(err, "assume_specification<A, const N: usize, const M: usize> [crate::foo] (_0: &[A; N]) -> [A; M];")
}
test_verify_one_file! {
    #[test] test_assume_specification_const_generics_suggestion_correct code! {
        use vstd::prelude::*;
        fn foo<A, const N: usize, const M: usize>(inputs: &[A; N]) -> [A; M] {
            panic!()
        }
        verus! {
            assume_specification<A, const N: usize, const M: usize> [crate::foo] (_0: &[A; N]) -> [A; M];
            pub fn bar<A>(inputs: &[A; 1]) {
                let a = foo::<A, 1, 2>(inputs);
            }
        }
    } => Ok(())
}
test_verify_one_file! {
    #[test] test_assume_specification_region_outlives_suggestion_made code! {
        fn foo<'a, 'b, 'c, A, B>(a: &'a A, b: &'b B) -> &'c A
        where 'c: 'a + 'b {
            panic!()
        }
        verus! {
            pub fn bar<'a, 'b, 'c, A, B>(a: &'a A, b: &'b B) -> &'c A {
                foo(a, b)
            }
        }
    } => Err(e) => assert_help_error_msg(e, "assume_specification<'a, 'b, 'c, A, B> [crate::foo] (_0: &'a A, _1: &'b B) -> &'c A
           where
           'c: 'a + 'b,;")
}
test_verify_one_file! {
    #[test] test_assume_specification_region_outlives_correct code! {
        fn foo<'a, 'b, 'c, A, B>(a: &'a A, b: &'b B) -> &'c A
        where 'c: 'a + 'b {
            panic!()
        }
        verus! {
            assume_specification<'a, 'b, 'c, A, B> [crate::foo] (_0: &'a A, _1: &'b B) -> &'c A
            where
            'c: 'a + 'b,;
            pub fn bar<'a, 'b, 'c, A, B>(a: &'a A, b: &'b B) -> &'c A {
                foo(a, b)
            }
        }
    } => Ok(())
}

// Tests for external_type_specification
test_verify_one_file! {
    #[test] error_msg_two_external_types verus_code! {
        #[verifier(external)]
        struct X { }

        #[verifier(external)]
        struct Y { }

        #[verifier::external_body]
        fn stuff(y: Y) -> X {
            panic!()
        }
    } => Err(err) => assert_help_error_msgs(err, &["cannot use type `crate::X` which is ignored", "cannot use type `crate::Y` which is ignored"])
}

// These two together form a 'smoke test' that the suggestions provided are correct.
// A more elegant strategy might be to extract the suggestion from the error message and
// put that directly into the code! macro.
test_verify_one_file! {
    #[test] two_external_type_suggestions code! {
        struct X { }

        pub struct Y { }

        verus!{
            #[verifier::external_body]
            fn stuff(y: Y) -> X {
                X {}
            }
        }
    } => Err(err) => assert_help_error_msgs(err, &["#[verifier::external_type_specification]
           struct ExX(crate::X);", "#[verifier::external_type_specification]
           pub struct ExY(crate::Y);"])
}
test_verify_one_file! {
    #[test] two_external_type_suggestions_are_correct code! {
        struct X { }
        pub struct Y { }

        verus!{
            #[verifier::external_type_specification]
            struct ExX(crate::X);

            #[verifier::external_type_specification]
            pub struct ExY(crate::Y);

            fn stuff(y: Y) -> X {
                X {}
            }
        }
    } => Ok(())
}
test_verify_one_file! {
    #[test] external_type_generics_suggestion_made code! {
        // Using view here because Add, etc caused lifetime errors and ill-typed AIR
        use vstd::prelude::*;
        verus! {
            trait T { }
        }
        struct X<'a, 'b, A: View + T ,B,C: View<V = A>, const N: usize>
            where B: View<V = C> + T{
            a: A,
            b: &'b B,
            c: C,
            l1: &'a std::marker::PhantomData<A>,
        }

        verus! {
            fn stuff<'a, 'b, A: View + T, B, C: View<V = A>, const N: usize>(x: X<'a, 'b, A, B, C, N>) -> X<'a, 'b, A, B, C, N>
            where B: View<V = C> + T{
                x
            }
        }
    } => Err(err) => assert_help_error_msg(err,
"#[verifier::reject_recursive_types(A)]
           #[verifier::reject_recursive_types(B)]
           #[verifier::reject_recursive_types(C)]
           #[verifier::external_type_specification]
           struct ExX<'a, 'b, A, B, C, const N: usize>(crate::X<'a, 'b, A, B, C, N>)
           where
           A: vstd::string::View + crate::T,
           B: vstd::string::View<V = C> + crate::T,
           C: vstd::string::View<V = A>,;")
}
// TODO: Test generic params not in lexographical order
test_verify_one_file! {
    #[test] external_type_generics_suggestion_correct code! {
        // Using view here because Add, etc caused lifetime errors and ill-typed AIR
        use vstd::prelude::*;
        verus! {
            trait T { }
        }
        struct X<'a, 'b, A: View + T , B, C: View<V = A>, const N: usize>
            where B: View<V = C> + T{
            a: A,
            b: &'b B,
            c: C,
            l1: &'a std::marker::PhantomData<A>,
        }

        verus! {
            #[verifier::reject_recursive_types(A)]
            #[verifier::reject_recursive_types(B)]
            #[verifier::reject_recursive_types(C)]
            #[verifier::external_type_specification]
            struct ExX<'a, 'b, A, B, C, const N: usize>(crate::X<'a, 'b, A, B, C, N>)
            where
            A: vstd::string::View + crate::T,
            B: vstd::string::View<V = C> + crate::T,
            C: vstd::string::View<V = A>,;

            fn stuff<'a, 'b, A: View + T, B, C: View<V = A>, const N: usize>(x: X<'a, 'b, A, B, C, N>) -> X<'a, 'b, A, B, C, N>
            where B: View<V = C> + T{
                x
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] external_type_assoc_type_suggestion_made code! {
        use vstd::prelude::*;
        verus! {
            trait T {
                type AssocT;
             }
        }
        struct X<'a, 'b, A: View + T ,B,C: View<V = A>, const N: usize>
            where B: View<V = C> + T,
            A::AssocT: View<V = A>,
            B::AssocT: 'b,
            {
            a: A,
            b: B,
            c: &'b C,
            l1: &'a std::marker::PhantomData<A>,
        }
        verus! {
            fn stuff<'a, 'b, A: View + T, B, C: View<V = A>, const N: usize>(x: X<'a, 'b, A, B, C, N>) -> X<'a, 'b, A, B, C, N>
            where B: View<V = C> + T,
            B::AssocT: 'b,
            A::AssocT: View<V = A>{
                x
            }
        }
    } => Err(e) => assert_help_error_msg(e, "#[verifier::reject_recursive_types(A)]
           #[verifier::reject_recursive_types(B)]
           #[verifier::reject_recursive_types(C)]
           #[verifier::external_type_specification]
           struct ExX<'a, 'b, A, B, C, const N: usize>(crate::X<'a, 'b, A, B, C, N>)
           where
           <A as T>::AssocT: vstd::string::View<V = A>,
           A: vstd::string::View + crate::T,
           B: vstd::string::View<V = C> + crate::T,
           C: vstd::string::View<V = A>,;")
}

test_verify_one_file! {
    #[test] external_type_assoc_type_suggestion_correct code! {
        use vstd::prelude::*;
        verus! {
            trait T {
                type AssocT;
             }
        }
        struct X<'a, 'b, A: View + T ,B,C: View<V = A>, const N: usize>
            where B: View<V = C> + T,
            A::AssocT: View<V = A>,
            B::AssocT: 'b,
            {
            a: A,
            b: B,
            c: &'b C,
            l1: &'a std::marker::PhantomData<A>,
        }
        verus! {
            #[verifier::reject_recursive_types(A)]
            #[verifier::reject_recursive_types(B)]
            #[verifier::reject_recursive_types(C)]
            #[verifier::external_type_specification]
            struct ExX<'a, 'b, A, B, C, const N: usize>(crate::X<'a, 'b, A, B, C, N>)
                where
                <A as T>::AssocT: vstd::string::View<V = A>,
                A: vstd::string::View + crate::T,
                B: vstd::string::View<V = C> + crate::T,
                C: vstd::string::View<V = A>,;

            fn stuff<'a, 'b, A: View + T, B, C: View<V = A>, const N: usize>(x: X<'a, 'b, A, B, C, N>) -> X<'a, 'b, A, B, C, N>
            where B: View<V = C> + T,
            B::AssocT: 'b,
            A::AssocT: View<V = A>{
                x
            }
        }
    } => Ok(())
}
