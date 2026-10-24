#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_opaque_return_followed_by_spec_and_proof verus_code! {
        use vstd::prelude::*;

        trait Marker { }
        impl Marker for bool { }

        fn opaque_return() -> impl Marker {
            true
        }

        spec fn ordinary_spec() -> bool {
            true
        }

        proof fn ordinary_proof()
            ensures ordinary_spec(),
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{}
        impl DummyTrait for bool{}
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type_hides_real_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{}
        impl DummyTrait for bool{}
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            assert(x);
        }
    } => Err(err) => assert_rust_error_msg_all(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test_return_opaque_type_allows_trait_functions verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
        }
        impl DummyTrait for bool{
            fn foo(&self) -> (ret: bool)
            {
                false
            }
        }
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            let ret = x.foo();
            assert(ret == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type_reveal_real_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
            fn get_output(&self) -> (ret : Self::Output);
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            fn get_output(&self) -> (ret : Self::Output){
                *self
            }
        }
        fn return_opaque_variable() -> impl DummyTrait<Output = bool>{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            let output = x.get_output();
            // Here Verus should be able to infer the type of output, but assertion should fail
            assert(output);  // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_no_opaque_types_from_traits verus_code! {
    use vstd::prelude::*;
    trait DummyTraitA{}
    impl<T> DummyTraitA for T {}
    trait DummyTraitB {
        fn foo(&self) -> impl DummyTraitA;
    }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not yet support Opaque types in trait def")
}

test_verify_one_file! {
    #[test] test_opaque_function_with_ensures verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{}
        impl<T> DummyTraitA for T {}
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret
        {
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_function_return_value_type verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{}
        impl<T> DummyTraitA for T {}
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret == true,
        {
            true
        }
    } => Err(err) => assert_rust_error_msg(err, "the trait bound")
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_without_annotation  verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{
            type Output;
            spec fn get_output(&self) -> Self::Output;
        }
        impl<T> DummyTraitA for T {
            type Output = T;
            uninterp spec fn get_output(&self) -> Self::Output;
        }
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret.get_output() == true,
        {
            true
        }
    } => Err(err) => assert_rust_error_msg(err, "the trait bound")
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_with_annotation verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{
            type Output;
            spec fn get_output(&self) -> Self::Output;
        }
        impl<T> DummyTraitA for T {
            type Output = T;
            uninterp spec fn get_output(&self) -> Self::Output;
        }
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret.get_output() == true,  // FAILS
        {
            true
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_opaque_type_external_body_function verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool {
                true
            }
        }

        #[verifier::external_body]
        fn return_opaque_variable() -> (ret: impl DummyTrait)
            ensures
                ret.bar() == false,
        {
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
        {
            x
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T) -> (ret: impl DummyTrait<Output = T>)
            ensures ret.bar();
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_tuple_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T, y:T) -> (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>)
        {
            (x, y)
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T, y:T) -> (ret: (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>))
            ensures ret.0.bar();
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_assume_spec_fail verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
        {
            x
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T) -> (ret: impl DummyTrait)
            ensures ret.bar();
    }  => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
         trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
            spec fn get_self(&self) -> Self::Output;
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }

            spec fn get_self(&self) -> Self::Output{
                *self
            }
        }
        #[verifier::external]
        fn return_opaque_variable() -> impl DummyTrait<Output = impl DummyTrait>
        {
            true
        }
        assume_specification [ return_opaque_variable ]() -> (ret: impl DummyTrait<Output = impl DummyTrait>)
            ensures ret.get_self().bar()
            ;

        fn test(){
            let ret = return_opaque_variable();
            assert(ret.get_self().bar());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_assume_spec_fail verus_code! {
        use vstd::prelude::*;
         trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
            spec fn get_self(&self) -> Self::Output;
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }

            spec fn get_self(&self) -> Self::Output{
                *self
            }
        }
        #[verifier::external]
        fn return_opaque_variable() -> impl DummyTrait<Output = impl DummyTrait<Output = bool>>
        {
            true
        }
        assume_specification [ return_opaque_variable ]() -> (ret: impl DummyTrait<Output = impl DummyTrait>)
            ensures ret.get_self().bar()
            ;
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] test_opaque_type_returns_error verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
            returns x
        {
            x
        }
    }  => Err(err) => assert_vir_error_msg(err, "`returns` clause is not allowed for function that returns opaque type")
}

test_verify_one_file! {
    #[test] test_tuple_of_opaque_types_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn foo() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            (true, true)
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_from_opaque_type_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn foo() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            (true, true)
        }
        fn bar() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            foo()
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_fail verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }
        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = impl Tr<T = bool>>)
            ensures
                // ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(), // FAILS
        {
            boo()
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_ok verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }

        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            boo()
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_inherent_ok verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }

        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = bool>)
            ensures
                // ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            boo()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // Regression test for ensuring opaque type constructor context is present
    // in spinoff queries. -V spinoff-all verifies every function in its own context.
    #[test] opaque_type_in_spinoff_context ["-V spinoff-all"] => verus_code! {
        trait DummyTrait {}
        impl DummyTrait for bool {}
        fn return_opaque() -> impl DummyTrait {
            true
        }
        fn test() {
            let x = return_opaque();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] issue2541 ["--no-lifetime"] => code! {
        use std::future::Future;
        #[allow(unused_imports)]
        use vstd::prelude::*;

        pub trait F<T> {
            fn f(x: &T) -> impl Future + Send;
        }

        struct E;
        struct S;

        #[allow(refining_impl_trait)]
        impl F<E> for S {
            async fn f(_x: &E) {}
        }

        fn main() {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] opaque_type_spec_fn verus_code! {
        struct X { }
        trait Tr { }
        impl Tr for X { }

        spec fn foo() -> impl Tr {
            X{}
        }
    } => Err(err) => assert_vir_error_msg(err, "impl trait in return position is only supported for 'exec' functions")
}

test_verify_one_file! {
    #[test] opaque_type_proof_fn verus_code! {
        struct X { }
        trait Tr { }
        impl Tr for X { }

        proof fn foo() -> Option<impl Tr> {
            Some(X{})
        }
    } => Err(err) => assert_vir_error_msg(err, "impl trait in return position is only supported for 'exec' functions")
}

test_verify_one_file! {
    #[test] opaque_type_when_used_as_spec verus_code! {
        struct X { }
        trait Tr { }
        impl Tr for X { }

        spec fn foo2() -> X {
            X{}
        }

        #[verifier::when_used_as_spec(foo2)]
        fn foo() -> impl Tr {
            X{}
        }
    } => Err(err) => assert_vir_error_msg(err, "impl trait in return position is not supported together with `when_used_as_spec`")
}

test_verify_one_file! {
    // g's nested opaque type must be instantiated with g's type args (u8), not with f's T
    #[test] test_nested_opaque_type_args_fail verus_code! {
        use vstd::prelude::*;

        pub trait K { spec fn k() -> int; }
        impl K for u8 { open spec fn k() -> int { 0 } }
        impl K for u16 { open spec fn k() -> int { 1 } }

        pub trait Tr { type X; }
        pub trait Tr2 { type Y; }
        pub struct W<A>(pub A);
        impl<A> Tr for W<A> { type X = W<A>; }
        impl<A> Tr2 for W<A> { type Y = A; }

        fn g<T>(t: T) -> impl Tr<X = impl Tr2<Y = T>> { W(t) }

        fn f<T: K>(x: u8) -> impl Tr<X = impl Tr2<Y = u8>>
            ensures T::k() == u8::k() // FAILS
        {
            g::<u8>(x)
        }

        fn test() {
            f::<u16>(0);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_args_renamed_fail verus_code! {
        use vstd::prelude::*;

        pub trait K { spec fn k() -> int; }
        impl K for u8 { open spec fn k() -> int { 0 } }
        impl K for u16 { open spec fn k() -> int { 1 } }

        pub trait Tr { type X; }
        pub trait Tr2 { type Y; }
        pub struct W<A>(pub A);
        impl<A> Tr for W<A> { type X = W<A>; }
        impl<A> Tr2 for W<A> { type Y = A; }

        fn g<Q>(t: Q) -> impl Tr<X = impl Tr2<Y = Q>> { W(t) }

        fn f<T: K>(x: u8) -> impl Tr<X = impl Tr2<Y = u8>>
            ensures T::k() == u8::k() // FAILS
        {
            g::<u8>(x)
        }

        fn test() {
            f::<u16>(0);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_args_ok verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; spec fn sx(&self) -> Self::X; }
        pub trait Tr2 { type Y; spec fn sy(&self) -> Self::Y; spec fn good(&self) -> bool; }
        pub struct W<A>(pub A);
        impl<A> Tr for W<A> { type X = W<A>; open spec fn sx(&self) -> W<A> { W(self.0) } }
        impl<A> Tr2 for W<A> {
            type Y = A;
            open spec fn sy(&self) -> A { self.0 }
            open spec fn good(&self) -> bool { true }
        }

        fn g<Q>(t: Q) -> (r: impl Tr<X = impl Tr2<Y = Q>>)
            ensures r.sx().good()
        {
            W(t)
        }

        fn f<T>(x: T) -> (r: impl Tr<X = impl Tr2<Y = T>>)
            ensures r.sx().good()
        {
            g::<T>(x)
        }

        fn h(x: u8) -> (r: impl Tr<X = impl Tr2<Y = u8>>)
            ensures r.sx().good()
        {
            g::<u8>(x)
        }

        fn test() {
            let r = h(0);
            assert(r.sx().good());
        }
    } => Ok(())
}

test_verify_one_file! {
    // the same trait appears twice with different trait args, in opposite order in f and g
    #[test] test_nested_opaque_type_trait_args_fail verus_code! {
        use vstd::prelude::*;

        pub trait K { spec fn k() -> int; }
        impl K for u8 { open spec fn k() -> int { 0 } }
        impl K for u16 { open spec fn k() -> int { 1 } }

        pub trait Tr<P> { type X; }
        pub trait Tr2 { type Y; }
        pub struct W<A>(pub A);
        pub struct V<A, B>(pub A, pub B);
        impl<A> Tr2 for W<A> { type Y = A; }
        impl<A, B> Tr<u8> for V<A, B> { type X = W<A>; }
        impl<A, B> Tr<u16> for V<A, B> { type X = W<B>; }

        fn g<T>(t: T) -> impl Tr<u8, X = impl Tr2<Y = u8>> + Tr<u16, X = impl Tr2<Y = T>> {
            V(0u8, t)
        }

        fn f<T: K>(t: T) -> impl Tr<u16, X = impl Tr2<Y = T>> + Tr<u8, X = impl Tr2<Y = u8>>
            ensures T::k() == u8::k() // FAILS
        {
            g::<T>(t)
        }

        fn test() {
            f::<u16>(0);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_trait_args_ok verus_code! {
        use vstd::prelude::*;

        pub trait Tr<P> { type X; spec fn sx(&self) -> Self::X; }
        pub trait Tr2 { type Y; spec fn good(&self) -> bool; }
        pub struct W<A>(pub A);
        pub struct V<A, B>(pub A, pub B);
        impl<A> Tr2 for W<A> { type Y = A; open spec fn good(&self) -> bool { true } }
        impl<A, B> Tr<u8> for V<A, B> { type X = W<A>; open spec fn sx(&self) -> W<A> { W(self.0) } }
        impl<A, B> Tr<u16> for V<A, B> { type X = W<B>; open spec fn sx(&self) -> W<B> { W(self.1) } }

        fn g<T>(t: T) -> (r: impl Tr<u8, X = impl Tr2<Y = u8>> + Tr<u16, X = impl Tr2<Y = T>>)
            ensures
                <_ as Tr<u8>>::sx(&r).good(),
                <_ as Tr<u16>>::sx(&r).good(),
        {
            V(0u8, t)
        }

        fn f<T>(t: T) -> (r: impl Tr<u16, X = impl Tr2<Y = T>> + Tr<u8, X = impl Tr2<Y = u8>>)
            ensures
                <_ as Tr<u8>>::sx(&r).good(),
                <_ as Tr<u16>>::sx(&r).good(),
        {
            g::<T>(t)
        }

        fn test() {
            let r = f::<u32>(0);
            assert(<_ as Tr<u8>>::sx(&r).good());
            assert(<_ as Tr<u16>>::sx(&r).good());
        }
    } => Ok(())
}

// https://github.com/verus-lang/verus/issues/3014

test_verify_one_file! {
    #[test] test_issue3014_const_ptr_cast_fail verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn to_const_ptr(c: *mut u64) -> (ret: impl Tr)
            ensures ret.is_mut() // FAILS
        {
            c as *const u64
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_issue3014_const_ptr_cast_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn to_const_ptr(c: *mut u64) -> (ret: impl Tr)
            ensures !ret.is_mut()
        {
            c as *const u64
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_issue3014_const_ptr_coercion_fail verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn to_const_ptr(c: *mut u64) -> (ret: impl Tr)
            ensures ret.is_mut() // FAILS
        {
            let p: *const u64 = c;
            p
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_issue3014_const_ptr_coercion_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn to_const_ptr(c: *mut u64) -> (ret: impl Tr)
            ensures !ret.is_mut()
        {
            let p: *const u64 = c;
            p
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_issue3014_field_fail verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_x(&self) -> bool; }
        struct X { i: i64 }
        impl Tr for X { spec fn is_x(&self) -> bool { true } }
        impl Tr for i64 { spec fn is_x(&self) -> bool { false } }

        fn to_field(x: X) -> (ret: impl Tr)
            ensures ret.is_x() // FAILS
        {
            x.i
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_issue3014_field_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_x(&self) -> bool; }
        struct X { i: i64 }
        impl Tr for X { spec fn is_x(&self) -> bool { true } }
        impl Tr for i64 { spec fn is_x(&self) -> bool { false } }

        fn to_field(x: X) -> (ret: impl Tr)
            ensures !ret.is_x()
        {
            x.i
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_issue3014_array_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn valid(&self) -> bool; }
        impl Tr for u64 { spec fn valid(&self) -> bool { true } }

        fn make() -> (ret: [impl Tr; 1])
            ensures ret[0].valid()
        {
            [0u64]
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_issue3014_array_fail verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn valid(&self) -> bool; }
        impl Tr for u64 { spec fn valid(&self) -> bool { true } }

        fn make() -> (ret: [impl Tr; 1])
            ensures !ret[0].valid() // FAILS
        {
            [0u64]
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_opaque_type_early_return_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn good(&self) -> bool; }
        struct X { i: u64 }
        impl Tr for X { spec fn good(&self) -> bool { true } }

        fn f(b: bool, x: X, y: X) -> (r: impl Tr)
            ensures r.good()
        {
            if b {
                return x;
            }
            y
        }

        fn g(x: X) -> (r: impl Tr)
            ensures r.good()
        {
            let mut i: u64 = 0;
            while i < 10
                invariant i <= 10,
                decreases 10 - i,
            {
                if i == 5 {
                    return x;
                }
                i = i + 1;
            }
            x
        }

        fn h(x: X) -> (r: impl Tr)
            ensures r.good()
        {
            let mut i: u64 = 0;
            loop
                invariant i <= 10,
                decreases 10 - i,
            {
                if i >= 5 {
                    return x;
                }
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // the return inside the loop body is checked in a separate query
    #[test] test_opaque_type_early_return_fail verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn g(c: *mut u64) -> (r: impl Tr)
            ensures r.is_mut() // FAILS
        {
            let p: *const u64 = c;
            let mut i: u64 = 0;
            while i < 10
                invariant i <= 10,
                decreases 10 - i,
            {
                if i == 5 {
                    return p; // FAILS
                }
                i = i + 1;
            }
            p
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_opaque_type_async_early_return_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        async fn f(b: bool, c: *mut u64) -> (ret: impl Tr)
            ensures !ret.is_mut()
        {
            if b {
                return c as *const u64;
            }
            return c as *const u64;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_async_early_return_fail verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        async fn f(b: bool, c: *mut u64) -> (ret: impl Tr)
            ensures ret.is_mut()
        {
            if b {
                return c as *const u64; // FAILS
            }
            return c as *const u64; // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_opaque_type_generic_hidden_type_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn good(&self) -> bool; }
        struct W<T>(T);
        impl<T> Tr for W<T> { spec fn good(&self) -> bool { true } }

        fn f<T>(t: T) -> (r: impl Tr)
            ensures r.good()
        {
            W(t)
        }

        fn test() {
            let r = f::<u8>(0);
            assert(r.good());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_tuple_const_ptr_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn f(c: *mut u64) -> (r: (impl Tr, u8))
            ensures !r.0.is_mut()
        {
            (c as *const u64, 0u8)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_tuple_const_ptr_fail verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn is_mut(&self) -> bool; }
        impl Tr for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl Tr for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn f(c: *mut u64) -> (r: (impl Tr, u8))
            ensures r.0.is_mut() // FAILS
        {
            (c as *const u64, 0u8)
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_opaque_type_ref_in_tuple_ok verus_code! {
        use vstd::prelude::*;
        trait Tr { spec fn good(&self) -> bool; }
        struct X { i: u64 }
        impl Tr for X { spec fn good(&self) -> bool { true } }

        fn f<'a>(x: &'a X) -> (r: (&'a impl Tr, u8))
            ensures r.0.good()
        {
            (x, 0u8)
        }

        trait TrP { spec fn is_mut(&self) -> bool; }
        impl TrP for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl TrP for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn g<'a>(c: &'a *mut u64) -> (r: (&'a impl TrP, u8))
            ensures r.0.is_mut()
        {
            (c, 0u8)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_ref_in_tuple_fail verus_code! {
        use vstd::prelude::*;
        trait TrP { spec fn is_mut(&self) -> bool; }
        impl TrP for *mut u64 { spec fn is_mut(&self) -> bool { true } }
        impl TrP for *const u64 { spec fn is_mut(&self) -> bool { false } }

        fn g<'a>(c: &'a *mut u64) -> (r: (&'a impl TrP, u8))
            ensures !r.0.is_mut() // FAILS
        {
            (c, 0u8)
        }
    } => Err(err) => assert_one_fails(err)
}
