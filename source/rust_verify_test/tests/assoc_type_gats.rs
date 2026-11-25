#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] gat_decl_impl_projection verus_code! {
        trait T {
            type X<A>;
            spec fn mk<A>(a: A) -> Self::X<A>;
        }
        struct S;
        impl T for S {
            type X<A> = (A, u8);
            spec fn mk<A>(a: A) -> (A, u8) {
                (a, 7)
            }
        }
        spec fn mk_generic<B: T, A>(a: A) -> B::X<A> {
            B::mk(a)
        }
        proof fn test1(x: <S as T>::X<bool>) {
            assert(x.1 < 256);
        }
        proof fn test2() {
            let x: (bool, u8) = mk_generic::<S, bool>(true);
            assert(x == (true, 7u8));
        }
        proof fn test3() {
            let x: (bool, u8) = mk_generic::<S, bool>(true);
            assert(x.1 == 8); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] gat_generic_projection verus_code! {
        trait T {
            type X<A>;
            spec fn get<A>(&self, a: A) -> Self::X<A>;
            spec fn put<A>(&self, x: Self::X<A>) -> A;
        }
        spec fn round_trip<B: T>(b: B, x: B::X<u8>) -> u8 {
            b.put(x)
        }
        proof fn test<B: T>(b: B) {
            let x: B::X<u8> = b.get(3u8);
            let y: u8 = round_trip(b, x);
            assert(y < 256);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_args_distinct_fail verus_code! {
        trait Tag {
            spec fn tag() -> int;
        }
        trait T {
            type X<A>: Tag;
        }
        proof fn test<B: T>() {
            assert(<B::X<u8> as Tag>::tag() == <B::X<bool> as Tag>::tag()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] gat_param_bound verus_code! {
        trait P {}
        trait D {}
        impl P for u8 {}
        struct W<A>(A);
        impl<A: P> D for W<A> {}
        trait Tag {
            spec fn tag() -> int;
        }
        struct Wrap<A>(A);
        impl<A: D> Tag for Wrap<A> {
            spec fn tag() -> int { 5 }
        }
        trait T {
            type X<A: P>: D;
        }
        struct S;
        impl T for S {
            type X<A: P> = W<A>;
        }
        proof fn test<B: T>() {
            assert(<Wrap<B::X<u8>> as Tag>::tag() == 5);
        }
        proof fn test_impl() {
            assert(<Wrap<<S as T>::X<u8>> as Tag>::tag() == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_param_where_clause verus_code! {
        trait P {}
        trait Q {}
        trait D {}
        impl P for u8 {}
        impl Q for u8 {}
        struct W<A>(A);
        impl<A: P + Q> D for W<A> {}
        trait Tag {
            spec fn tag() -> int;
        }
        struct Wrap<A>(A);
        impl<A: D> Tag for Wrap<A> {
            spec fn tag() -> int { 5 }
        }
        trait T {
            type X<A: P>: D where A: Q;
        }
        struct S;
        impl T for S {
            type X<A: P> = W<A> where A: Q;
        }
        proof fn test<B: T>() {
            assert(<Wrap<B::X<u8>> as Tag>::tag() == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_item_bound verus_code! {
        trait D {
            spec fn d(&self) -> int;
            proof fn d_pos(&self)
                ensures self.d() > 0;
        }
        trait T {
            type X<A>: D;
        }
        proof fn test<B: T>(x: B::X<u8>, y: B::X<bool>) {
            x.d_pos();
            y.d_pos();
            assert(x.d() + y.d() > 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_item_bound_needs_param_bound verus_code! {
        trait P {}
        trait D {}
        trait Tag {
            spec fn tag() -> int;
        }
        struct Wrap<A>(A);
        impl<A: D> Tag for Wrap<A> {
            spec fn tag() -> int { 5 }
        }
        trait T {
            type X<A: P>: D;
        }
        proof fn test<B: T, C: P>() {
            assert(<Wrap<B::X<C>> as Tag>::tag() == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_item_bound_mentions_param verus_code! {
        trait D<A> {
            spec fn d(&self) -> A;
        }
        trait T {
            type X<A>: D<A>;
        }
        proof fn test<B: T>(x: B::X<u8>) {
            let a: u8 = x.d();
            assert(a < 256);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_nested_projection verus_code! {
        trait U {
            type Y;
        }
        trait T {
            type X<A>: U;
        }
        struct S;
        struct V<A>(A);
        impl<A> U for V<A> {
            type Y = A;
        }
        impl T for S {
            type X<A> = V<A>;
        }
        spec fn nest<B: T>(x: B::X<B::X<u8>>) -> B::X<B::X<u8>> {
            x
        }
        spec fn inner<B: T>(y: <B::X<u8> as U>::Y) -> <B::X<u8> as U>::Y {
            y
        }
        proof fn test(x: V<V<u8>>, y: u8) {
            assert(nest::<S>(x) == x);
            assert(inner::<S>(y) == y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_trait_method_sig verus_code! {
        use vstd::prelude::*;
        trait T {
            type X<A>;
            spec fn view<A>(x: &Self::X<A>) -> A;
            fn wrap<A>(&self, a: A) -> (r: Self::X<A>)
                ensures Self::view(&r) == a;
        }
        struct S;
        impl T for S {
            type X<A> = Option<A>;
            spec fn view<A>(x: &Option<A>) -> A {
                x.unwrap()
            }
            fn wrap<A>(&self, a: A) -> (r: Option<A>) {
                Some(a)
            }
        }
        fn test<B: T>(b: &B) {
            let r = b.wrap(3u8);
            assert(B::view(&r) == 3);
        }
        fn test_s(s: &S) {
            let r = s.wrap(true);
            assert(r.unwrap() == true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_trait_method_ensures_fail verus_code! {
        use vstd::prelude::*;
        trait T {
            type X<A>;
            spec fn view<A>(x: &Self::X<A>) -> A;
            fn wrap<A>(&self, a: A) -> (r: Self::X<A>)
                ensures Self::view(&r) == a; // FAILS
        }
        struct S;
        impl T for S {
            type X<A> = Option<A>;
            spec fn view<A>(x: &Option<A>) -> A {
                x.unwrap()
            }
            fn wrap<A>(&self, a: A) -> (r: Option<A>) {
                None
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] gat_spec_fn verus_code! {
        use vstd::prelude::*;
        trait T {
            type X<A>;
            spec fn len<A>(x: Self::X<A>) -> nat;
        }
        struct S;
        impl T for S {
            type X<A> = Seq<A>;
            spec fn len<A>(x: Seq<A>) -> nat {
                x.len()
            }
        }
        uninterp spec fn f<B: T>(x: B::X<int>) -> int;
        spec fn g<B: T>(x: B::X<int>) -> nat {
            B::len(x)
        }
        proof fn test(s: Seq<int>) {
            assert(f::<S>(s) == f::<S>(s));
            assert(g::<S>(s) == s.len());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_two_impls_different_values verus_code! {
        trait Tag {
            spec fn tag() -> int;
        }
        impl Tag for u8 {
            spec fn tag() -> int { 1 }
        }
        impl Tag for u16 {
            spec fn tag() -> int { 2 }
        }
        trait T {
            type X<A>: Tag;
        }
        struct S1;
        struct S2;
        impl T for S1 {
            type X<A> = u8;
        }
        impl T for S2 {
            type X<A> = u16;
        }
        spec fn tag_of<B: T, A>() -> int {
            <B::X<A> as Tag>::tag()
        }
        proof fn test() {
            assert(tag_of::<S1, bool>() == 1);
            assert(tag_of::<S2, bool>() == 2);
        }
        proof fn test_fail() {
            assert(tag_of::<S1, bool>() == tag_of::<S2, bool>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] gat_impl_value_depends_on_arg verus_code! {
        trait Tag {
            spec fn tag() -> int;
        }
        impl Tag for u8 {
            spec fn tag() -> int { 1 }
        }
        impl Tag for bool {
            spec fn tag() -> int { 2 }
        }
        trait T {
            type X<A: Tag>: Tag;
        }
        struct S;
        impl T for S {
            type X<A: Tag> = A;
        }
        spec fn tag_of<B: T, A: Tag>() -> int {
            <B::X<A> as Tag>::tag()
        }
        proof fn test() {
            assert(tag_of::<S, u8>() == 1);
            assert(tag_of::<S, bool>() == 2);
        }
        proof fn test_fail() {
            assert(tag_of::<S, u8>() == tag_of::<S, bool>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] gat_impl_value_bound_proof_fail verus_code! {
        trait D {
            spec fn d(&self) -> int;
            proof fn d_pos(&self)
                ensures self.d() > 0; // FAILS
        }
        struct W<A>(A);
        impl<A> D for W<A> {
            spec fn d(&self) -> int { 0 }
            proof fn d_pos(&self) {
            }
        }
        trait T {
            type X<A>: D;
        }
        struct S;
        impl T for S {
            type X<A> = W<A>;
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] gat_impl_value_violates_bound verus_code! {
        trait D {}
        trait T {
            type X<A>: D;
        }
        struct S;
        impl T for S {
            type X<A> = A;
        }
    } => Err(err) => assert_vir_error_msg(err, "is not satisfied")
}

test_verify_one_file! {
    #[test] gat_impl_value_bound_cycle verus_code! {
        trait D {
            spec fn d() -> int;
        }
        trait T {
            type X<A>: D;
        }
        struct S;
        struct W<A>(A);
        impl<A> D for W<A> {
            spec fn d() -> int {
                f::<S>()
            }
        }
        impl T for S {
            type X<A> = W<A>;
        }
        spec fn f<B: T>() -> int {
            <B::X<u8> as D>::d()
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] gat_impl_missing_where_clause verus_code! {
        trait P {}
        trait T {
            type X<A> where A: P;
        }
        struct S;
        impl T for S {
            type X<A> = (A, A);
        }
    } => Err(err) => assert_vir_error_msg(err, "is not satisfied")
}

test_verify_one_file! {
    #[test] gat_unsized_param verus_code! {
        use vstd::prelude::*;
        trait T {
            type X<A: ?Sized>;
        }
        struct S;
        impl T for S {
            type X<A: ?Sized> = Box<A>;
        }
        proof fn test(x: <S as T>::X<[u8]>, y: <S as T>::X<u8>) {
            assert(*y < 256);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_lifetime_and_type verus_code! {
        trait T {
            type X<'a, A: 'a> where Self: 'a;
            fn get<'a, A>(&'a self, a: &'a A) -> (r: Self::X<'a, A>);
        }
        struct S;
        impl T for S {
            type X<'a, A: 'a> = &'a A where Self: 'a;
            fn get<'a, A>(&'a self, a: &'a A) -> (r: &'a A)
                ensures r == a,
            {
                a
            }
        }
        fn test(s: &S) {
            let a = 5u8;
            let r = s.get(&a);
            assert(*r == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_lifetime_only verus_code! {
        trait T {
            type X<'a> where Self: 'a;
            fn get<'a>(&'a self) -> Self::X<'a>;
        }
        struct S(u8);
        impl T for S {
            type X<'a> = &'a u8 where Self: 'a;
            fn get<'a>(&'a self) -> (r: &'a u8)
                ensures *r == self.0,
            {
                &self.0
            }
        }
        fn test(s: &S) {
            let r = s.get();
            assert(*r == s.0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_const_param_unsupported verus_code! {
        trait T {
            type X<const N: usize>;
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support const parameters on generic associated types")
}

test_verify_one_file! {
    #[test] gat_equality_bound_unsupported verus_code! {
        trait T {
            type X<A>;
        }
        fn f<B: T<X<u8> = u16>>(b: B) {}
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support equality bounds on generic associated types")
}

test_verify_one_file! {
    #[test] gat_external_trait_specification_unsupported verus_code! {
        #[verifier::external]
        trait T {
            type X<A>;
        }
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;
            type X<A>;
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support generic associated types in `external_trait_specification`")
}

test_verify_one_file! {
    #[test] gat_impl_of_unverified_trait_no_ice code! {
        use vstd::prelude::*;
        pub trait T {
            type X<A>;
        }
        verus! {
            pub struct S;
            impl T for S {
                type X<A> = Vec<A>;
            }
            fn f(x: <S as T>::X<u8>) -> (r: usize)
                ensures r == x.len(),
            {
                x.len()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_recursive_datatype_through_arg verus_code! {
        trait T {
            type X<A>;
        }
        struct S;
        impl T for S {
            type X<A> = spec_fn(A) -> bool;
        }
        struct L<B: T> {
            f: B::X<L<B>>,
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive position")
}

test_verify_one_file! {
    #[test] gat_prune_unused verus_code! {
        trait D {}
        trait T {
            type X<A>: D;
            type Y;
        }
        struct S;
        struct W<A>(A);
        impl<A> D for W<A> {}
        impl T for S {
            type X<A> = W<A>;
            type Y = u8;
        }
        proof fn test(y: <S as T>::Y) {
            assert(y < 256);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_prune_reached_via_bound verus_code! {
        trait D {
            spec fn d(&self) -> int;
            proof fn d_pos(&self)
                ensures self.d() > 0;
        }
        trait T {
            type X<A>: D;
        }
        spec fn get_d<B: D>(b: B) -> int {
            b.d()
        }
        proof fn test<B: T>(x: B::X<u8>) {
            x.d_pos();
            assert(get_d(x) > 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] gat_future_bound_where_clause verus_code! {
        use vstd::prelude::*;
        trait RA {}
        impl RA for u8 {}
        trait T {
            type Fut<A>: core::future::Future<Output = u8> where A: RA;
            fn t<A: RA>(&self, a: A) -> Self::Fut<A>;
        }
        struct S;
        #[verifier::external_body]
        struct Ready;
        #[verifier::external]
        impl core::future::Future for Ready {
            type Output = u8;
            fn poll(
                self: core::pin::Pin<&mut Self>,
                _cx: &mut core::task::Context<'_>,
            ) -> core::task::Poll<u8> {
                core::task::Poll::Ready(3)
            }
        }
        impl T for S {
            type Fut<A> = Ready where A: RA;
            #[verifier::external_body]
            fn t<A: RA>(&self, a: A) -> Ready {
                Ready
            }
        }
        fn test<B: T>(b: &B) {
            let _f = b.t(1u8);
        }
    } => Ok(())
}

test_verify_crates! {
    #[test] gat_cross_crate [
        "a" => verus_code! {
            pub trait D {
                spec fn d(&self) -> int;
                proof fn d_pos(&self)
                    ensures self.d() > 0;
            }
            pub trait T {
                type X<A>: D;
                spec fn mk<A>(a: A) -> Self::X<A>;
            }
            pub struct W<A>(pub A);
            impl<A> D for W<A> {
                open spec fn d(&self) -> int { 1 }
                proof fn d_pos(&self) {}
            }
            pub struct S;
            impl T for S {
                type X<A> = W<A>;
                open spec fn mk<A>(a: A) -> W<A> { W(a) }
            }
        },
        "b" => verus_code! {
            use a::*;
            pub struct S2;
            impl T for S2 {
                type X<A> = W<(A, A)>;
                open spec fn mk<A>(a: A) -> W<(A, A)> { W((a, a)) }
            }
            proof fn test<B: T>(x: B::X<u8>) {
                x.d_pos();
                assert(x.d() > 0);
            }
            proof fn test_impls() {
                assert(S::mk(3u8).0 == 3);
                assert(S2::mk(3u8).0 == (3u8, 3u8));
            }
            proof fn test_fail() {
                assert(S2::mk(3u8).0.0 == 4); // FAILS
            }
        },
    ] => Err(err) => assert_one_fails(err)
}
