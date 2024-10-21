#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_189a verus_code! {
        use vstd::set::*;

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);
            let s2: Set<i32> = Set::empty();
            assert(!s2.contains(1));
            // assert(!s1.ext_equal(s2));
            assert(s1 !== s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_189b verus_code! {
        use vstd::set::*;

        spec fn different_set<V>(s: Set<V>) -> Set<V> { s }

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);

            assert (exists|s3: Set<i32>| different_set(s3) !== s1) by {
                assert(!different_set(Set::empty()).contains(1i32));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_verifier_truncate_allowed_on_cast verus_code! {
        fn test(a: u64) -> u8 {
            #[verifier(truncate)] (a as u8)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hygienic_identifiers_regression_279 verus_code! {
        macro_rules! assert_with_binding {
            ($s1:expr) => {
                let s1 = $s1;
                vstd::pervasive::assert(s1);
            }
        }

        proof fn test() {
            let s1: nat = 0;
            assert_with_binding!(true);
            assert(s1 === 0);
        }

        macro_rules! recursor {
            () => { };
            ($e:expr, $($tail:tt)*) => {
                let s: u8 = $e;
                recursor!($($tail)*);   // this recursive call defines a *distinct* variable called `s`
                assert_(s == $e);       // this `s` should refer to the decl from 2 lines above
            };
        }

        macro_rules! iterer {
            ($($e:expr),*) => {
                $( let s: u8 = $e; )*   // This makes two let statements, but rustc treats them as the same identifier
                assert_(s == 3);        // So this always refers to the last `s` that was declared
            };
        }

        proof fn test_more_complex() {
            let s: u8 = 20;

            recursor!(5, 6,);
            iterer!(2, 3);

            assert_(s == 20);

            let s: u8 = 19;
            assert_(s == 19);
        }

        macro_rules! closure {
            ($e:expr) => {
                closure_to_fn_spec(|s: u8| { $e })
            };
        }

        proof fn test_closure_param_names() {
            let foo = |s: u8| {
                closure!(s)(20) // when we pass `s` into the macro, it should refer to the `s` in the line above
            };

            assert_(foo(5) == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_bad_span_for_postcondition_failure_regression_281 verus_code! {
        #[is_variant]
        enum Enum {
            A,
            B,
        }


        fn test(a: u32) -> (res: Enum)
            ensures (match res {
                Enum::A => a <= 10,
                Enum::B => a > 10, // FAILS
            }) {

            Enum::B
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] fields_from_macros_not_treated_as_distinct_identifiers verus_code! {
        struct Foo(pub u64);

        // Internally, the use of .0 in the macro creates an identifier `0`
        // with some extra info that is used for macro hygeine purposes.
        // However, that info needs to be ignored: the field access .0
        // should be treated like any other .0 access.

        macro_rules! some_macro {
            ($foo:ident) => {
                vstd::pervasive::assert($foo.0 == 20);
            }
        }

        proof fn some_func() {
            let foo = Foo(20);
            assert(foo.0 == 20);

            some_macro!(foo);
        }

        struct Bar { val: u64 }

        macro_rules! some_macro2 {
            ($bar:ident) => {
                vstd::pervasive::assert($bar.val == 30);
            }
        }

        proof fn some_func2() {
            let bar = Bar { val: 30 };
            assert(bar.val == 30);

            some_macro2!(bar);

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parse_named_return_type_with_comma_in_type_args verus_code! {
        use vstd::map::*;

        proof fn some_proof() -> (m: Map<int, int>)
            ensures m === Map::empty()
        {
            Map::empty()
        }

        proof fn cats() {
            let m = some_proof();
            assert(m === Map::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] forall_in_ensures_with_return_keyword_regression_216 verus_code! {
        #[verifier::spec]
        fn f(a: nat) -> bool {
            true
        }

        fn g() -> (res: bool)
            ensures forall|i: nat| f(i)
        {
            return true;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_func_unused_from_other_module_issue_411 verus_code! {
        mod X {
            #[verifier(opaque)]
            pub open spec fn foo() -> bool { true }
        }

        proof fn test() {
            reveal(X::foo);
        }
    } => Ok(_err) => { /* allow deprecated warning */ }
}

test_verify_one_file! {
    #[test] reveal_exec_fn_issue_411 verus_code! {
        pub fn foo() -> bool { true }

        proof fn test() {
            reveal(foo);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal/fuel statements require a spec-mode function")
}

test_verify_one_file! {
    #[test] reveal_proof_fn_issue_411 verus_code! {
        pub proof fn foo() -> bool { true }

        proof fn test() {
            reveal(foo);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal/fuel statements require a spec-mode function")
}

test_verify_one_file! {
    #[test] let_with_parens_issue_260 verus_code! {
        fn f() {
            let (x):usize = 0;
            assert(x == 0);
        }

        fn g() {
            let (x):usize = 0;
            assert(x == 1); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] use_statement_of_spec_fn_issue293 verus_code! {
        mod Y {
            #![allow(dead_code)] // this was needed for the original crash

            use builtin::*;
            use builtin_macros::*;

            verus!{
                mod X {
                    pub open spec fn foo();
                }

                proof fn some_proof_fn() {
                    let x = foo();
                }
            }

            use X::foo; // this was needed for the original crash
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] is_variant_in_exec_issue_341 verus_code! {
        pub struct Lock {}

        #[is_variant]
        pub enum OptionX<T> {
            NoneX,
            SomeX(T)
        }

        pub fn what_is_wrong() -> bool
        {
            let opt_lock = OptionX::SomeX(Lock{});
            let lock = opt_lock.get_SomeX_0();   // This line triggers panic
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::OptionX::get_SomeX_0` with mode spec")
}

test_verify_one_file! {
    #[test] reveal_non_opaque_issue236_1 verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            hide(is_true);
            assert(is_true(true)); // FAILS
            reveal(is_true);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] reveal_non_opaque_issue236_2 verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            hide(is_true);
            reveal(is_true);
            assert(is_true(true));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_with_fuel_non_opaque_non_recursive_issue236_373_pass verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            reveal_with_fuel(is_true, 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_with_fuel_non_opaque_non_recursive_issue236_373_fail verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            reveal_with_fuel(is_true, 2);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal_with_fuel statements require a spec function with a decreases clause")
}

test_verify_one_file_with_options! {
    #[test] call_spec_fn_from_external_body_issue_257 ["--compile"] => verus_code! {
        #[verifier(external_body)]
        fn f(x: usize) -> usize {
            id(x)
        }

        pub open spec fn id(x: usize) -> usize {
            x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] air_function_names_issue_376 verus_code! {
        enum Nat {
            Zero,
            Succ(Box<Nat>),
        }

        spec fn height(n: Nat) -> nat
            decreases n
        {
            match n {
                Nat::Zero => 0,
                Nat::Succ(box m) => height(m),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parse_empty_requires_ensure_invariant verus_code! {
        proof fn test()
            requires
        {
        }

        proof fn test2()
            ensures
        {
        }

        fn test3()
        {
            loop
                invariant
            {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] const_name_in_lifetime_generate_regression_563 verus_code! {
        pub spec const CONST_VALUE: nat = 32;
        #[verifier(external_body)]
        struct Data { }
        impl Data {
            proof fn foo(self) {
                let value: nat = CONST_VALUE as nat;
                if vstd::prelude::arbitrary::<nat>() >= value {
                } else {
                }
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] nat_no_use_builtin_issue575 ["no-auto-import-builtin"] => code! {
        use vstd::prelude::*;

        pub struct MyType {
            x: nat,
        }

        fn main() { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] poly_invalid_air_regression_577 verus_code! {
        use vstd::{prelude::*};

        pub trait Foo {
            fn do_something(&mut self, val: u8);
        }

        pub struct Bar {
            vec: Vec<u8>,
            field0: u8
        }

        impl Bar {
            fn new() -> Self {
                Self {
                    vec: Vec::with_capacity(2),
                    field0: 0,
                }
            }
        }

        impl Foo for Bar {
            fn do_something(&mut self, val: u8) {
                self.field0 = val;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] poly_has_type_regression_577 verus_code! {
        #[verifier::ext_equal]
        struct S {
            n: nat,
            i: int,
        }

        trait T {
            proof fn f(x: &mut S);
        }

        impl T for S {
            proof fn f(x: &mut S) {
                x.n = 3; // breaks has_type unless we add Box(Unbox(x)) == x
                assert(*x =~= S { n: x.n, i: x.i });
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] def_id_names_for_builtins_regression_588 ["no-auto-import-builtin"] => code! {
        use vstd::{prelude::*, seq::*};

        verus! {

        spec fn pred(a: nat, s: Seq<int>) -> bool
        {
            a < s.len()
        }

        } // verus!
    } => Ok(_err) => { /* allow unused warning */ }
}

test_verify_one_file! {
    #[test] typ_invariants_with_typ_decorations_issue604 verus_code!{
        pub struct PageId {
            pub i: nat,
        }

        struct PageIdContainer {
            page_id: Ghost<PageId>,
        }

        spec fn a(page_id: PageId) -> bool;
        spec fn b(page_id: PageId) -> bool;

        proof fn test(pic: PageIdContainer) {
            let page_id = pic.page_id@;

            assume(a(page_id));
            assume(forall |page_id| #[trigger] a(page_id) ==> b(page_id));
            assert(b(page_id));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_impl_for_same_name_issue314 verus_code! {
        pub trait Foo {
            spec fn foo(&self) -> bool;
        }

        pub type MyType<T> = spec_fn(T) -> bool;

        impl<T> Foo for MyType<T> {
            open spec fn foo(&self) -> bool {
                true
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_broadcast_forall_import_issue471 ["no-auto-import-builtin"] => code! {
        use builtin_macros::*;
        #[allow(unused_imports)]
        use vstd::{seq::*, seq_lib::*};

        verus! {

        proof fn weird_broadcast_failure(seq:Seq<usize>)
        {
            //seq_to_set_is_finite_broadcast::<usize>(seq);
            assert(seq.to_set().finite());
        }

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_attr_parsing_387_discussioncomment_6611094_1 verus_code! {
        #[verifier:ext_equal]
        pub struct Y {
            y: int
        }
    } => Err(err) => assert_vir_error_msg(err, "expected one of")
}

test_verify_one_file! {
    #[test] test_attr_parsing_387_discussioncomment_6611094_2 verus_code! {
        #[verifier(wat, wat)]
        pub struct Y {
            y: int
        }
    } => Err(err) => assert_vir_error_msg(err, "unrecognized verifier attribute")
}

test_verify_one_file! {
    #[test] test_attr_parsing_regression_684 verus_code! {
        #[verifier(external),verifier(external_body)]
        proof fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "expected `]`, found `,`")
}

test_verify_one_file! {
    #[test] test_attr_parsing_387_discussioncomment_6611094_3 verus_code! {
        #[verifier("something")]
        proof fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "unrecognized verifier attribute")
}

test_verify_one_file! {
    #[test] test_empty_recommends_387_discussioncomment_5670055 verus_code! {
        pub open spec fn foo() -> bool
          recommends
          {
              true
          }

        proof fn test() {
            assert(foo());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_empty_recommends_387_discussioncomment_6117310_1 verus_code! {
        pub open fn test() -> bool {
            1int > 0int
        }
    } => Err(err) => assert_vir_error_msg(err, "only `spec` functions can be marked `open` or `closed`")
}

test_verify_one_file! {
    #[test] test_unwrapped_tracked_wrong_span_387_discussioncomment_6733203_1 verus_code! {
        fn test_bug1(Tracked(s): Tracked<&mut i32>)
        {
            let tracked x: &mut i32 = s;
        }
    } => Err(err) => {
        assert!(err.errors[0].rendered.contains("let tracked x: &mut i32 = s;"));
    }
}

test_verify_one_file! {
    #[test] test_unwrapped_tracked_wrong_span_387_discussioncomment_6733203_2 verus_code! {
        fn test_bug2(Tracked(s): Tracked<&mut i32>)
        {
            let tracked x: i32 = s;
        }
    } => Err(err) => {
        assert!(err.errors[0].rendered.contains("let tracked x: i32 = s;"));
    }
}

test_verify_one_file! {
    #[test] test_unwrapped_tracked_unintended_387_discussioncomment_6680621 verus_code! {
        exec fn f(foo: &mut usize) {
            let tracked tracked_foo = Tracked(foo);
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert_eq!(err.warnings.len(), 1);
        assert!(err.errors[0].rendered.contains("let tracked tracked_foo = Tracked(foo);"));
        assert!(err.warnings.iter().find(|x| x.message.contains("the right-hand side is already wrapped with `Tracked`")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_unwrapped_ghost_unintended_387_discussioncomment_6680621 verus_code! {
        exec fn f(foo: usize) {
            let ghost ghost_foo = Ghost(foo);
        }
    } => Ok(err) => {
        dbg!(&err);
        assert_eq!(err.errors.len(), 0);
        assert!(err.warnings.iter().find(|x| x.message.contains("the right-hand side is already wrapped with `Ghost`")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_multiset_finite_false_1 verus_code! {
        use vstd::{map::*, multiset::*};
        proof fn test(mymap: Map<nat, nat>)
            requires !mymap.dom().finite() {

            let m = Multiset::new(mymap);
            assert(m.dom().finite());

            assert(!m.dom().finite()); // FAILS
            // assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_multiset_finite_false_2 verus_code! {
        use vstd::{map::*, multiset::*};
        proof fn test(mymap: Map<nat, nat>)
            requires !mymap.dom().finite() {

            let m = Multiset::new(mymap);
            assert(m.dom().finite());

            assert(m.dom() =~= mymap.dom()); // FAILS
            // assert(!m.dom().finite());
            // assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] str_len_contradiction_from_suspect_unsoundness_report verus_code! {
        use vstd::string::*;
        use vstd::seq::*;
        proof fn test(s2: Seq<char>, s1: Seq<char>)
            requires
                (s1 + new_strlit("-ab")@ == s2 + new_strlit("-cde")@) ||
                (s1 + new_strlit("-cde")@ == s2 + new_strlit("-cde")@),
        {
            assert(
                (s1.len() + 3 == s2.len() + 4) ||
                (s1.len() + 4 == s2.len() + 4)
            ) by {
                reveal_strlit("-cde");
                reveal_strlit("-ab");
                assert((s1 + new_strlit("-ab")@).len() == s1.len() + new_strlit("-ab")@.len() == s1.len() + 3);
                assert((s1 + new_strlit("-cde")@).len() == s1.len() + new_strlit("-cde")@.len() == s1.len() + 4);
                assert((s2 + new_strlit("-cde")@).len() == s2.len() + new_strlit("-cde")@.len() == s2.len() + 4);
            };

            assert(s1 + new_strlit("-ab")@ != s2 + new_strlit("-cde")@) by {
                let str1 = s1 + new_strlit("-ab")@;
                let str2 = s2 + new_strlit("-cde")@;
                assert(str1.len() == s1.len() + 3) by {
                    reveal_strlit("-ab");
                    assert(str1.len() == (s1 + new_strlit("-ab")@).len() == s1.len() + new_strlit("-ab")@.len() == s1.len() + 3);
                };
                assert(str2.len() == s2.len() + 4) by {
                    reveal_strlit("-cde");
                    assert(str2.len() == (s2 + new_strlit("-cde")@).len() == s2.len() + new_strlit("-cde")@.len() == s2.len() + 4);
                };
                if str2.len() == str1.len() {
                    assert(s1.len() + 3 == s2.len() + 4);
                    assert(s1 + new_strlit("-ab")@ == s2 + new_strlit("-cde")@); // from the requires

                    assert(str1 == s2 + new_strlit("-cde")@);
                    assert(str1 == s1 + new_strlit("-ab")@);

                    reveal_strlit("-ab");
                    reveal_strlit("-cde");
                    assert(str2[str2.len() - 1] == 'e');
                    assert(str2[str2.len() - 1] == 'b');
                    assert(false);
                }
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_reveal_type_args_regression_704 verus_code! {
        trait X {}
        impl X for int {}

        #[verifier::opaque]
        spec fn foo(x: impl X) -> bool {
            true
        }

        proof fn test()
        {
            reveal(foo);

            assert(foo(3int));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_lifetime_constructor_regression_768 verus_code! {
        use vstd::prelude::*;
        proof fn foo() {
            let input: Option<u64> = None;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_generate_assoc_type_regression_769 verus_code! {
        pub trait EA {
            type I;
            type O;
        }

        pub struct Empty {}

        pub struct EAA {}

        impl EA for EAA {
            type I = Empty;
            type O = Empty;
        }

        pub struct MC<E>(E);

        pub struct M<E: EA> {
            pub content: MC<E>,
        }

        enum A<X> {
            Y(X),
            Z,
        }

        proof fn foo() {
            let input: A<M<EAA>> = A::Z;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] zulip_rc_clone verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;

        fn test(rc: Rc<Vec<u8>>) {
            let rc2 = Rc::clone(&rc);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_fn_with_ref_arguments_1 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        struct X { v: u64 }

        fn test<F: Fn(&X) -> bool>(f: F, x: X) -> bool
            requires f.requires((&x,))
        {
            f(&x)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_fn_with_ref_arguments ["vstd"] => verus_code! {
        use vstd::prelude::*;

        struct X { v: u64 }
        struct Y { w: u64 }

        fn test<F: Fn(&X, &Y) -> bool>(f: F, x: X, y: Y) -> bool
            requires f.requires((&x, &y,))
        {
            f(&x, &y)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] zulip_external_body_clone_regression_800_1 verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;
        #[verifier(external_body)]
        pub exec fn rc_clone(rc: &Rc<Vec<u8>>) -> (res: Rc<Vec<u8>>)
            ensures (*rc)@ == (*res)@
        {
            Rc::clone(&rc)
        }

        pub exec fn blah(rc: Rc<Vec<u8>>) {
            let tmp: Rc<Vec<u8>> = rc_clone(&rc);
            assert((*rc)@ == tmp@); // assertion fails
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] zulip_external_body_clone_regression_800_2 verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;
        pub exec fn blah(rc: Rc<Vec<u8>>) {
            assert(rc@ == (*rc)@); // fails
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assert_forall_trigger_regression_824 verus_code! {
        use vstd::seq::Seq;
        pub open spec fn f(x: u32) -> bool;

        proof fn test(a: Seq<u32>)
            requires forall |i| #![trigger f(a[i])] f(a[i]),
        {
            // assert forall #![trigger f(a[i])] |i| f(a[i]) by { }
            assert forall |i| #![trigger f(a[i])] f(a[i]) by { } // <== error
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] inside_of_ghost_processed_as_ghost_issue815 verus_code! {
        spec fn stuff_spec() -> bool { true }

        #[verifier::when_used_as_spec(stuff_spec)]
        fn stuff() -> bool { true }

        // Test to check if properly determine ghostness withing a Ghost(...) expression

        fn test() {
            // at the time of writing,
            // when_used_as_spec is processed via the is_ghost flag in rust_to_vir

            let x: Ghost<bool> = Ghost(stuff());
            assert(x@ == true);
        }

        fn test2() {
            // Likewise, ghostness determines whether the following command
            // has a hard overflow-check (in ghost mode, it shouldn't)

            let x: Ghost<u8> = Ghost(add(200u8, 200u8));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] use_import_is_not_supported_in_traits_or_impls verus_code! {
        use state_machines_macros::state_machine;
        use vstd::*;

        state_machine!{ MachineWithProof {
        fields {
            pub x: int,
        }

        // If the `pub` access specifier is added then the error message goes away
        proof fn truey()
            ensures true
        {
            assume(false);
        }
        } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_generate_trait_lifetime_arg verus_code! {
        trait T<'a> { type X; }
        struct S { }
        impl<'a> T<'a> for S { type X = u8; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_generate_trait_lifetime_arg_supported verus_code! {
        trait T<'a> { type X; }
        struct S { }
        impl<'a> T<'a> for S { type X = u8; }
        proof fn test1(x: <S as T>::X) {
            assert(x < 256);
        }
    } => Ok(())
}

test_verify_one_file! {
    // tests a scenario (temporarily) addressed by 81100927
    // > As a temporary patch, order spec functions early in call graph
    #[test] axiom_ordering_patched verus_code! {
        mod m2 {
            use vstd::prelude::*;

            pub trait B<T: View> {
                spec fn b1(t: T) -> bool;

                spec fn b2(t: T::V) -> bool;

                proof fn b_proof(t: T) requires Self::b1(t), ensures Self::b2(t@);
            }

        }

        mod m3 {
            use vstd::prelude::*;

            pub struct C {}

            impl crate::m2::B<crate::m0::MyBool> for C {
                open spec fn b1(t: crate::m0::MyBool) -> bool { t.0 }

                open spec fn b2(t: bool) -> bool { t }

                proof fn b_proof(t: crate::m0::MyBool) {
                    // let v = t@; // this line was necessary to make this proof pass before the patch
                }
            }
        }

        mod m0 {
            pub struct MyBool(pub bool);
        }

        // this module has to come last to trigger the incompleteness
        mod m1 {
            use vstd::prelude::*;

            impl View for crate::m0::MyBool {
                type V = bool;

                open spec fn view(&self) -> bool { self.0 }
            }

            pub open spec fn aa<T: View>(t: T) -> T::V { t@ }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tuple_impl_regression_869 verus_code! {
        pub trait Tau {
            fn foo() -> Self::T;

            type T;
        }
        impl<A, B> Tau for (A, B) {
            fn foo() -> bool { true }

            type T = bool;
        }
        impl<A, B, C> Tau for (A, B, C) {
            fn foo() -> bool { true }

            type T = bool;
        }

        fn main() {
            let c: <(u64, u64) as Tau>::T = <(u64, u64)>::foo();
            let c: <(u64, u64, u64) as Tau>::T = <(u64, u64, u64)>::foo();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_macros_regression_866 verus_code! {
        use vstd::seq::seq;
        macro_rules! temp {
          () => {
            verus! {
              proof fn foo() {
                assert(seq![1u64,2] =~= seq![1u64,2]);
                assert(seq![1u64,2] =~~= seq![1u64,2]);

                assert(false !~= true);
                assert(false !~~= true);
              }
            }
          };
        }
        temp!{}
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_proof_using_own_lemma verus_code! {
        mod m1 {
            use builtin_macros::*;
            verus! {
                #[verifier::external_body]
                pub struct S { p: core::marker::PhantomData<()> }

                pub spec fn p1(s: S) -> bool;
                pub spec fn p2(s: S) -> bool;

                pub proof fn p(s: S)
                    requires p1(s),
                    ensures p2(s) {

                    assume(false);
                }

                pub trait A {
                    proof fn two(s: S)
                        requires p1(s),
                        ensures p2(s);

                    proof fn one()
                        ensures forall|s: S| p1(s) ==> p2(s);
                }
            }
        }

        mod m2 {
            use builtin_macros::*;
            verus! {
                use crate::m1::*;

                struct X;

                impl A for X {
                    proof fn two(s: S) {
                        Self::one();
                    }

                    proof fn one() {
                        assert forall|s: S| p1(s) implies p2(s) by {
                            p(s);
                        }
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] panic_external_by_default_regression893 verus_code! {
        use vstd::prelude::*;

        pub enum Message { A, B, }

        pub enum SingleMessage {
            Message {
                seqno: nat,
                other: nat,
            },
            Other,
        }

        pub struct Packet {
            pub msg: SingleMessage,
            pub other: nat,
        }

        pub struct CPacket {
            pub msg: CSingleMessage,
            pub other: u64,
        }

        impl CPacket {
            pub open spec fn view(self) -> Packet {
                Packet { msg: self.msg@, other: self.other@ as nat }
            }
        }

        pub enum CSingleMessage {
            Message { seqno: u64, other: u64 },
            Other,
        }

        impl CSingleMessage {
            pub open spec fn view(self) -> SingleMessage {
                arbitrary()
            }
        }

        struct HostState {
            received_packet: Option<CPacket>,
        }

        impl HostState {
            fn host_model_next_get_request(&mut self) -> (sent_packets: Vec<CPacket>) {
                assume(self.received_packet.is_some());
                let cpacket: &CPacket = &self.received_packet.as_ref().unwrap();
                let ghost pkt: Packet = cpacket@;
                match &cpacket.msg {
                    CSingleMessage::Message{ seqno, .. } => {
                        let ghost received_request: nat = seqno@ as nat;
                    }
                    _ => (),
                }
                assume(false); unreached()
            }
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] closure_projection_regression_910 verus_code! {
        use vstd::prelude::*;

        trait T {
            type X;
        }

        struct L<D: T> {
            x: D::X,
        }

        spec fn f1<DT: T>(l: Map<nat, L<DT>>) -> Seq<DT::X> {
            Seq::new(1, |i: int| l[i as nat].x)
        }

        spec fn f2<DT: T>(l: L<DT>) -> spec_fn(L<DT>)->DT::X {
            |ll: L<DT>| ll.x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parsing_unit_ret_type_issue937 verus_code! {
        fn stuff() -> () { }

        fn stuff_fn_once<F: FnOnce(u8) -> ()>() { }

        fn pat_ret_colons() -> (x: ::std::primitive::bool)
        {
            true
        }

        fn pat_ret_colons2() -> (::std::primitive::bool)
        {
            true
        }

        fn pat_ret_colons3() -> (std::primitive::bool)
        {
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] syntax_named_return_type_issue603 verus_code! {
        // Make sure a type gets translated when it gets copied into
        // the macro-generated 'ensures' call.
        pub proof fn test(x: nat) -> (t: spec_fn(nat) -> nat)
            ensures true,
        {
            |i| i
        }

        pub fn test2(x: nat)
            ensures true,
        {
            let clos = || -> (t: Ghost<spec_fn(nat) -> nat>)
                ensures true
            {
                let ghost s = |i| i;
                Ghost(s)
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_with_updater_and_tuple_type_in_field_issue857 verus_code! {
        use vstd::prelude::*;
        use vstd::set::*;

        pub struct S {
            pub n: int,
            pub s: Set<(int, int)>,
        }

        pub open spec fn f(s1: S, s2: S) -> bool {
            s2 == S { n: s1.n + 1, ..s1 }
        }

        pub proof fn test(se: Set<(int, int)>) {
            let s1 = S { n: 20, s: se };
            let s2 = S { n: 21, s: se };
            assert(f(s1, s2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_with_updater_and_typ_subst_in_field_issue956 verus_code! {
        struct X<T> {
            a: int,
            b: T,
        }

        proof fn stuff(x: X<bool>) {
            let y = X { a: x.a + 1, .. x };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] seq_add_axiom_issue990 verus_code! {
        use vstd::{prelude::*, seq::*};
        proof fn seq_bad()
            ensures false
        {
            let s1: Seq<int> = seq![1];
            let s1_2: Seq<int> = seq![1, 2];
            let s2: Seq<int> = seq![];
            assert(s1.add(s2)[0] == s2[-1]); // FAILS
            assert(s1_2.add(s2)[1] == s2[-1]); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] external_module_issue618 verus_code! {
        #[verifier::external]
        mod M {
            pub fn stuff() {
                panic!("qewrty");
            }
        }

        fn rawr() {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] arithmetic_trigger_choose_issue923 verus_code! {
        proof fn foo(a: nat, b: nat) {
            let i = choose|i: nat| a == #[trigger] (b * i);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] slice_of_tuple_issue1259 verus_code! {
        use vstd::*;
        pub fn run(val: &[(u32, u32)]) -> u64
            requires
                val.len() > 0,
        {
            val[0].0 as u64 + val[0].1 as u64
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] external_body_trait_item_issue1134 verus_code! {
        trait Serializable : Sized {
            fn serialized_len() -> (out: u64);

            #[verifier::external_body]
            fn as_bytes(&self)
            {
                let ptr = self as *const Self as *const u8;
                let slice = unsafe {
                    std::slice::from_raw_parts(ptr, Self::serialized_len() as usize)
                };
            }
        }
    } => Ok(())
}
