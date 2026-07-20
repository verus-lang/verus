#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_field_havocing0 verus_code! {
        fn cond() -> bool { true }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
                // fails because of loop_isolation
                assert(x.0 == 0); // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test2(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
                assert(x.1 == 1); // FAILS
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test_no_iso(mut x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            while cond() {
                x.1 = 5;
                assert(x.0 == 0);
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test2_no_iso(mut x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
                assert(x.1 == 1); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_field_havocing1 verus_code! {
        fn cond() -> bool { true }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
            }
            assert(x.0 == 0);
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test2(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
            }
            assert(x.1 == 1); // FAILS
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test_no_iso(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
            }
            assert(x.0 == 0);
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        pub fn test2_no_iso(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
            }
            assert(x.1 == 1); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_field_havocing2 verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        pub fn test1(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.1 = 5;
                x = (1, 1);
            }
            assert(x.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        pub fn test2(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x = (1, 1);
                x.1 = 5;
            }
            assert(x.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        pub fn test3(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                x.0 = 5;
                x.1 = 5;
            }
            assert(x.0 == 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_field_havocing3 verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        pub fn test1(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                if cond() {
                    x.1 = 5;
                } else {
                    x = (1, 1);
                }
            }
            assert(x.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        pub fn test2(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                if cond() {
                    x = (1, 1);
                } else {
                    x.1 = 5;
                }
            }
            assert(x.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        pub fn test3(x: (u64, u64))
            requires x.0 == 0, x.1 == 1,
        {
            let mut x = x;
            while cond() {
                if cond() {
                    x.0 = 5;
                } else {
                    x.1 = 5;
                }
            }
            assert(x.0 == 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_enum verus_code! {
        enum Foo { Bar(u64), Qux(u64) }
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test() {
            let mut foo = Foo::Bar(0);
            while cond() {
                match foo {
                    Foo::Bar(x) => { }
                    Foo::Qux(_) => { }
                }
            }
            assert(foo->Bar_0 == 0);
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2() {
            let mut foo = Foo::Bar(0);
            while cond() {
                match foo {
                    Foo::Bar(ref mut x) => { *x = 1; }
                    Foo::Qux(_) => { }
                }
            }
            assert(foo->Bar_0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3() {
            let mut foo = Foo::Bar(0);
            let ghost old_foo = foo;
            while cond() {
                match foo {
                    Foo::Bar(ref mut x) => { *x = 1; }
                    Foo::Qux(_) => { }
                }
            }
            // The field Qux_0 is never modified, but we don't know we're in the right
            // variant.
            assert(foo->Qux_0 == old_foo->Qux_0); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_enum2 verus_code! {
        enum Foo { Bar(u64), Qux(u64) }
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test1(mut foo: Foo) {
            let ghost old_foo = foo;
            while cond() {
                match foo {
                    Foo::Bar(ref mut x) => { *x = 1; }
                    Foo::Qux(_) => { }
                }
            }
            // This would be ok, but not currently supported by our analysis:
            assert(old_foo is Bar ==> foo is Bar); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut foo: Foo) {
            let ghost old_foo = foo;
            while cond() {
                match foo {
                    Foo::Bar(ref mut x) => { *x = 1; }
                    Foo::Qux(_) => { }
                }
            }
            // This would be ok, but not currently supported by our analysis:
            assert(old_foo is Qux ==> foo is Qux); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut foo: Foo) {
            let ghost old_foo = foo;
            while cond() {
                match foo {
                    Foo::Bar(ref mut x) => { *x = 1; }
                    Foo::Qux(_) => { }
                }
            }
            // This would be ok, but not currently supported by our analysis:
            assert(foo is Qux && old_foo is Qux ==> foo->Qux_0 == old_foo->Qux_0); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_nested verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1.0 = 20;
            }
            assert(a.0.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1.0 = 20;
            }
            assert(a.0.1 == 1);
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1.0 = 20;
            }
            assert(a.1.0 == 10); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test4(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1.0 = 20;
            }
            assert(a.1.1 == 11);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_nested2 verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1 = (20, 30);
            }
            assert(a.0.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1 = (20, 30);
            }
            assert(a.0.1 == 1);
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1 = (20, 30);
            }
            assert(a.1.0 == 10); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test4(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.0.0 = 10;
                a.1 = (20, 30);
            }
            assert(a.1.1 == 11); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_nested3 verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.1 = (20, 30);
                a.0.0 = 10;
            }
            assert(a.0.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.1 = (20, 30);
                a.0.0 = 10;
            }
            assert(a.0.1 == 1);
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.1 = (20, 30);
                a.0.0 = 10;
            }
            assert(a.1.0 == 10); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test4(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                a.1 = (20, 30);
                a.0.0 = 10;
            }
            assert(a.1.1 == 11); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_nested4_test_havoc_set_merge verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.0.0 = 10;
                } else {
                    a.1 = (20, 30);
                }
            }
            assert(a.0.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.0.0 = 10;
                } else {
                    a.1 = (20, 30);
                }
            }
            assert(a.0.1 == 1);
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.0.0 = 10;
                } else {
                    a.1 = (20, 30);
                }
            }
            assert(a.1.0 == 10); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test4(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.0.0 = 10;
                } else {
                    a.1 = (20, 30);
                }
            }
            assert(a.1.1 == 11); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_nested5_test_havoc_set_merge verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.1 = (20, 30);
                } else {
                    a.0.0 = 10;
                }
            }
            assert(a.0.0 == 0); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.1 = (20, 30);
                } else {
                    a.0.0 = 10;
                }
            }
            assert(a.0.1 == 1);
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.1 = (20, 30);
                } else {
                    a.0.0 = 10;
                }
            }
            assert(a.1.0 == 10); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test4(mut a: ((u64, u64), (u64, u64)))
            requires a.0.0 == 0, a.0.1 == 1, a.1.0 == 10, a.1.1 == 11,
        {
            while cond() {
                if cond() {
                    a.1 = (20, 30);
                } else {
                    a.0.0 = 10;
                }
            }
            assert(a.1.1 == 11); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
