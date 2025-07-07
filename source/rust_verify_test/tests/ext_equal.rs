#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_fn verus_code! {
        #[verifier::auto_ext_equal()]
        proof fn test(x: spec_fn(int, u8) -> int, y: spec_fn(int, u8) -> int) {
            assume(forall|i: int, j: u8| #[trigger] x(i, j) == y(i, j));
            assert(x =~= y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fn_fails verus_code! {
        proof fn test(x: spec_fn(int, u8) -> int, y: spec_fn(int, u8) -> int) {
            assert(x =~= y); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_seq verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<u8>, s2: Seq<u8>) {
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s1[0] == s2[0]);
            assert(s1 =~= s2);
        }

        proof fn test_auto_ext_equal_in_assert(s1: Seq<u8>, s2: Seq<u8>) {
            assert(s1.len() == 1 && s2.len() == 1 && s1[0] == s2[0] ==> s1 == s2);
        }

        #[verifier::auto_ext_equal(assert)]
        proof fn test_no_auto_ext_equal_in_ensures(s1: Seq<u8>, s2: Seq<u8>)
            ensures s1.len() == 1 && s2.len() == 1 && s1[0] == s2[0] ==> s1 == s2 // FAILS
        {
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_seq_fails1 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<u8>, s2: Seq<u8>) {
            assume(s1.len() == 1);
            assume(s1[0] == s2[0]);
            assert(s1 =~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_seq_fails2 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<u8>, s2: Seq<u8>) {
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assert(s1 =~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_set verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Set<u8>, s2: Set<u8>) {
            assume(forall|i: u8| 1 <= i ==> !s1.contains(i));
            assume(forall|i: u8| 1 <= i ==> !s2.contains(i));
            assume(s1.contains(0));
            assume(s2.contains(0));
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_set_fails1 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Set<u8>, s2: Set<u8>) {
            assume(forall|i: u8| 1 <= i ==> !s1.contains(i));
            assume(s1.contains(0));
            assume(s2.contains(0));
            assert(s1 =~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_set_fails2 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Set<u8>, s2: Set<u8>) {
            assume(forall|i: u8| 1 <= i ==> !s1.contains(i));
            assume(forall|i: u8| 1 <= i ==> !s2.contains(i));
            assume(s2.contains(0));
            assert(s1 =~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_map verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(m1: Map<u8, bool>, m2: Map<u8, bool>) {
            assume(forall|i: u8| 1 <= i ==> !m1.dom().contains(i));
            assume(forall|i: u8| 1 <= i ==> !m2.dom().contains(i));
            assume(m1.dom().contains(0));
            assume(m2.dom().contains(0));
            assume(m1[0] == m2[0]);
            assert(m1 =~= m2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_map_fails1 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(m1: Map<u8, bool>, m2: Map<u8, bool>) {
            assume(forall|i: u8| 1 <= i ==> !m1.dom().contains(i));
            assume(m1.dom().contains(0));
            assume(m2.dom().contains(0));
            assume(m1[0] == m2[0]);
            assert(m1 =~= m2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_map_fails2 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(m1: Map<u8, bool>, m2: Map<u8, bool>) {
            assume(forall|i: u8| 1 <= i ==> !m1.dom().contains(i));
            assume(forall|i: u8| 1 <= i ==> !m2.dom().contains(i));
            assume(m1.dom().contains(0));
            assume(m2.dom().contains(0));
            assert(m1 =~= m2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_seq_not_deep verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) {
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s1[0].len() == 1);
            assume(s2[0].len() == 1);
            assume(s1[0][0] == s2[0][0]);
            assert(s1[0] =~= s2[0]);
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_seq_not_deep_fails verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) {
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s1[0].len() == 1);
            assume(s2[0].len() == 1);
            assume(s1[0][0] == s2[0][0]);
            assert(s1 =~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_seq_deep verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) {
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s1[0].len() == 1);
            assume(s2[0].len() == 1);
            assume(s1[0][0] == s2[0][0]);
            assert(s1 =~~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_seq_deep_fails1 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) {
            assume(s2.len() == 1);
            assume(s1[0].len() == 1);
            assume(s2[0].len() == 1);
            assume(s1[0][0] == s2[0][0]);
            assert(s1 =~~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_seq_deep_fails2 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) {
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s1[0].len() == 1);
            assume(s1[0][0] == s2[0][0]);
            assert(s1 =~~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_seq_deep_fails3 verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) {
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s1[0].len() == 1);
            assume(s2[0].len() == 1);
            assert(s1 =~~= s2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_list verus_code! {
        use vstd::prelude::*;
        #[verifier::ext_equal]
        enum List { Nil, Cons(Seq<u8>, Box<List>), }
        #[verifier::auto_ext_equal()]
        proof fn test_list(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, s4: Seq<u8>) {
            let x = List::Cons(s1, Box::new(List::Cons(s2, Box::new(List::Nil))));
            let y = List::Cons(s3, Box::new(List::Cons(s4, Box::new(List::Nil))));
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s3.len() == 1);
            assume(s4.len() == 1);
            assume(s1[0] == s3[0]);
            assume(s2[0] == s4[0]);
            assert(s2 =~= s4);
            assert(x =~= y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_list_fails1 verus_code! {
        use vstd::prelude::*;
        // omit #[verifier::ext_equal]
        enum List { Nil, Cons(Seq<u8>, Box<List>), }
        #[verifier::auto_ext_equal()]
        proof fn test_list(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, s4: Seq<u8>) {
            let x = List::Cons(s1, Box::new(List::Cons(s2, Box::new(List::Nil))));
            let y = List::Cons(s3, Box::new(List::Cons(s4, Box::new(List::Nil))));
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s3.len() == 1);
            assume(s4.len() == 1);
            assume(s1[0] == s3[0]);
            assume(s2[0] == s4[0]);
            assert(s2 =~= s4);
            // fails without #[verifier::ext_equal]
            assert(x =~= y); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_list_fails2 verus_code! {
        use vstd::prelude::*;
        #[verifier::ext_equal]
        enum List { Nil, Cons(Seq<u8>, Box<List>), }
        #[verifier::auto_ext_equal()]
        proof fn test_list(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, s4: Seq<u8>) {
            let x = List::Cons(s1, Box::new(List::Cons(s2, Box::new(List::Nil))));
            let y = List::Cons(s3, Box::new(List::Cons(s4, Box::new(List::Nil))));
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s3.len() == 1);
            assume(s4.len() == 1);
            assume(s1[0] == s3[0]);
            assume(s2[0] == s4[0]);
            // to avoid trigger matching loops, ext_equal does not traverse recursive data structure fields:
            assert(x =~= y); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_list_deep verus_code! {
        use vstd::prelude::*;
        #[verifier::ext_equal]
        enum List { Nil, Cons(Seq<u8>, Box<List>), }
        #[verifier::auto_ext_equal()]
        proof fn test_list(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, s4: Seq<u8>) {
            let x = List::Cons(s1, Box::new(List::Cons(s2, Box::new(List::Nil))));
            let y = List::Cons(s3, Box::new(List::Cons(s4, Box::new(List::Nil))));
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s3.len() == 1);
            assume(s4.len() == 1);
            assume(s1[0] == s3[0]);
            assume(s2[0] == s4[0]);
            assert(s2 =~~= s4);
            assert(x =~~= y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_list_deep_fail verus_code! {
        use vstd::prelude::*;
        #[verifier::ext_equal]
        enum List { Nil, Cons(Seq<u8>, Box<List>), }
        #[verifier::auto_ext_equal()]
        proof fn test_list(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, s4: Seq<u8>) {
            let x = List::Cons(s1, Box::new(List::Cons(s2, Box::new(List::Nil))));
            let y = List::Cons(s3, Box::new(List::Cons(s4, Box::new(List::Nil))));
            assume(s1.len() == 1);
            assume(s2.len() == 1);
            assume(s3.len() == 1);
            assume(s4.len() == 1);
            assume(s1[0] == s3[0]);
            assume(s2[0] == s4[0]);
            // to avoid trigger matching loops, ext_equal does not traverse recursive data structure fields:
            assert(x =~~= y); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

const SEQ4: &str = verus_code_str! {
    mod m1 {
        use vstd::prelude::*;
        #[verifier::ext_equal]
        pub struct Seq4<A>(A, A, A, A);
        impl<A> Seq4<A> {
            pub closed spec fn spec_index(&self, i: int) -> A {
                if i == 0 {
                    self.0
                } else if i == 1 {
                    self.1
                } else if i == 2 {
                    self.2
                } else {
                    self.3
                }
            }
        }
        // TODO: make this broadcast_forall
        pub proof fn lemma_ext_equal<A>(x: Seq4<A>, y: Seq4<A>)
            ensures
                x =~= y <==> (forall|i: int| 0 <= i < 4 ==> x[i] == y[i]),
        {
            if (forall|i: int| 0 <= i < 4 ==> x[i] == y[i]) {
                assert(x[0] == y[0]);
                assert(x[1] == y[1]);
                assert(x[2] == y[2]);
                assert(x[3] == y[3]);
            }
        }
        // TODO: make this broadcast_forall
        pub proof fn lemma_ext_equal_deep<A>(x: Seq4<A>, y: Seq4<A>)
            ensures
                x =~~= y <==> (forall|i: int| 0 <= i < 4 ==> x[i] =~~= y[i]),
        {
            lemma_ext_equal(x, y);
        }
    }
};

test_verify_one_file! {
    #[test] test_seq4 SEQ4.to_string() + verus_code_str! {
        mod m2 {
            use vstd::prelude::*;
            use crate::m1::*;
            #[verifier::auto_ext_equal()]
            proof fn test(x: Seq4<u8>, y: Seq4<u8>)
                requires
                    x[0] == y[0],
                    x[1] == y[1],
                    x[2] == y[2],
                    x[3] == y[3],
            {
                lemma_ext_equal(x, y);
                assert(x == y);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_seq4_fails SEQ4.to_string() + verus_code_str! {
        mod m2 {
            use vstd::prelude::*;
            use crate::m1::*;
            #[verifier::auto_ext_equal()]
            proof fn test(x: Seq4<u8>, y: Seq4<u8>)
                requires
                    x[0] == y[0],
                    x[1] == y[1],
                    x[2] == y[2],
                    x[3] == y[3],
            {
                assert(x == y); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_std_specs_option_ext_eq verus_code! {
        use vstd::prelude::*;
        #[verifier::auto_ext_equal()]
        proof fn test(a: core::option::Option<Seq<int>>, b: core::option::Option<Seq<int>>)
            requires
                a is Some == b is Some,
                a is Some ==> {
                    &&& a->0.len() == 2
                    &&& b->0.len() == 2
                    &&& a->0[0] == 0
                    &&& b->0[0] == 0
                    &&& a->0[1] == 1
                    &&& b->0[1] == 1
                },
        {
            assert(a =~= b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] heuristic_assert_by verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_ext_equal(assert_by)]
        proof fn test_assert_by(s: Seq<int>) {
            let t = s.push(5).drop_last();
            assert(s == t) by { };
            assert(s == t);
        }

        #[verifier::auto_ext_equal(assert)]
        proof fn test_assert_by_fail(s: Seq<int>) {
            let t = s.push(5).drop_last();
            assert(s == t) by { }; // FAILS
            assert(s == t);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] heuristic_calc verus_code! {
        use vstd::prelude::*;
        use vstd::calc_macro::*;

        #[verifier::auto_ext_equal(assert_by)]
        proof fn test_calc(s: Seq<int>) {
            calc! {
                (==)
                s; {}
                s.push(5).drop_last();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] heuristic_invariant verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_ext_equal(assert, ensures)]
        fn test_invariant1(Ghost(s): Ghost<Seq<int>>) {
            let ghost t = s.push(5).drop_last();
            loop
                invariant s == t, // FAILS
                decreases 1int,
            {
                break;
            }
        }

        #[verifier::auto_ext_equal(invariant)]
        fn test_invariant2(Ghost(s): Ghost<Seq<int>>) {
            let ghost t = s.push(5).drop_last();
            loop
                invariant s == t,
                decreases 1int,
            {
                break;
            }
        }

        #[verifier::auto_ext_equal(invariant)]
        fn test_invariant3(Ghost(s): Ghost<Seq<int>>) {
            let ghost mut t = s.push(5).drop_last();
            for i in 0..3
                invariant s == t,
            {
                proof {
                    t = s.push(6).push(7).drop_last().drop_last();
                }
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] heuristic_ensures verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_ext_equal(assert, assert_by, ensures)]
        proof fn test_ensures(s: Seq<int>) -> (t: Seq<int>)
            ensures s == t,
        {
            let t = s.push(5).drop_last();
            t
        }

        #[verifier::auto_ext_equal(assert, assert_by)]
        proof fn test_ensures(s: Seq<int>) -> (t: Seq<int>)
            ensures s == t, // FAILS
        {
            let t = s.push(5).drop_last();
            t
        }

        #[verifier::auto_ext_equal(ensures)]
        proof fn test_ensures_with_return_stmt(s: Seq<int>) -> (t: Seq<int>)
            ensures s == t,
        {
            let t = s.push(5).drop_last();
            return t;
        }

        trait Tr : Sized {
            proof fn foo(self) -> (s: (Self, Self))
                ensures s.0 == s.1;
        }

        struct X { }

        #[verifier::auto_ext_equal(ensures)]
        impl Tr for X {
            proof fn foo(self) -> (s: (Self, Self))
            {
                (X { }, X { })
            }
        }

        #[verifier::auto_ext_equal(ensures)]
        impl Tr for Seq<int> {
            proof fn foo(self) -> (s: (Self, Self))
            {
                let s = self;
                let t = s.push(5).drop_last();
                (s, t)
            }
        }

        trait Tr2 : Sized {
            proof fn foo(self) -> (s: (Self, Self));
        }

        #[verifier::auto_ext_equal(ensures)]
        impl Tr2 for Seq<int> {
            proof fn foo(self) -> (s: (Self, Self))
                ensures s.0 == s.1
            {
                let s = self;
                let t = s.push(5).drop_last();
                (s, t)
            }
        }
    } => Err(err) => assert_one_fails(err)
}
