#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        enum Maybe<A> {
            None,
            Some(A),
        }

        fn test() {
            let x = Maybe::Some(100u64);
            let i = match x {
                Maybe::None => 1,
                Maybe::Some(n) if n < 10 => n + 2,
                Maybe::Some(n) if n < 100 => n + 3,
                Maybe::Some(n) if n < 200 => n + 4,
                Maybe::Some(n) => n + 5,
            };
            assert(i == 104);
            let mut j: u64 = 0;
            match x {
                Maybe::None => { j = 1; }
                Maybe::Some(hd) => { j = hd; }
            }
            assert(j == 100);
            let k: u32 = match Maybe::Some(100u64) {
                Maybe::None => { j = 11; 6 }
                Maybe::Some(h) => { j = h + 1; 7 }
            };
            assert(j == 101);
            assert(k == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        enum Maybe<A> {
            None,
            Some(A),
        }

        fn test() {
            let x = Maybe::Some(100u64);
            let i = match x {
                Maybe::None => 1,
                Maybe::Some(n) if n < 10 => n + 2,
                Maybe::Some(n) if n < 100 => n + 3,
                Maybe::Some(n) if n < 200 => n + 4,
                Maybe::Some(n) => n + 5,
            };
            assert(i == 104);
            let mut j: u64 = 0;
            match x {
                Maybe::None => { j = 1; }
                Maybe::Some(hd) => { j = hd; }
            }
            assert(j == 100);
            let k: u32 = match Maybe::Some(100u64) {
                Maybe::None => { j = 11; 6 }
                Maybe::Some(h) => { j = h + 1; 7 }
            };
            assert(j != 101); // FAILS
            assert(k == 7);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        enum List<A> {
            Nil,
            Cons(A, Box<List<A>>),
        }

        spec fn len<A>(list: &List<A>) -> nat
            decreases list
        {
            match list {
                List::Nil => 0,
                List::Cons(_, tl) => 1 + len(tl),
            }
        }

        fn get_len<A>(list: &List<A>) -> (r: u64)
            requires
                len(list) <= 0xffffffffffffffff,
            ensures
                r == len(list),
        {
            let mut n: u64 = 0;
            let mut done = false;
            let mut iter = list;
            while !done
                invariant
                    len(list) <= 0xffffffffffffffff,
                    n + len(iter) == len(list),
                    done ==> len(iter) == 0,
            {
                match iter {
                    List::Nil => {
                        done = true;
                    }
                    List::Cons(_, tl) => {
                        iter = tl;
                        proof {
                            reveal_with_fuel(len, 2);
                        }
                        n = n + 1;
                    }
                }
            }
            n
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_struct verus_code! {
        enum List<A> {
            Nil,
            Cons { hd: A, tl: Box<List<A>> },
        }

        spec fn len<A>(list: &List<A>) -> nat
            decreases list
        {
            match list {
                List::Nil => 0,
                List::Cons { hd: _, tl } => 1 + len(tl),
            }
        }

        fn get_len<A>(list: &List<A>) -> (r: u64)
            requires
                len(list) <= 0xffffffffffffffff,
            ensures
                r == len(list),
        {
            let mut n: u64 = 0;
            let mut done = false;
            let mut iter = list;
            while !done
                invariant
                    len(list) <= 0xffffffffffffffff,
                    n + len(iter) == len(list),
                    done ==> len(iter) == 0,
            {
                match iter {
                    List::Nil => {
                        done = true;
                    }
                    List::Cons { hd: _, tl } => {
                        iter = tl;
                        proof {
                            reveal_with_fuel(len, 2);
                        }
                        n = n + 1;
                    }
                }
            }
            n
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        enum List<A> {
            Nil,
            Cons(A, Box<List<A>>),
        }

        spec fn len<A>(list: &List<A>) -> nat
            decreases list
        {
            match list {
                List::Nil => 0,
                List::Cons(_, tl) => 1 + len(tl),
            }
        }

        fn get_len<A>(list: &List<A>) -> (r: u64)
            requires
                len(list) <= 0xffffffffffffffff,
            ensures
                r == len(list),
        {
            let mut n: u64 = 0;
            let mut done = false;
            let mut iter = list;
            while !done
                invariant
                    n + len(iter) == len(list),
                    done ==> len(iter) == 0,
            {
                match iter {
                    List::Nil => {
                        done = true;
                    }
                    List::Cons(_, tl) => {
                        iter = tl;
                        proof {
                            reveal_with_fuel(len, 2);
                        }
                        n = n + 1; // FAILS
                        assume(n + len(iter) == len(list));
                    }
                }
            }
            n
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2_unreached verus_code! {
        enum Hand {
            Left,
            Right,
        }

        fn test() -> (ret: u64)
            ensures ret == 10
        {
            match Hand::Left {
                Hand::Left => 10,
                Hand::Right => vstd::pervasive::unreached(),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_unreached_fail verus_code! {
        enum Hand {
            Left,
            Right,
        }

        fn test() -> (ret: u64)
            // ensures ret == 10 // TODO(main_new) add `ensures false` to `unreached` for this?
        {
            match Hand::Right {
                Hand::Left => 10,
                Hand::Right => vstd::pervasive::unreached(), // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

/////////

test_verify_one_file! {
    #[test] test3 verus_code! {
        enum Pair<A, B> {
            Pair(A, B),
        }

        fn test() {
            let Pair::Pair(mut y, z) = Pair::Pair(true, false);
            assert(y);
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_enum_struct verus_code! {
        enum Pair<A, B> {
            Pair { a: A, b: B },
        }

        fn test() {
            let Pair::Pair { a: mut y, b: z } = Pair::Pair { a: true, b: false };
            assert(y);
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_struct verus_code! {
        struct Pair<A, B> { a: A, b: B }

        fn test() {
            let Pair { a: mut y, b: z } = Pair { a: true, b: false };
            assert(y);
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_tuple_struct verus_code! {
        struct Pair<A, B>(A, B);

        fn test() {
            let Pair(mut y, z) = Pair(true, false);
            assert(y);
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_struct_dots verus_code! {
        struct Pair<A, B> { a: A, b: B }

        fn test() {
            let Pair { b: z, .. } = Pair { a: true, b: false };
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_struct_dots_fail verus_code! {
        struct Pair<A, B> { a: A, b: B }

        fn test() {
            let Pair { b: z, .. } = Pair { a: true, b: false };
            assert(z); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3b verus_code! {
        enum Pair<A, B> {
            Pair(A, B),
        }

        fn test() {
            let x = Pair::Pair(true, false);
            let Pair::Pair(mut y, z) = x;
            assert(y);
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_fails verus_code! {
        enum Pair<A, B> {
            Pair(A, B),
        }

        fn test() {
            let Pair::Pair(mut y, z) = Pair::Pair(true, false);
            assert(!y); // FAILS
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3_fails2 verus_code! {
        enum Pair<A, B> {
            Pair(A, B),
        }

        fn test() {
            let Pair::Pair(mut y, z) = Pair::Pair(true, false);
            assert(y);
            y = false;
            assert(y); // FAILS
            assert(!z);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3_fails3 verus_code! {
        enum Pair<A, B> {
            Pair(A, B),
        }

        fn test() {
            let x = Pair::Pair(true, false);
            let Pair::Pair(mut y, z) = x;
            assert(y);
            y = false;
            assert(!y);
            assert(z); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

/////////

test_verify_one_file! {
    #[test] test4 verus_code! {
        fn test() {
            let (mut y, z) = (true, false);
            assert(y);
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4b verus_code! {
        fn test() {
            let x = (true, false);
            let (mut y, z) = x;
            assert(y);
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4_fails verus_code! {
        fn test() {
            let (mut y, z) = (true, false);
            assert(!y); // FAILS
            y = false;
            assert(!y);
            assert(!z);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test4_fails2 verus_code! {
        fn test() {
            let (mut y, z) = (true, false);
            assert(y);
            y = false;
            assert(y); // FAILS
            assert(!z);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test4_fails3 verus_code! {
        fn test() {
            let x = (true, false);
            let (mut y, z) = x;
            assert(y);
            y = false;
            assert(!y);
            assert(z); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test5 verus_code! {
        fn test<A>(t: (bool, u8, A)) {
            let (x, y, z) = t;
            assert(equal((x, y, z), t));
            assert(x == t.0);
            assert(y == t.1);
            assert(equal(z, t.2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test5_fails verus_code! {
        fn test<A>(t: (bool, u8, A)) {
            let (x, y, z) = t;
            assert(equal((x, y, z), t));
            assert(x == t.0);
            assert(y == t.1);
            assert(equal(z, t.2));
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_if_let1 verus_code! {
        enum E { X(u64), Y(bool) }

        proof fn test_ep(e: &E) {
            if let E::X(u) = e {
                assert(*u as int >= 0);
            }
        }

        fn test_ee(e: &E) {
            if let E::X(u) = e {
                assert(*u as int >= 0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_if_let1_fails verus_code! {
        enum E { X(u64), Y(bool) }

        proof fn test_ep(e: &E) {
            if let E::X(u) = e {
                assert(*u as int == 5); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_if_let2 verus_code! {
        enum E { X(u64) }

        proof fn test_ep(e: &E) {
            #[allow(irrefutable_let_patterns)]
            if let E::X(u) = e {
                assert(*u as int >= 0);
            } else {
                assert(false);
            }
        }

        fn test_ee(e: &E) {
            #[allow(irrefutable_let_patterns)]
            if let E::X(u) = e {
                assert(*u as int >= 0);
            } else {
                assert(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_if_let2_fails1 verus_code! {
        enum E { X(u64), Y(bool) }

        proof fn test_ep(e: &E) {
            if let E::X(u) = e {
                assert(*u as int >= 0);
            } else {
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_if_let2_fails2 verus_code! {
        enum E { X(u64), Y(bool) }

        fn test_ee(e: &E) {
            if let E::X(u) = e {
                assert(*u as int >= 0);
            } else {
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_or_patterns verus_code! {
        #[is_variant]
        enum Foo {
            Bar(u64),
            Qux(u64),
            Duck(u64),
        }

        spec fn match_spec(foo: Foo) -> int {
            match foo {
                Foo::Bar(x) | Foo::Qux(x) => x as int + 1,
                Foo::Duck(x) => x as int,
            }
        }

        proof fn test_match_spec(foo: Foo) {
            assert(foo.is_Bar() ==>
                match_spec(foo) === foo.get_Bar_0() as int + 1);
            assert(foo.is_Qux() ==>
                match_spec(foo) === foo.get_Qux_0() as int + 1);
            assert(foo.is_Duck() ==>
                match_spec(foo) === foo.get_Duck_0() as int);
        }

        proof fn test_match_statements(foo: Foo) {
            match foo {
                Foo::Bar(x) | Foo::Qux(x) => {
                    assert(foo.is_Bar() || foo.is_Qux());
                    if foo.is_Bar() {
                        assert(x == foo.get_Bar_0());
                    } else {
                        assert(x == foo.get_Qux_0());
                    }
                }
                Foo::Duck(x) => {
                    assert(foo.is_Duck());
                    assert(x == foo.get_Duck_0());
                }
            }
        }

        proof fn test_match_statements2(foo: Foo) {
            match foo {
                Foo::Bar(x) | Foo::Qux(x) => {
                    assert(false); // FAILS
                }
                _ => { }
            }
        }

        #[is_variant]
        enum Dinosaur {
            TRex(int, int),
            Bird(int, int),
            Brachiosaurus(int, int),
        }

        proof fn test_vars_bound_not_in_same_order(dino: Dinosaur) {
            match dino {
                Dinosaur::TRex(x, y) | Dinosaur::Bird(y, x) => {
                    assert(dino.is_TRex() || dino.is_Bird());
                    if dino.is_TRex() {
                        assert(x == dino.get_TRex_0());
                        assert(y == dino.get_TRex_1());
                    } else {
                        assert(x == dino.get_Bird_1());
                        assert(y == dino.get_Bird_0());
                    }
                }
                Dinosaur::Brachiosaurus(_, _) => {
                    assert(dino.is_Brachiosaurus());
                }
            }
        }

        #[is_variant]
        enum Path {
            Left(Box<Path>),
            Right(Box<Path>),
            Middle(Box<Path>),
            Up(Box<Path>),
            Sideways(Box<Path>),
            Inwards,
        }

        proof fn test_threeway_or(p: Path) {
            match p {
                Path::Left(box q) | q | Path::Right(box q) => {
                    // If 'p' matches multiple, then it should be the first
                    if p.is_Left() {
                        assert(q === *p.get_Left_0());
                    } else {
                        assert(q === p);
                    }
                }
                _ => {
                    // can't get here
                    assert(false);
                }
            }
        }

        proof fn test_threeway_or2(p: Path) {
            match p {
                Path::Left(box q) | Path::Right(box q) | q => {
                    // If 'p' matches multiple, then it should be the first
                    if p.is_Left() {
                        assert(q === *p.get_Left_0());
                    } else if p.is_Right() {
                        assert(q === *p.get_Right_0());
                    } else {
                        assert(q === p);
                    }
                }
                _ => {
                    // can't get here
                    assert(false);
                }
            }
        }

        proof fn test_threeway_or3(p: Path) {
            match p {
                Path::Left(box q) | q | Path::Right(box q) => {
                    if p.is_Left() {
                        assert(p === q); // FAILS
                    }
                }
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] match_single_arm_issue_444 verus_code! {
        enum A { B }
        impl A {
            fn c(self) {
                let (d, e) = match self {
                    A::B => (0, 0),
                };
                assert(d == 0);
            }

            fn c_fail(self) {
                let (d, e) = match self {
                    A::B => (0, 0),
                };
                assert(false); // FAILS
            }


            spec fn d(self) -> (int, int) {
                match self {
                    A::B => (0, 0)
                }
            }

            proof fn test_d(self) {
                let p = self.d();
                assert(p.0 == 0);
            }

            proof fn test_d_fails(self) {
                let p = self.d();
                assert(false); // FAILS
            }

        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] match_arm_returns_poly_issue_523 verus_code! {
        enum Option<A> { Some(A), None }

        #[verifier(external_body)]
        fn unreached<A>() -> A {
            panic!()
        }

        fn test(x: Option<Option<bool>>) -> u8 {
            match x {
                Option::Some(m) =>
                    match m {
                        Option::Some(_) => {
                            return 77;
                        }
                        _ => {
                            unreached()
                        },
                    },
                _ => {
                    unreached()
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dot_dot_patterns verus_code! {
        #[derive(Clone, Copy)]
        struct R { }

        fn test_tuple() {
            let tup = (1, false, 3, R { });

            let (x, .., y) = tup;
            assert(x == 1);
            assert(y == R { });

            let (w, ..) = tup;
            assert(w == 1);

            let (.., b, c, d) = tup;
            assert(b == false);
            assert(c == 3);
            assert(d == R { });

            let (..) = tup;
        }

        enum Foo {
            Bar(u8, bool, u8, R),
        }

        fn test_tuple_ctor() {
            let tup = Foo::Bar(1, false, 3, R { });

            let Foo::Bar(x, .., y) = tup;
            assert(x == 1);
            assert(y == R { });

            let Foo::Bar(w, ..) = tup;
            assert(w == 1);

            let Foo::Bar(.., b, c, d) = tup;
            assert(b == false);
            assert(c == 3);
            assert(d == R { });

            let Foo::Bar(..) = tup;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] at_patterns verus_code! {
        enum Opt<V> {
            Some(V),
            None,
        }
        use Opt::Some;
        use Opt::None;

        fn test1(x: &Opt<Opt<u8>>) {
            match x {
                Some(None) => { }
                Some(y @ Some(z)) => {
                    assert(x == Some(Some(*z)));
                    assert(y == Some(*z));
                }
                None => {
                }
            }
        }

        fn test2(x: &Opt<Opt<u8>>) {
            match x {
                Some(y @ Some(z)) => {
                    assert(x == Some(Some(*z)));
                    assert(y == Some(*z));
                }
                _ => {
                    assert(x is None || x->Some_0 is None);
                }
            }
        }

        fn test3(x: &Opt<Opt<u8>>) {
            match x {
                Some(None) => { }
                Some(y @ Some(z)) => {
                    assert(x == Some(Some(*z)));
                    assert(y == Some(*z));
                    assert(false); // FAILS
                }
                None => {
                }
            }
        }

        spec fn some_fn(x: Opt<Opt<u8>>) -> (u8, Opt<u8>) {
            match x {
                Some(y @ Some(z)) => (z, y),
                Some(y @ None) => (0, y),
                None => (1, None),
            }
        }

        fn test4() {
            assert(some_fn(Some(Some(4))) === (4, Some(4)));
            assert(some_fn(Some(None)) === (0, None));
            assert(some_fn(None) === (1, None));
        }

        fn test5() {
            assert(some_fn(Some(Some(4))) === (4, Some(4)));
            assert(some_fn(Some(None)) === (0, None));
            assert(some_fn(None) === (1, None));
            assert(false); // FAILS
        }

        enum Foo {
            Bar(u8, Opt<u8>),
            Qux(Opt<u8>),
            Zaz(bool),
        }

        proof fn test6(foo: Foo) {
            match foo {
                Foo::Bar(x, y) | Foo::Qux(y @ Some(x)) => {
                    if foo is Bar {
                        assert(x == foo->Bar_0);
                        assert(y == foo->Bar_1);
                    } else if foo is Qux {
                        assert(foo == Foo::Qux(y));
                        assert(foo == Foo::Qux(Some(x)));
                    } else {
                        assert(false);
                    }
                }
                Foo::Qux(z @ _) => {
                    assert(z is None);
                }
                Foo::Zaz(_) => {
                }
            }
        }

        proof fn test7(foo: Foo) {
            match foo {
                Foo::Bar(x, y) | Foo::Qux(y @ Some(x)) => {
                    if foo is Bar {
                        assert(y == foo->Qux_0); // FAILS
                    } else if foo is Qux {
                    } else {
                    }
                }
                _ => { }
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] const_and_literals verus_code! {
        spec fn m_bool_lit(x: bool) -> u64 {
            match x {
                true => 0,
                t => 20,
            }
        }

        proof fn test() {
            assert(m_bool_lit(true) == 0);
            assert(m_bool_lit(false) == 20);
        }

        const I: u64 = 20;

        spec fn m_int_const(x: u64) -> u64 {
            match x {
                I => 0,
                t => t,
            }
        }

        proof fn test2() {
            assert(m_int_const(20) == 0);
            assert(m_int_const(19) == 19);
        }

        fn test3(x: i64) {
            let z = match x {
                7 => 0,
                -16 => 1,
                t => t,
            };

            assert(x == 7 ==> z == 0);
            assert(x == -16 ==> z == 1);
            assert(x != 7 && x != -16 ==> z == x);
        }

        fn test4(x: u64) {
            let z = match x {
                I => 0,
                t => t,
            };

            assert(x == I ==> z == 0);
            assert(x == 20 ==> z == 0);
            assert(x != 20 ==> z == x);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] const_wrong_mode verus_code! {
        spec const I: u64 = 20u64;

        fn test(j: u64) {
            match j {
                I => { }
                _ => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] matching_literal_arms_get_checked verus_code! {
        tracked struct X { }
        proof fn use_x(tracked x: X) { }

        proof fn test(j: u64) {
            let tracked x = X { };
            use_x(x);

            match j {
                20u64 => { }
                30u64 => {
                    use_x(x);
                }
                _ => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value: `x`")
}

test_verify_one_file! {
    #[test] matching_const_arms_get_checked verus_code! {
        const X: u64 = 30;
        const Y: u64 = 32;

        tracked struct X { }
        proof fn use_x(tracked x: X) { }

        proof fn test(j: u64) {
            let tracked x = X { };
            use_x(x);

            match j {
                X => { }
                Y => {
                    use_x(x);
                }
                _ => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value: `x`")
}

test_verify_one_file! {
    #[test] const_pattern_gets_wf_checked verus_code! {
        #[verifier::external]
        const X: u64 = 30;

        fn test(x: u64) {
            match x {
                X => { }
                _ => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external`")
}

test_verify_one_file! {
    #[test] pattern_ranges verus_code! {
        spec fn m_range(x: u64) -> bool {
            match x {
                5u64 .. => true,
                _ => false,
            }
        }

        spec fn m_range2(x: u64) -> bool {
            match x {
                ..=5u64 => true,
                _ => false,
            }
        }

        spec fn m_range3(x: u64) -> bool {
            match x {
                ..5u64 => true,
                _ => false,
            }
        }

        spec fn m_range4(x: u64) -> bool {
            match x {
                3u64..5u64 => true,
                _ => false,
            }
        }

        spec fn m_range5(x: u64) -> bool {
            match x {
                3u64..=5u64 => true,
                _ => false,
            }
        }

        spec fn m_range6(x: u64) -> bool {
            match x {
                3u64..=3u64 => true,
                _ => false,
            }
        }

        spec fn m_range7(x: i64) -> bool {
            match x {
                -4i64..=3i64 => true,
                _ => false,
            }
        }

        const A: u64 = 3;
        const B: u64 = 17;

        spec fn m_range8(x: u64) -> bool {
            match x {
                A..=B => true,
                _ => false,
            }
        }

        proof fn test(x: u64, y: i64) {
            assert(m_range(x) <==> 5 <= x);
            assert(m_range2(x) <==> x <= 5);
            assert(m_range3(x) <==> x < 5);
            assert(m_range4(x) <==> 3 <= x < 5);
            assert(m_range5(x) <==> 3 <= x <= 5);
            assert(m_range6(x) <==> x == 3);
            assert(m_range7(y) <==> -4 <= y <= 3);
            assert(m_range8(x) <==> 3 <= x <= 17);
        }

        fn test_exec(x: u64, y: i64) {
            let a = match x {
                5u64 .. => true,
                _ => false,
            };
            assert(a <==> 5 <= x);

            let b = match x {
                ..=5u64 => true,
                _ => false,
            };
            assert(b <==> x <= 5);

            let c = match x {
                ..5u64 => true,
                _ => false,
            };
            assert(c <==> x < 5);

            let d = match x {
                3u64..5u64 => true,
                _ => false,
            };
            assert(d <==> 3 <= x < 5);

            let e = match x {
                3u64..=5u64 => true,
                _ => false,
            };
            assert(e <==> 3 <= x <= 5);

            let f = match x {
                3u64..=3u64 => true,
                _ => false,
            };
            assert(f <==> x == 3);

            let g = match y {
                -4i64..=3i64 => true,
                _ => false,
            };
            assert(g <==> -4 <= y <= 3);

            let h = match x {
                A..=B => true,
                _ => false,
            };
            assert(h <==> 3 <= x <= 17);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pattern_ranges_bad_range verus_code! {
        spec fn m_range6(x: u64) -> bool {
            match x {
                5u64..=3u64 => true,
                _ => false,
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "lower range bound must be less than or equal to upper")
}

test_verify_one_file! {
    #[test] pattern_ranges_const_mode_error verus_code! {
        spec const A: u64 = 3u64;
        spec const B: u64 = 17u64;

        fn test(x: u64) {
            match x {
                A..=B => { }
                _ => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot read const with mode spec")
}

test_verify_one_file! {
    #[test] pattern_has_both_or_pat_and_if_guard_issue1208 verus_code! {
        fn stuff() {
            let m = match (true, false) {
                (true, a) | (a, false) if a => {
                    // Rust enters this block
                    assert(false); // FAILS
                }
                _ => { }
            };
        }
    //} => Err(err) => assert_one_fails(err)
    } => Err(err) => assert_vir_error_msg(err, "Not supported: pattern containing both an or-pattern (|) and an if-guard")
}
