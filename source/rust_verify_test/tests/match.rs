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
                            reveal_with_fuel(len::<A>, 2);
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
                            reveal_with_fuel(len::<A>, 2);
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
                            reveal_with_fuel(len::<A>, 2);
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
            if let E::X(u) = e {
                assert(*u as int >= 0);
            } else {
                assert(false);
            }
        }

        fn test_ee(e: &E) {
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
