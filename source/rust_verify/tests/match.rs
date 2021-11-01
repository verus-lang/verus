#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_with_pervasive! {
    #[test] test1 code! {
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

test_verify_with_pervasive! {
    #[test] test1_fails code! {
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

test_verify_with_pervasive! {
    #[test] test2 code! {
        enum List<A> {
            Nil,
            Cons(A, Box<List<A>>),
        }

        #[spec]
        fn len<A>(list: &List<A>) -> nat {
            decreases(list);
            match list {
                List::Nil => 0,
                List::Cons(_, tl) => 1 + len(tl),
            }
        }

        fn get_len<A>(list: &List<A>) -> u64 {
            requires(len(list) <= 0xffffffffffffffff);
            ensures(|r: u64| r == len(list));

            let mut n: u64 = 0;
            let mut done = false;
            let mut iter = list;
            while !done {
                invariant([
                    len(list) <= 0xffffffffffffffff,
                    n + len(iter) == len(list),
                    imply(done, len(iter) == 0),
                ]);

                match iter {
                    List::Nil => {
                        done = true;
                    }
                    List::Cons(_, tl) => {
                        iter = tl;
                        n = n + 1;
                    }
                }
            }
            n
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test2_fails code! {
        enum List<A> {
            Nil,
            Cons(A, Box<List<A>>),
        }

        #[spec]
        fn len<A>(list: &List<A>) -> nat {
            decreases(list);
            match list {
                List::Nil => 0,
                List::Cons(_, tl) => 1 + len(tl),
            }
        }

        fn get_len<A>(list: &List<A>) -> u64 {
            requires(len(list) <= 0xffffffffffffffff);
            ensures(|r: u64| r == len(list));

            let mut n: u64 = 0;
            let mut done = false;
            let mut iter = list;
            while !done {
                invariant([
                    n + len(iter) == len(list), // FAILS
                    imply(done, len(iter) == 0),
                ]);

                match iter {
                    List::Nil => {
                        done = true;
                    }
                    List::Cons(_, tl) => {
                        iter = tl;
                        n = n + 1;
                    }
                }
            }
            n
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test3 code! {
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

test_verify_with_pervasive! {
    #[test] test3b code! {
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

test_verify_with_pervasive! {
    #[test] test3_fails code! {
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

test_verify_with_pervasive! {
    #[test] test3_fails2 code! {
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

test_verify_with_pervasive! {
    #[test] test3_fails3 code! {
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
