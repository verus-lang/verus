#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -- e01 --

test_verify_with_pervasive! {
    #[test] e01_pass code! {
        fn e01() {
            assert(5 > 3);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e01_fail code! {
        fn e01() {
            assert(5 < 3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e02 --

test_verify_with_pervasive! {
    #[test] e02_pass code! {
        fn e02(p: int) {
            assert(imply(true, true));
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e02_fail code! {
        fn e02(p: int) {
            assert(imply(true, false)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e03 --

const E03_SHARED: &str = code_str! {
    #[spec]
    fn double(val: int) -> int {
        2 * val
    }
};

test_verify_with_pervasive! {
    #[test] e03_pass E03_SHARED.to_string() + code_str! {
        #[proof]
        fn double_is_like_plus(p: int) {
            assert(double(6) == 6 + 6);
            assert(double(-2) == -4);
        }

        #[proof]
        fn foo4(val: int) {
            assert(double(val) == val + val);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e03_fail E03_SHARED.to_string() + code_str! {
        #[proof]
        fn double_is_like_plus(p: int) {
            assert(double(-2) == 4); // FAILS
        }

        #[proof]
        fn foo4(val: int) {
            assert(double(val) == val + val + val); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// -- e04 --

const E04_SHARED: &str = code_str! {
    #[spec]
    fn at_least_twice_as_big_a(a: int, b: int) -> bool {
        a >= 2 * b
    }

    // this is less interesting in Verus because, contrary to Dafny, there's no predicate keyword
    // in Verus
    #[spec]
    fn at_least_twice_as_big_b(a: int, b: int) -> bool {
        a >= 2 * b
    }

    #[spec]
    fn double(a: int) -> int {
        2 * a
    }
};

test_verify_with_pervasive! {
    #[test] e04_pass E04_SHARED.to_string() + code_str! {
        #[proof]
        fn these_two_predicates_are_equivalent(x: int, y: int)
        {
            assert(at_least_twice_as_big_a(x, y) == at_least_twice_as_big_b(x, y));
        }

        #[proof]
        fn four_times_is_pretty_big(x: int)
        {
            requires(x >= 0);
            assert(at_least_twice_as_big_a(double(double(x)), x));
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e04_fail E04_SHARED.to_string() + code_str! {
        #[proof]
        fn four_times_is_pretty_big(x: int)
        {
            assert(at_least_twice_as_big_a(double(double(x)), x)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e05 --

const E05_SHARED: &str = code_str! {
    // TODO: Set<> does not exist yet
    #[spec]
    fn has_seven_and_not_nine(intset: Set::<int>) -> bool {
        intset.contains(7) && (!intset.contains(9))
    }
};

test_verify_with_pervasive! {
    #[test] #[ignore] e05_pass E05_SHARED.to_string() + code_str! {
        #[proof]
        fn try_out_some_set_literals(x: int, y: int)
        {
            // TODO: What should be the literal for mathematical Sets, and the encoding?
            // TODO: This is probably what it would look like for rust HashSet
            assert(Set::<int>::from([1, 3, 8]) == Set::<int>::from([8, 1, 3]));
            // NOTE(Chris): The way you encode set literals influences what you can prove about it
            // - axiom for conversion from slice (has quantifiers)
            // - set![8, 1, 3] to sequence of insertions
            // - construct an axiom about that particular literal (most efficient encoding)

            assert(has_seven_and_not_nine(Set::<int>::from([7])));

            assert(has_seven_and_not_nine(Set::<int>::from([7, 6, 5])));
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] #[ignore] e05_fail E05_SHARED.to_string() + code_str! {
        #[proof]
        fn try_out_some_set_literals(x: int, y: int)
        {
            assert(has_seven_and_not_nine(Set::<int>::from([])));

            assert(has_seven_and_not_nine(Set::<int>::from([7, 9])));

            assert(has_seven_and_not_nine(Set::<int>::from([1, 3, 5, 7, 8, 9, 10])));
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e06 --

const E06_SHARED: &str = code_str! {
    // TODO: Set<> does not exist yet
    #[spec]
    fn has_four_five_six(intset: Set::<int>) -> bool {
        Set::<int>::from([6, 5, 4]).is_subset(intset)
    }
};

test_verify_with_pervasive! {
    #[test] #[ignore] e06_pass E06_SHARED.to_string() + code_str! {
        #[proof]
        fn some_assertions_about_sets()
        {
            // TODO literals?
            assert(!has_four_five_six(Set::<int>::from([1, 2, 4, 6, 7])));
            
            let happySet = Set::<int>::from([1, 2, 4, 6, 7, 5]);

            assert(has_four_five_six(happySet));

            assert(happySet.difference(Set::<int>::from([4, 5, 6])) == Set::<int>::from([7, 2, 1]));

            assert(has_four_five_six(Set::<int>::from([4, 6]).union(Set::<int>::from([5]))));

            assert(happySet.len() == 6);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] #[ignore] e06_fail E06_SHARED.to_string() + code_str! {
        #[proof]
        fn some_assertions_about_sets()
        {
            let happySet = Set::<int>::from([1, 2, 4, 6, 7, 5]);

            assert(happySet.len() == 7);
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e07 --

test_verify_with_pervasive! {
    #[test] #[ignore] e07_pass code! {
        #[proof]
        fn experiments_with_sequences()
        {
            // TODO: what is the mathematical sequence type?
            let fibo: &[int] = &[1, 1, 2, 3, 5, 8, 13, 21, 34];

            assert(fibo[4] == 5);

            assert(fibo.len() == 9);

            assert(fibo[0] == 1);

            assert(fibo[8] == 34);

            assert(fibo[7] == 21);

            assert(&fibo[2..4] == &[2, 3]);

            assert(&fibo[..3] == &[1, 1, 2]);

            assert(&fibo[7..] == &[21, 34]);

            assert(fibo[2..5].len() == 3);

            assert(&fibo[5..6] == &[8]);

            let copy: &[int] = fibo;

            let seq_of_sets: &[Set::<int>] = &[Set::<int>::from([0]), Set::<int>::from([0, 1]), Set::<int>::from([0, 1, 2])];

            assert(seq_of_sets.len() == 3);

            assert(seq_of_sets[1].len() == 2);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] #[ignore] e07_fail code! {
        #[proof]
        fn some_assertions_about_sets()
        {
            let fibo: &[int] = &[1, 1, 2, 3, 5, 8, 13, 21, 34];

            assert(fibo[9] == 55); // FAILS

            assert(fibo[2..5].len() == 4); // FAILS

            let seq_of_sets: &[Set::<int>] = &[Set::<int>::from([0]), Set::<int>::from([0, 1]), Set::<int>::from([0, 1, 2])];

            assert(seq_of_sets[1].len() == 3); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

// -- e08 --

// TODO factor out type alias

test_verify_with_pervasive! {
    #[test] #[ignore] e08_pass code! {
        // TODO: do we want to support type renaming
        type SeqOfSets = &[Set::<int>];

        #[proof]
        fn try_a_type_synonym()
        {
            let seq_of_sets: SeqOfSets = &[set![0], set![0, 1], set![0, 1, 2]];

            assert(seq_of_sets[1].contains(1));
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] #[ignore] e08_fail code! {
        // TODO: do we want to support type renaming
        type SeqOfSets = &[Set::<int>];

        #[proof]
        fn try_a_type_synonym()
        {
            let seq_of_sets: SeqOfSets = &[set![0], set![0, 1], set![0, 1, 2]];

            assert(seq_of_sets[0].contains(1));
        }
    } => Err(err) => assert_fails(err, 3)
}

// -- e09 --

const E09_SHARED: &str = code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct Point {
        x: int,
        y: int,
    }
};

test_verify_with_pervasive! {
    #[test] e09_pass E09_SHARED.to_string() + code_str! {
        #[spec]
        fn subtract_points(tip: Point, tail: Point) -> Point
        {
            Point { x: tip.x - tail.x, y: tip.y - tail.y }
        }

        #[proof]
        fn point_arithmetic()
        {
            let a = Point { x: 1, y: 13 };
            let b = Point { x: 2, y: 7 };

            assert(subtract_points(a, b) == Point { x: -1, y: 6 });
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e09_fail E09_SHARED.to_string() + code_str! {
        #[spec]
        fn subtract_points(tip: Point, tail: Point) -> Point
        {
            Point { x: tip.x - tail.x, y: tip.y - tail.x }
        }

        #[proof]
        fn point_arithmetic()
        {
            let a = Point { x: 1, y: 13 };
            let b = Point { x: 2, y: 7 };

            assert(subtract_points(a, b) == Point { x: -1, y: 6 }); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// -- e10 --

#[test]
fn e10_pass() {
    let files = vec![
        ("lib.rs".to_string(), code! {
            extern crate builtin;
            extern crate builtin_macros;

            pub mod pervasive;
            pub mod directions;
        }),
        ("pervasive.rs".to_string(), PERVASIVE.to_string()),
        // TODO: maybe use the prelude here
        ("directions.rs".to_string(), code! {
            #[allow(unused_imports)] use builtin::*;
            #[allow(unused_imports)] use builtin_macros::*;
            use crate::pervasive::*;

            #[derive(PartialEq, Eq, Structural)]
            pub enum Direction {
                North,
                East,
                South,
                West,
            }

            #[spec]
            pub fn turn_right(direction: Direction) -> Direction {
                // TODO do we want the ADT dependent typing that dafny does for enums?
                // NOTE(Chris): there is already an expression in VIR for this
                if direction == Direction::North {
                    Direction::East
                } else if direction == Direction::East {
                    Direction::South
                } else if direction == Direction::South {
                    Direction::West
                } else {
                    Direction::North
                }
            }

            #[proof]
            fn rotation() {
                assert(turn_right(Direction::North) == Direction::East);
            }

            #[spec]
            pub fn turn_left(direction: Direction) -> Direction {
                match direction {
                    Direction::North => Direction::West,
                    Direction::West => Direction::South,
                    Direction::South => Direction::East,
                    Direction::East => Direction::North,
                }
            }
        }),
        ("test.rs".to_string(), code! {
            extern crate builtin;
            extern crate builtin_macros;

            mod pervasive;
            mod directions;

            #[allow(unused_imports)] use builtin::*;
            #[allow(unused_imports)] use builtin_macros::*;
            use crate::pervasive::*;
            use crate::directions::{Direction, turn_left, turn_right};

            #[proof]
            fn two_wrongs_dont_make_a_right(dir: Direction) {
                assert(turn_left(turn_left(dir)) == turn_right(turn_right(dir)));
            }
        }),
    ];
    let result = verify_files(files, "test.rs".to_string());
    assert!(result.is_ok());
}

