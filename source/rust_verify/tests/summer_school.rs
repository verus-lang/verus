// tools/cargo.sh test -p rust_verify --test summer_school
// VERIFY_LOG_IR_PATH="logs" tools/cargo.sh test -p rust_verify --test summer_school -- e05_pas

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -- e01 --

test_verify_one_file! {
    #[test] e01_pass code! {
        fn e01() {
            assert(5 > 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e01_fail code! {
        fn e01() {
            assert(5 < 3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e02 --

test_verify_one_file! {
    #[test] e02_pass code! {
        fn e02(p: int) {
            assert(imply(true, true));
        }
    } => Ok(())
}

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
    #[test] e05_pass E05_SHARED.to_string() + code_str! {
        use set::*;

        #[proof]
        fn try_out_some_set_literals(x: int, y: int)
        {
            // TODO: What should be the literal for mathematical Sets, and the encoding?
            // TODO: This is probably what it would look like for rust HashSet
            // TODO(utaal): not even THIS works
            // assert(Set::<int>::from([1, 3, 8]) == Set::<int>::from([8, 1, 3]));
            let set138: Set<int> = set_empty().insert(1).insert(3).insert(8);
            let set813: Set<int> = set_empty().insert(8).insert(1).insert(3);
            // TODO(utaal): fix sets to allow == syntax for equality
            //assert(set138 == set813);
            assert(set138.ext_equal(set813));

            // NOTE(Chris): The way you encode set literals influences what you can prove about it
            // - axiom for conversion from slice (has quantifiers)
            // - set![8, 1, 3] to sequence of insertions
            // - construct an axiom about that particular literal (most efficient encoding)

            let set7 = set_empty().insert(7);
            let set765 = set_empty().insert(7).insert(6).insert(5);
            assert(has_seven_and_not_nine(set7));

            assert(has_seven_and_not_nine(set765));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] #[ignore] e05_fail E05_SHARED.to_string() + code_str! {
        #[proof]
        fn try_out_some_set_literals(x: int, y: int)
        {
            // TODO literals
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
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

const DIRECTIONS_SHARED_CODE: &str = code_str! {
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
};

#[test]
fn e10_pass() {
    let files = vec![
        ("directions.rs".to_string(), DIRECTIONS_SHARED_CODE.to_string()),
        (
            "test.rs".to_string(),
            code! {
                mod pervasive;
                mod directions;

                use pervasive::*;
                use directions::{Direction, turn_left, turn_right};

                #[proof]
                fn two_wrongs_dont_make_a_right(dir: Direction) {
                    assert(turn_left(turn_left(dir)) == turn_right(turn_right(dir)));
                }
            },
        ),
    ];
    let result = verify_files(files, "test.rs".to_string());
    assert!(result.is_ok());
}

// TODO(jonh): e10_fail

// -- e11 --

test_verify_one_file! {
    #[test] e11_pass code! {
        use set::*;

        #[derive(PartialEq, Eq, Structural)]
        pub enum HAlign { Left, Center, Right }

        #[derive(PartialEq, Eq, Structural)]
        pub enum VAlign { Top, Middle, Bottom }

        #[derive(PartialEq, Eq, Structural)]
        pub struct TextAlign {
            hAlign: HAlign,
            vAlign: VAlign,
        }

        #[derive(PartialEq, Eq, Structural)]
        pub enum GraphicsAlign { Square, Round }

        #[derive(PartialEq, Eq, Structural)]
        pub enum PageElement {
            Text(TextAlign),
            Graphics(GraphicsAlign),
        }

        #[proof]
        fn num_page_elements()
        {
            /*
            ensures([
                exists(|eltSet:Set<HAlign>| eltSet.len() == 3), // bound is tight
                forall(|eltSet:Set<HAlign>| eltSet.len() <= 3), // bound is upper
            ]);
            */

            let maxSet = set_empty().insert(HAlign::Left).insert(HAlign::Center).insert(HAlign::Right);

            let intSet = set_empty().insert(8).insert(4);
            assert(set_empty::<int>().len() == 0);
            // TODO remove: trigger the wrong trigger while waiting for the right trigger
            assert(!set_empty::<int>().contains(1) && set_empty::<int>().insert(1).len() == set_empty::<int>().len() + 1);
            assert(set_empty::<int>().insert(1).len() == set_empty::<int>().len() + 1);

            // TODO remove: more manual triggering of undesirable trigger
            assert(!set_empty().contains(HAlign::Left));
            assert(!set_empty().insert(HAlign::Left).contains(HAlign::Center));
            assert(!set_empty().insert(HAlign::Left).insert(HAlign::Center).contains(HAlign::Right));
            assert(maxSet.len() == 3);

            // TODO(jonh): Complete rest of forall proof.
        }
    } => Ok(())
}

// -- e12 --
//
const LUNCH_SHARED_CODE: &str = code_str! {
    #[allow(unused_imports)] use builtin::*;
    #[allow(unused_imports)] use builtin_macros::*;

    #[derive(PartialEq, Eq, Structural)]
    pub enum Meat { Salami, Ham }

    #[derive(PartialEq, Eq, Structural)]
    pub enum Cheese { Provolone, Swiss, Cheddar, Jack }

    #[derive(PartialEq, Eq, Structural)]
    pub enum Veggie { Olive, Onion, Pepper }

    #[derive(PartialEq, Eq, Structural)]
    pub enum Order {
        Sandwich { meat: Meat, cheese: Cheese },
        Pizza { meat: Meat, veggie: Veggie },
        Appetizer { cheese: Cheese },
    }
};

#[test]
fn e13_pass() {
    let files = vec![
        ("directions.rs".to_string(), DIRECTIONS_SHARED_CODE.to_string()),
        ("lunch.rs".to_string(), LUNCH_SHARED_CODE.to_string()),
        (
            "test.rs".to_string(),
            code! {
                #[allow(unused_imports)] use builtin::*;
                #[allow(unused_imports)] use builtin_macros::*;
                mod pervasive; use pervasive::*;
                mod directions; use directions::{Direction, turn_left, turn_right};
                mod lunch;

                #[spec]
                fn add(x: int, y:int) -> int {
                    x + y
                }

                #[proof]
                fn forall_lemma() {
                    // NB: The original version here fails with:
                    // "Could not automatically infer triggers for this quantifer."
                    // We decided that this use case -- a forall that can be proven but
                    // never used (in any reasonable setting because no way is Chris
                    // gonna trigger on '+'!) -- is extremely rare. Relevant in teaching,
                    // perhaps, but not even in proof debugging.
                    // assert(forall(|x:int| x + x == 2 * x));

                    assert(forall(|x:int| add(x, x) == 2 * x));
                }

                #[proof]
                fn another_forall_lemma() {
                    assert(forall(|dir: Direction| turn_left(turn_left(dir))
                                    == turn_right(turn_right(dir))));
                }

                #[proof]
                fn cheese_take_two() {
                    // TODO(chris) Forall statements!
                }
            },
        ),
    ];
    let result = verify_files(files, "test.rs".to_string());
    assert!(result.is_ok());
}
