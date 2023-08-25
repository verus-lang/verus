// tools/cargo.sh test -p rust_verify --test summer_school
// VERIFY_LOG_IR_PATH="logs" tools/cargo.sh test -p rust_verify --test summer_school -- e05_pas

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -- e01 --

test_verify_one_file! {
    #[test] e01_pass verus_code! {
        fn e01() {
            assert(5 > 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e01_fail verus_code! {
        fn e01() {
            assert(5 < 3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e02 --

test_verify_one_file! {
    #[test] e02_pass verus_code! {
        fn e02(p: int) {
            assert(true ==> true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e02_fail verus_code! {
        fn e02(p: int) {
            assert(true ==> false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e03 --

const E03_SHARED: &str = verus_code_str! {
    spec fn double(val: int) -> int {
        2 * val
    }
};

test_verify_one_file! {
    #[test] e03_pass E03_SHARED.to_string() + verus_code_str! {
        proof fn double_is_like_plus(p: int) {
            assert(double(6) == 6 + 6);
            assert(double(-2) == -4);
        }

        proof fn foo4(val: int) {
            assert(double(val) == val + val);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e03_fail E03_SHARED.to_string() + verus_code_str! {
        proof fn double_is_like_plus(p: int) {
            assert(double(-2) == 4); // FAILS
        }

        proof fn foo4(val: int) {
            assert(double(val) == val + val + val); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// -- e04 --

const E04_SHARED: &str = verus_code_str! {
    spec fn at_least_twice_as_big_a(a: int, b: int) -> bool {
        a >= 2 * b
    }

    // this is less interesting in Verus because, contrary to Dafny, there's no predicate keyword
    // in Verus
    spec fn at_least_twice_as_big_b(a: int, b: int) -> bool {
        a >= 2 * b
    }

    spec fn double(a: int) -> int {
        2 * a
    }
};

test_verify_one_file! {
    #[test] e04_pass E04_SHARED.to_string() + verus_code_str! {
        proof fn these_two_predicates_are_equivalent(x: int, y: int)
        {
            assert(at_least_twice_as_big_a(x, y) == at_least_twice_as_big_b(x, y));
        }

        proof fn four_times_is_pretty_big(x: int)
            requires x >= 0
        {
            assert(at_least_twice_as_big_a(double(double(x)), x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e04_fail E04_SHARED.to_string() + verus_code_str! {
        proof fn four_times_is_pretty_big(x: int) {
            assert(at_least_twice_as_big_a(double(double(x)), x)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e05 --

const E05_SHARED: &str = verus_code_str! {
    use vstd::set::*;

    spec fn has_seven_and_not_nine(intset: Set::<int>) -> bool {
        intset.contains(7) && !intset.contains(9)
    }
};

test_verify_one_file! {
    #[test] e05_pass E05_SHARED.to_string() + verus_code_str! {

        proof fn try_out_some_set_literals(x: int, y: int) {
            let set138: Set<int> = set![1, 3, 8];
            let set813: Set<int> = set![8, 1, 3];
            assert(set138 =~= set813);

            let set7 = set![7];
            let set765 = set![7, 6, 5];
            assert(has_seven_and_not_nine(set7));

            assert(has_seven_and_not_nine(set765));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e05_fail E05_SHARED.to_string() + verus_code_str! {
        proof fn try_out_some_set_literals_1(x: int, y: int) {
            assert(has_seven_and_not_nine(set![])); // FAILS
        }

        fn try_out_some_set_literals_2(x: int, y: int) {
            assert(has_seven_and_not_nine(set![7, 9])); // FAILS
        }

        fn try_out_some_set_literals_3(x: int, y: int) {
            assert(has_seven_and_not_nine(set![1, 3, 5, 7, 8, 9, 10])); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

// -- e06 --

const E06_SHARED: &str = verus_code_str! {
    use vstd::set::*;

    spec fn has_four_five_six(intset: Set<int>) -> bool {
        let s = set![4, 5, 6];
        s.subset_of(intset)
    }
};

test_verify_one_file! {
    #[test] e06_pass E06_SHARED.to_string() + verus_code_str! {
        proof fn some_assertions_about_sets() {
            let sadSet: Set<int> = set![1, 2, 4, 6, 7];
            assert(!has_four_five_six(sadSet)) by {
                // NOTE it's interesting that Dafny can get this without the witness
                // maybe dafny is more aggressive in introducing contains when there are set
                // literals around
                assert(!sadSet.contains(5));
            }

            let happySet: Set<int> = set![1, 2, 4, 6, 7, 5];

            assert(has_four_five_six(happySet));

            assert(happySet.difference(set![4, 5, 6]) =~= set![1, 2, 7]);

            assert(has_four_five_six(set![4, 6].union(set![5])));

            assert(happySet.len() == 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e06_fail E06_SHARED.to_string() + verus_code_str! {
        proof fn some_assertions_about_sets() {
            let happySet: Set<int> = set![1, 2, 4, 6, 7, 5];

            assert(happySet.len() == 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e07 --

test_verify_one_file! {
    #[test] e07_pass verus_code! {
        #[allow(unused_imports)]
        use vstd::seq::*;
        #[allow(unused_imports)]
        use vstd::set::*;

        proof fn experiments_with_sequences() {
            let fibo: Seq<int> = seq![1, 1, 2, 3, 5, 8, 13, 21, 34];

            // TODO(utaal) index trait impl Index<Range<nat>> for Seq
            assert(fibo[4] == 5);

            assert(fibo.len() == 9);

            assert(fibo[0] == 1);

            assert(fibo[8] == 34);

            assert(fibo[7] == 21);

            assert(fibo.subrange(2, 4) =~= seq![2, 3]);

            assert(fibo.subrange(0, 3) =~= seq![1, 1, 2]);

            assert(fibo.subrange(7, fibo.len() as int) =~= seq![21, 34]);

            assert(fibo.subrange(2, 5).len() == 3);

            assert(fibo.subrange(5, 6) =~= seq![8]);

            let copy: Seq<int> = fibo;

            let seq_of_sets: Seq<Set::<int>> = seq![set![0], set![0, 1], set![0, 1, 2]];

            assert(seq_of_sets.len() == 3);

            assert(seq_of_sets[1].len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e07_fail verus_code! {
        #[allow(unused_imports)]
        use vstd::seq::*;
        #[allow(unused_imports)]
        use vstd::set::*;

        proof fn experiments_with_sequences_1() {
            let fibo: Seq<int> = seq![1, 1, 2, 3, 5, 8, 13, 21, 34];

            // TODO should this cause a diagnostics warning?
            assert(fibo.index(9) == 55); // FAILS
        }

        proof fn experiments_with_sequences_2() {
            let fibo: Seq<int> = seq![1, 1, 2, 3, 5, 8, 13, 21, 34];

            assert(fibo.subrange(2, 5).len() == 4); // FAILS
        }

        proof fn experiments_with_sequences_3() {
            let seq_of_sets: Seq<Set<int>> = seq![set![0], set![0, 1], set![0, 1, 2]];

            assert(seq_of_sets.index(1).len() == 3); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

// -- e08 --

// TODO factor out type alias

test_verify_one_file! {
    #[test] #[ignore] e08_pass verus_code! {
        #[allow(unused_imports)]
        use vstd::seq::*;
        #[allow(unused_imports)]
        use vstd::set::*;

        // TODO type aliases
        type SeqOfSets = Seq<Set<int>>;

        proof fn try_a_type_synonym()
        {
            let seq_of_sets: SeqOfSets = seq![set![0], set![0, 1], set![0, 1, 2]];

            assert(seq_of_sets.index(1).contains(1));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] #[ignore] e08_fail verus_code! {
        // TODO type aliases
        type SeqOfSets = &[Set::<int>];

        proof fn try_a_type_synonym()
        {
            let seq_of_sets: SeqOfSets = &[set![0], set![0, 1], set![0, 1, 2]];

            assert(seq_of_sets[0].contains(1));
        }
    } => Err(err) => assert_fails(err, 3)
}

// -- e09 --

const E09_SHARED: &str = verus_code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct Point {
        x: int,
        y: int,
    }
};

test_verify_one_file! {
    #[test] e09_pass E09_SHARED.to_string() + verus_code_str! {
        spec fn subtract_points(tip: Point, tail: Point) -> Point {
            Point { x: tip.x - tail.x, y: tip.y - tail.y }
        }

        proof fn point_arithmetic() {
            let a = Point { x: 1, y: 13 };
            let b = Point { x: 2, y: 7 };

            assert(subtract_points(a, b) == Point { x: -1, y: 6 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e09_fail E09_SHARED.to_string() + verus_code_str! {
        spec fn subtract_points(tip: Point, tail: Point) -> Point {
            Point { x: tip.x - tail.x, y: tip.y - tail.x }
        }

        proof fn point_arithmetic() {
            let a = Point { x: 1, y: 13 };
            let b = Point { x: 2, y: 7 };

            assert(subtract_points(a, b) == Point { x: -1, y: 6 }); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// -- e10 --

const DIRECTIONS_SHARED_CODE: &str = verus_code_str! {
    #[allow(unused_imports)] use builtin::*;
    #[allow(unused_imports)] use builtin_macros::*;

    #[derive(PartialEq, Eq, Structural)]
    pub enum Direction {
        North,
        East,
        South,
        West,
    }

    pub open spec fn turn_right(direction: Direction) -> Direction {
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

    proof fn rotation() {
        assert(turn_right(Direction::North) == Direction::East);
    }

    pub open spec fn turn_left(direction: Direction) -> Direction {
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
            verus_code! {
                mod directions;

                use directions::{Direction, turn_left, turn_right};

                proof fn two_wrongs_dont_make_a_right(dir: Direction) {
                    assert(turn_left(turn_left(dir)) == turn_right(turn_right(dir)));
                }
            },
        ),
    ];
    let result = verify_files("e10_pass", files, "test.rs".to_string(), &[]);
    assert!(result.is_ok());
}

// TODO(jonh): e10_fail

// -- e11 --

test_verify_one_file! {
    #[test] e11_pass verus_code! {
        use vstd::set::*;

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

        proof fn num_page_elements()
            ensures
                exists|eltSet:Set<HAlign>| eltSet.len() == 3, // bound is tight
                forall|eltSet:Set<HAlign>| eltSet.len() <= 3, // bound is upper
        {
            let maxSet =  set![HAlign::Left, HAlign::Center, HAlign::Right];

            assert(maxSet.len() == 3);

            assert forall|eltSet: Set<HAlign>| eltSet.len() <= 3 by {
                // Prove eltSet <= maxSet
                assert forall|elt: HAlign| eltSet.contains(elt) implies maxSet.contains(elt) by {
                    if let HAlign::Left = elt { }  // hint at a case analysis
                }

                vstd::set_lib::lemma_len_subset(eltSet, maxSet);
            }
        }
    } => Ok(())
}

// -- e12 --
//
const LUNCH_SHARED_CODE: &str = verus_code_str! {
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
            "#![feature(fmt_internals)]#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]\n".to_string()
                + &verus_code! {
                    #[allow(unused_imports)] use builtin::*;
                    #[allow(unused_imports)] use builtin_macros::*;
                    mod directions; use directions::{Direction, turn_left, turn_right};
                    mod lunch; use lunch::*;

                    spec fn add(x: int, y: int) -> int {
                        x + y
                    }

                    proof fn forall_lemma() {
                        // NB: The original version here fails with:
                        // "Could not automatically infer triggers for this quantifer."
                        // We decided that this use case -- a forall that can be proven but
                        // never used (in any reasonable setting because no way is Chris
                        // gonna trigger on '+'!) -- is extremely rare. Relevant in teaching,
                        // perhaps, but not even in proof debugging.
                        // assert(forall(|x: int| x + x == 2 * x));

                        assert(forall|x: int| add(x, x) == 2 * x);
                    }

                    proof fn another_forall_lemma() {
                        assert(forall|dir: Direction|
                            turn_left(turn_left(dir)) == turn_right(turn_right(dir)));
                    }

                    // TODO(utaal/jon): use utaal's auto-generated predicates
                    impl Order {
                        spec fn is_appetizer(self) -> bool {
                            match self { Order::Appetizer { .. } => true, _ => false }
                        }

                        spec fn is_sandwich(self) -> bool {
                            match self { Order::Sandwich { .. } => true, _ => false }
                        }

                        spec fn get_cheese(self) -> Cheese {
                            // TODO() use Order::*;
                            match self {
                                Order::Sandwich { cheese: cheese, .. } => cheese,
                                Order::Appetizer { cheese: cheese, .. } => cheese,
                                Order::Pizza { .. }  => vstd::pervasive::arbitrary(),
                            }
                        }
                    }

                    proof fn cheese_take_two() {
                        assert forall|o1:Order| o1.is_appetizer() implies
                            exists|o2:Order| o2.is_sandwich() && o1.get_cheese() == o2.get_cheese() by
                        {
                            // ensures(exists(|o2: Order| matches!((o1, o2), (Order::Appetizer { cheese: c1, .. }, Order::Sanwhich { cheese: c2, .. }) if c1 == c2)))

                            // ensures(exists(|o2:Order| o2.is_sandwich() && o1.get_cheese() == o2.get_sandwich().cheese));
                            let o3 = Order::Sandwich { meat: Meat::Ham, cheese: o1.get_cheese() };
                            assert(o3.is_sandwich() /*&& o1.get_cheese() == o3.get_cheese()*/); // witness to ensures.
                        }
                    }
                },
        ),
    ];
    let result = verify_files_vstd("e13_pass", files, "test.rs".to_string(), true, &[]);
    assert!(result.is_ok());
}

// TODO(utaal): fix sets to allow == syntax for equals(set138, set813), but not
// extensional equality?

test_verify_one_file! {
    #[test] e14_pass verus_code! {
        use vstd::set::*;
        use vstd::set_lib::*;
        use vstd::map::*;
        use vstd::seq::*;

        spec fn is_even(x: int) -> bool {
            x / 2 * 2 == x
        }

        proof fn set_comprehension() {
            let modest_evens = Set::new(|x: int| 0 <= x < 10 && is_even(x));
            assert(modest_evens =~= set![0, 2, 4, 6, 8]);

            /* This is beyond summer school, but shows a verus-preferred style */
            let equivalent_evens = set_int_range(0, 10).filter(|x: int| is_even(x));
            assert(modest_evens =~= equivalent_evens);
        }

        proof fn maps() {
            let double_map = map![1 => 2, 2 => 4, 3 => 6, 4 => 8];

            assert(double_map[3] == 6);

            let replace_map = double_map.insert(3, 7);
            assert(replace_map[1] == 2);
            assert(replace_map[2] == 4);
            assert(replace_map[3] == 7);

            /* This is beyond summer school, but shows a verus-preferred style */
            let equivalent_double_map = set_int_range(1, 5).mk_map(|x: int| x * 2);
            assert(equivalent_double_map =~= double_map);
        }

        proof fn map_comprehension() {
            let doubly_map = set_int_range(0, 5).mk_map(|x: int| 2 * x);
            assert(doubly_map[1] == 2);
            assert(doubly_map[4] == 8);
        }

        proof fn seq_comprehension() {
            let evens_in_order = Seq::new(5, |i: int| i * 2);
            assert(evens_in_order[2] == 4);
            assert(evens_in_order =~= seq![0, 2, 4, 6, 8]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e14_fail verus_code! {
        use vstd::set::*;
        use vstd::set_lib::*;
        use vstd::seq::*;
        use vstd::map::*;

        spec fn is_even(x: int) -> bool {
            x / 2 * 2 == x
        }

        proof fn set_comprehension() {
            let modest_evens = Set::new(|x: int| 0 <= x < 10 && is_even(x));
            assert(modest_evens =~= set![0, 2, 4, 8]);   // FAILS
        }

        proof fn maps() {
            let double_map: Map<int, int> = map![1 => 2, 2 => 4, 3 => 6, 4 => 8];

            assert(double_map[3] == 6);

            let replace_map = double_map.insert(3, 7);
            assert(replace_map[1] == 2);
            assert(replace_map[2] == 4);
            assert(replace_map[3] == 6);  // FAILS
        }

        proof fn map_comprehension() {
            let doubly_map = set_int_range(0, 5).mk_map(|x: int| 2 * x);
            assert(doubly_map[1] == 2);
            assert(doubly_map[4] == 4);   // FAILS
        }

        proof fn seq_comprehension() {
            let evens_in_order = Seq::new(5, |i: int| i * 2);
            assert(evens_in_order[2] == 4);
            assert(evens_in_order =~= seq![8, 6, 4, 2, 0]);  // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] e15_pass verus_code! {
        use vstd::set::*;
        use vstd::set_lib::*;

        spec fn is_modest(x: int) -> bool {
            0 <= x < 10
        }

        spec fn is_even(x: int) -> bool {
            x / 2 * 2 == x
        }

        proof fn is_this_set_finite() {
            let modest_evens = Set::new(|x: int| is_modest(x) && is_even(x));
            // In verus, unlike Dafny, it's fine to have infinite sets, but you may want a finite
            // one (say because you're using it as a decreases to well-found an induction).
            let modest_numbers = set_int_range(0, 10);
            // TODO(chris): we need ambient automation for lemmes. lemma_int_range shoud be in a
            // low-risk kit.
            lemma_int_range(0, 10);
            // TODO(chris): don't want to have type annotation on this lemma, but there's an
            // erasure bug.
            lemma_len_subset::<int>(modest_evens, modest_numbers);
            assert(modest_evens.finite());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e15_fail verus_code! {
        use vstd::set::*;

        spec fn is_modest(x: int) -> bool {
            0 <= x < 10
        }

        spec fn is_even(x: int) -> bool {
            x / 2 * 2 == x
        }

        proof fn is_this_set_finite() {
            let modest_evens = Set::new(|x: int| is_modest(x) && is_even(x));
            // Need additional proof to show that this construction is finite.
            assert(modest_evens.finite());  // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] e16_pass verus_code! {
        spec fn is_even(x: int) -> bool {
            x / 2 * 2 == x
        }

        proof fn explain_even_numbers(x: int) -> (twocount: int)
            requires
                is_even(x),
            ensures
                twocount * 2 == x,
        {
            x / 2
        }

        spec fn double(x: int) -> int {
            x * 2
        }

        spec fn alternate_even(x: int) -> bool {
            // TODO(chris): Change no-trigger error message from "Use #[trigger] annotations to
            // manually mark trigger terms instead." to "Consider using a named function for some
            // subexpression to provide a trigger."
            // In Verus, we need a trgger for the exists, so we pull the x*2 expression out into a
            // named fn.
            exists|twocount: int| double(twocount) == x
        }

        proof fn even_definitions_are_equivalent(x: int)
            ensures is_even(x) == alternate_even(x)
        {
            assert(double(x / 2) == x / 2 * 2);   // trigger double.
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e16_fail verus_code! {
        spec fn is_even(x: int) -> bool {
            x / 2 * 2 == x
        }

        proof fn explain_even_numbers(x: int) -> (twocount: int)
            requires
                is_even(x),
            ensures
                twocount * 2 == x,    // FAILS
        {
            x / 3
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] e18_pass verus_code! {
        spec fn fibo(val: nat) -> nat
            // TODO I think Dafny is pretty successful at inferring decreases.
            decreases val
        {
            if val == 0 { 0 }
            else if val == 1 { 1 }
            else { fibo((val - 2) as nat) + fibo((val - 1) as nat) }
        }

        spec fn max_u64_fibo_arg() -> nat {
            20
        }

        proof fn fibo_monotonic(i: nat, j: nat)
            requires
                i <= j,
            ensures
                fibo(i) <= fibo(j),
            decreases j - i
        {
            if i < 2 && j < 2 {
            } else if i == j {
            } else if i == j - 1 {
                reveal_with_fuel(fibo, 2);
                fibo_monotonic(i, (j - 1) as nat);
            } else {
                fibo_monotonic(i, (j - 1) as nat);
                fibo_monotonic(i, (j - 2) as nat);
            }
        }

        fn max_u64_fibo_arg_bound()
            ensures
                forall|i: nat| i < max_u64_fibo_arg() ==> fibo(i) < 7000,
        {
            assert(fibo(20) == 6765) by {
                reveal_with_fuel(fibo, 11);
            }

            // TODO(chris): "Could not automatically infer triggers for this quantifer." but there's fibo
            // RIGHT THERE! Error should say "matching loop" instead.
            // assume(forall(|i:nat| fibo(i) < fibo(i+1)));

            assert forall|i: nat, j: nat| i <= j implies fibo(i) <= fibo(j) by {
                fibo_monotonic(i, j);
            }
        }

        fn fibo_recursive_impl(val: u64) -> (f: u64)
            requires
                val < max_u64_fibo_arg(),
            ensures
                fibo(val as nat) == f,
            decreases val
        {
            assume(val > 1);

            max_u64_fibo_arg_bound();

            if val == 0 { 0 }
            else if val == 1 { 1 }
            else { fibo_recursive_impl(val - 2) + fibo_recursive_impl(val - 1) }
        }

        proof fn check()
            ensures
                fibo(0) == 0,
                fibo(20) == 6765,
        {
            // Dafny gives lots of fuel for application on literals, which makes examples
            // like this go through like magic. Verus needs you to goose the throttle manually.
            reveal_with_fuel(fibo, 11); // Apparently we get 2 recursions for each drop of fuel.
        }

        fn main() {
            let mut x: u64 = 0;
            while x < 20 {
                let f = fibo_recursive_impl(x);
                x = x + 1;
            }
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().find(|x| x.message.contains("decreases checks in exec functions do not guarantee termination of functions with loops or of their callers")).is_some());
    }
}

test_verify_one_file! {
    #[test] e19_pass verus_code! {
        use vstd::view::*;
        use vstd::prelude::*;

        // The summer school uses executable methods that work with nats & ints (here and above in
        // ex17). We dislike that feature of Dafny, because nobody actually wants it.

        fn find_max(int_vec: &Vec<u64>) -> (max_index_rc: usize)
            requires
                int_vec.len() > 0,
            ensures
                max_index_rc < int_vec.len(),
                forall|idx: int|
                    0 <= idx < int_vec.len() ==>
                    int_vec[idx] <= int_vec[max_index_rc as int],
        {
            let mut count: usize = 0;
            let mut max_index: usize = 0;
            while count < int_vec.len()
                invariant
                    max_index < int_vec.len(),
                    forall|prioridx: int|
                        0 <= prioridx < count ==>
                        int_vec[prioridx] <= int_vec[max_index as int],
            {
                if int_vec[max_index] < int_vec[count] {
                    max_index = count;
                }
                count = count + 1;
            }
            max_index
        }
    } => Ok(())
}

// TODO(utaal) consider running the verifier multiple times to emit warnings
// about potential under/over-flow

// TODO prevent panics for underflow/overflow in debug mode

test_verify_one_file! {
    #[test] e20_pass verus_code! {
        use vstd::view::*;
        #[allow(unused_imports)]
        use vstd::seq::*;
        #[allow(unused_imports)]
        use vstd::prelude::*;

        spec fn is_sorted(seq: Seq<u64>) -> bool {
            forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
        }

        fn is_seq_sorted(vec: Vec<u64>) -> (ret: bool)
            ensures
                ret == is_sorted(vec.view()),
        {
            if vec.len() < 2 {
                return true;
            }

            let mut idx: usize = 0;
            while idx < vec.len() - 1
                invariant
                    idx < vec.len(),
                    // dafny had: idx <= vec.len() - 1,
                    // which needs an additional invariant: vec.len() != 0,
                    // because vec.len() == 0 then idx <= arbitrary()
                    forall|i: int, j: int| 0 <= i < j <= idx ==> vec[i] <= vec[j],
            {
                if vec[idx] > vec[idx + 1] { // vec[idx]
                    return false;
                }
                idx = idx + 1;
            }
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] e20_pass_with_ints verus_code! {
        // This version of e20 uses `Seq<int>` in `is_sorted`, which requires a manual conversion

        use vstd::view::*;
        #[allow(unused_imports)]
        use vstd::seq::*;
        #[allow(unused_imports)]
        use vstd::prelude::*;

        spec fn is_sorted(intseq: Seq<int>) -> bool {
            forall|i: int, j: int| 0 <= i < j < intseq.len() ==> intseq[i] <= intseq[j]
        }

        spec fn view_u64(u64seq: Seq<u64>) -> Seq<int> {
            u64seq.map(|_index: int, u: u64| u as int)
                /* TODO(chris): The verifier does not yet support the following Rust feature: pattern Wild (_index as _)*/
        }

        fn is_seq_sorted(intvec: Vec<u64>) -> (out: bool)
            ensures
                out == is_sorted(view_u64(intvec.view())),
        {
            if intvec.len() < 2 {
                true
            } else {
                let mut idx: usize = 0;
                while idx < intvec.len() - 1
                    invariant
                        idx < intvec.len(),
                        forall|i: int, j: int| 0 <= i < j <= idx ==> intvec[i] <= intvec[j]
                {
                    if intvec[idx] > intvec[idx + 1] {
                        // TODO(chris): Maybe there's a way to not need this manual trigger.
                        // Pull this knowledge through the view/view_u64 so it'll trigger the
                        // exists (!forall) of !is_sorted.
                        assert(view_u64(intvec.view())[idx as int] > view_u64(intvec.view())[idx + 1]);
                        return false;
                    }
                    idx = idx + 1;
                }
                true
            }
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] e21_pass verus_code! {
        use vstd::view::*;
        #[allow(unused_imports)]
        use vstd::seq::*;
        #[allow(unused_imports)]
        use vstd::prelude::*;
        #[allow(unused_imports)]
        use vstd::modes::*;

        spec fn is_sorted(intseq: Seq<int>) -> bool {
            forall|i: int, j: int| 0 <= i < j < intseq.len() ==> intseq[i] <= intseq[j]
        }

        spec fn view_u64(u64seq: Seq<u64>) -> Seq<int> {
            u64seq.map(|_index: int, u: u64| u as int)
                /* TODO(chris): The verifier does not yet support the following Rust feature: pattern Wild (_index as _)*/
        }

        fn binary_search(haystack: Vec<u64>, needle: u64) -> (index: usize)
            requires
                is_sorted(view_u64(haystack.view())),
            ensures
                index <= haystack.len(),
                forall|i: int| 0 <= i < index ==> haystack[i] < needle,
                forall|i: int| index <= i < haystack.len() ==> needle <= haystack[i],
        {
            let mut low: usize = 0;
            let mut high: usize = haystack.len();
            while low < high
                invariant
                    is_sorted(view_u64(haystack.view())),   // siiiiiiiigh
                    low <= high,
                    high <= haystack.len(),
                    forall|i:int| 0 <= i < low ==> haystack[i] < needle,
                    forall|i:int| high <= i < haystack.len() ==> needle <= haystack[i],
            {
                let ghost decreases = high - low;
                let mid = low + (high - low) / 2;
                if haystack[mid] < needle {
                    let ghost old_low = low;
                    low = mid + 1;
                    assert forall|i: int| 0 <= i < low implies haystack[i] < needle by {
                        assert(view_u64(haystack.view())[i] <= view_u64(haystack.view())[mid as int]);
                    }
                } else {
                    let ghost old_high = high;
                    high = mid;
                    assert forall|i: int| high < i < haystack.len() implies needle <= haystack[i] by {
                        assert(view_u64(haystack.view())[mid as int] <= view_u64(haystack.view())[i]);
                    }
                }
                assert(high - low < decreases); // Termination check
            }
            low
        }
    } => Ok(())
}

// e22 is in examples/summer_school/chapter-1-22.rs
