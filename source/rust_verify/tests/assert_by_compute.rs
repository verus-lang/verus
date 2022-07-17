#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] sequence_basics code! {
        use crate::pervasive::seq::*;

        #[proof]
        fn test_seq() {
            assert_by_compute_only({#[spec] let x = true; x});
            assert_by_compute_only(Seq::<u32>::empty().len() == 0);
        }
    } => Ok(())
}

//            assert_by_compute_only(Seq::empty().push(4).len() == 1);
//            assert_by_compute_only(Seq::empty().push(4).last() == 4);
//            assert_by_compute_only(Seq::empty().push(1).push(2).index(1) == 2);
//            assert_by_compute_only(seq![1, 2, 3].len() == 3);
//            assert_by_compute_only(seq![1, 2, 3].index(0) == 1);
//            assert_by_compute_only(seq![1, 2, 3].index(1) == 2);
//            assert_by_compute_only(seq![1, 2, 3].index(2) == 3);
//            assert_by_compute_only(seq![1, 2, 3].last() == 3);
//            assert_by_compute_only(seq![1, 2, 3].update(1, 5).index(0) == 1);
//            assert_by_compute_only(seq![1, 2, 3].update(1, 5).index(1) == 5);
//            assert_by_compute_only(seq![1, 2, 3].update(1, 5).index(2) == 3);
//            assert_by_compute_only(seq![1, 2, 3].add(seq![4, 5]).len() == 5);
//            assert_by_compute_only(seq![1, 2, 3].ext_equal(seq![1].add(seq![2, 3])));
//            assert_by_compute_only(seq![1, 2].subrange(1, 2).ext_equal(seq![2]));
//            assert_by_compute_only(seq![1, 2, 3, 4, 5].subrange(2, 4).ext_equal(seq![3, 4]));
//            assert_by_compute_only(Seq::new(5, |x| x).index(3) == 3);
//            assert_by_compute_only(Seq::new(5, |x| x + x).index(3) == 6);
//            assert_by_compute_only(Seq::new(5, |x| x + x).last() == 8);
//            assert_by_compute_only(Seq::new(5, |x| x + x).subrange(1,4).ext_equal(seq![2, 4, 6]));

//test_verify_one_file! {
//    #[test] test1_fails1 code! {
//        use crate::pervasive::seq::*;
//
//        #[proof]
//        fn test_seq() {
//            let s1 = Seq::new(5, |i: int| 10 * i);
//            assert(s1.len() == 5);
//            assert(s1.index(3) == 30);
//            assert(s1.index(5) == 50); // FAILS
//        }
//    } => Err(err) => assert_one_fails(err)
//}

