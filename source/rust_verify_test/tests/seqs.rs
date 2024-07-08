#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::seq::*;
        use vstd::seq_lib::*;

        proof fn test_seq() {
            let s1 = Seq::new(5, |i: int| 10 * i);
            assert(s1.len() == 5);
            assert(s1.index(3) == 30);
            let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
            assert(s1 =~= s2);
            assert(s1 === s2);
            let s3 = s2.subrange(1, 4);
            assert(s3.len() == 3);
            let s4 = Seq::<int>::empty().push(10).push(20).push(30);
            assert(s3 =~= s4);
            let s5 = s3.add(s1);
            assert(s5.len() == 8);
            assert(s5.index(1) == 20);
            assert(s5.index(6) == 30);
            let s6 = s4.map(|i: int, a: int| 2 * i + a);
            assert(s6.len() == s4.len());
            assert(s6.index(2) == 34);
            let s7 = seq![true ==> false, false ==> true];
            assert(!s7.index(0));
            assert(s7.index(1));
            let s8: Seq<int> = seq![5; 10];
            assert(s8[0] == 5);
            assert(s8.len() == 10);

            assert(s1.to_set().finite()) by {
                seq_to_set_is_finite(s1);
            }
            assert(s6.to_set().finite()) by {
                seq_to_set_is_finite(s6);
            }
            assert(s7.to_set().finite()) by {
                seq_to_set_is_finite(s7);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        use vstd::seq::*;

        proof fn test_seq() {
            let s1 = Seq::new(5, |i: int| 10 * i);
            assert(s1.len() == 5);
            assert(s1.index(3) == 30);
            assert(s1.index(5) == 50); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        use vstd::seq::*;

        proof fn test_seq() {
            let s1 = Seq::new(5, |i: int| 10 * i);
            assert(s1.len() == 5);
            assert(s1.index(3) == 30);
            let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
            assert(s1 =~= s2);
            assert(s1 === s2);
            let s3 = s2.subrange(1, 4);
            assert(s3.len() == 3);
            let s4 = Seq::<int>::empty().push(10).push(20).push(30);
            assert(s3 =~= s4);
            let s5 = s3.add(s1);
            assert(s5.len() == 8);
            assert(s5.index(1) == 20);
            assert(s5.index(6) == 30);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] auto_extensionality_syntax1 verus_code! {
        use vstd::seq::*;
        use vstd::seq_lib::*;
        proof fn test() {
            let s1 = Seq::new(5, |i: int| 10 * i);
            assert(s1.len() == 5);
            assert(s1.index(3) == 30);
            let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
            assert_seqs_equal!(s1, s2); // old syntax
            assert(s1 == s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] auto_extensionality_syntax2 verus_code! {
        use vstd::seq::*;
        use vstd::seq_lib::*;
        proof fn test() {
            let s1 = Seq::new(5, |i: int| 10 * i);
            assert(s1.len() == 5);
            assert(s1.index(3) == 30);
            let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
            assert_seqs_equal!(s1 == s2); // new syntax
            assert(s1 == s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] filter_lemmas verus_code! {
        use vstd::seq::*;
        use vstd::seq_lib::*;

        proof fn test() {
            // TODO: seq! is currently defined via repeated pushes.
            // This has sometimes led to Z3 timeouts, including in this test.
            // It may be time for a more efficient definition of seq!
            // (for example, via if/else, as shown below).
            //let s1 = seq![10, 20, 30, 45, 55, 70];
            let s1 = Seq::new(6, |i: int|
                if i == 0 { 10 }
                else if i == 1 { 20 }
                else if i == 2 { 30 }
                else if i == 3 { 45 }
                else if i == 4 { 55 }
                else { 70 }
            );
            let s2 = s1.filter(|x: int| x < 40);
            let s3 = seq![90, 100];
            let s4 = s3.filter(|x: int| x < 40);
            // Test for successful broadcast of filter_lemma_broadcast
            assert(forall|i: nat| i < s2.len() ==> s2[i as int] < 40);
            // Test for successful broadcast of filter_distributes_over_add
            assert((s1 + s3).filter(|x: int| x < 40) == (s2 + s4));
            // Test for successful broadcast of push_distributes_over_add
            assert((s2 + s4).push(120) == s2 + s4.push(120));
        }
    } => Ok(())
}
