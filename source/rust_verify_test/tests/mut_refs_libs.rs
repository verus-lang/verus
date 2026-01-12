#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_option_as_mut_spec ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let mut opt = Some(5);
            let opt_ref_int = opt.as_mut();
            let ref_int = opt_ref_int.unwrap();
            *ref_int = 20;
            assert(opt === Some(20));
        }

        fn test1_fails() {
            let mut opt = Some(5);
            let opt_ref_int = opt.as_mut();
            let ref_int = opt_ref_int.unwrap();
            *ref_int = 20;
            assert(opt === Some(20));
            assert(false); // FAILS
        }

        fn test2() {
            let mut opt = None::<u64>;
            let opt_ref_int = opt.as_mut();
            assert(opt_ref_int === None);
            assert(opt === None);
        }

        fn test2_fails() {
            let mut opt = None::<u64>;
            let opt_ref_int = opt.as_mut();
            assert(opt_ref_int === None);
            assert(opt === None);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] test_vec_index_assign ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut v = vec![1, 2, 3];
            assert(v.len() == 3);
            v[1] = 5;
            assert(v@ =~= seq![1, 5, 3]);
            let y = v[2];
            assert(y == 3);
        }

        fn fails() {
            let mut v = vec![1, 2, 3];
            assert(v.len() == 3);
            v[1] = 5;
            assert(v@ =~= seq![1, 5, 3]);
            let y = v[2];
            assert(y == 3);
            assert(false); // FAILS
        }

        fn test_fields() {
            let mut v = vec![(1, 11), (2, 12), (3, 13)];
            assert(v.len() == 3);
            v[1].0 = 5;
            assert(v@ =~= seq![(1, 11), (5, 12), (3, 13)]);
            let y = v[2].1;
            assert(y == 13);
        }

        fn fails_fields() {
            let mut v = vec![(1, 11), (2, 12), (3, 13)];
            assert(v.len() == 3);
            v[1].0 = 5;
            assert(v@ =~= seq![(1, 11), (5, 12), (3, 13)]);
            let y = v[2].1;
            assert(y == 13);
            assert(false); // FAILS
        }

        fn test_nested() {
            let mut v = vec![
                vec![1, 2, 3],
                vec![4, 5],
                vec![6],
            ];

            v[1][1] = 15;

            assert(v@.len() == 3);
            assert(v@[0]@ =~= seq![1, 2, 3]);
            assert(v@[1]@ =~= seq![4, 15]);
            assert(v@[2]@ =~= seq![6]);
        }

        fn fails_nested() {
            let mut v = vec![
                vec![1, 2, 3],
                vec![4, 5],
                vec![6],
            ];

            v[1][1] = 15;

            assert(v@.len() == 3);
            assert(v@[0]@ =~= seq![1, 2, 3]);
            assert(v@[1]@ =~= seq![4, 15]);
            assert(v@[2]@ =~= seq![6]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] test_vec_index_mut_ref ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_mut_ref() {
            let mut v = vec![1, 2, 3];
            assert(v.len() == 3);
            let r = &mut v[1];
            *r = 5;
            assert(v@ =~= seq![1, 5, 3]);
            let y = v[2];
            assert(y == 3);
        }

        fn fails_mut_ref() {
            let mut v = vec![1, 2, 3];
            assert(v.len() == 3);
            let r = &mut v[1];
            *r = 5;
            assert(v@ =~= seq![1, 5, 3]);
            let y = v[2];
            assert(y == 3);
            assert(false); // FAILS
        }

        fn test_mut_ref_fields() {
            let mut v = vec![(1, 11), (2, 12), (3, 13)];
            assert(v.len() == 3);
            let r = &mut v[1].0;
            *r = 5;
            assert(v@ =~= seq![(1, 11), (5, 12), (3, 13)]);
            let y = v[2].1;
            assert(y == 13);
        }

        fn fails_mut_ref_fields() {
            let mut v = vec![(1, 11), (2, 12), (3, 13)];
            assert(v.len() == 3);
            let r = &mut v[1].0;
            *r = 5;
            assert(v@ =~= seq![(1, 11), (5, 12), (3, 13)]);
            let y = v[2].1;
            assert(y == 13);
            assert(false); // FAILS
        }

        fn test_mut_ref_nested() {
            let mut v = vec![
                vec![1, 2, 3],
                vec![4, 5],
                vec![6],
            ];

            let r = &mut v[1][1];
            *r = 15;

            assert(v@.len() == 3);
            assert(v@[0]@ =~= seq![1, 2, 3]);
            assert(v@[1]@ =~= seq![4, 15]);
            assert(v@[2]@ =~= seq![6]);
        }

        fn fails_mut_ref_nested() {
            let mut v = vec![
                vec![1, 2, 3],
                vec![4, 5],
                vec![6],
            ];

            let r = &mut v[1][1];
            *r = 15;

            assert(v@.len() == 3);
            assert(v@[0]@ =~= seq![1, 2, 3]);
            assert(v@[1]@ =~= seq![4, 15]);
            assert(v@[2]@ =~= seq![6]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] test_index_out_of_bounds ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_out_of_bounds1() {
            let mut v = vec![1, 2, 3];
            v[3] = 5; // FAILS
        }

        fn test_out_of_bounds2() {
            let mut v = vec![1, 2, 3];
            let r = &mut v[3]; // FAILS
        }

        fn test_out_of_bounds3() {
            let mut v = vec![1, 2, 3];
            let r = v[3]; // FAILS
        }

        fn test_out_of_bounds4() {
            let mut v = vec![1, 2, 3];
            let r = &v[3]; // FAILS
        }

        fn test_out_of_bounds_nested() {
            let mut v = vec![
                vec![1, 2, 3],
                vec![4, 5],
                vec![6],
            ];
            v[2][1] = 5; // FAILS
        }

        fn test_out_of_bounds_nested2() {
            let mut v = vec![
                vec![1, 2, 3],
                vec![4, 5],
                vec![6],
            ];
            let m = &mut v[2][1]; // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] test_vec_of_mut_refs ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_vec() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;

            let mut v = vec![&mut a, &mut b, &mut c];

            *v[0] = 10;
            *v[1] = 11;
            *v[2] = 12;

            assert(has_resolved(v[0]));
            assert(has_resolved(v[1]));
            assert(has_resolved(v[2]));

            assert(a == 10);
            assert(b == 11);
            assert(c == 12);
        }

        fn fails_vec() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;

            let mut v = vec![&mut a, &mut b, &mut c];

            *v[0] = 10;
            *v[1] = 11;
            *v[2] = 12;

            assert(has_resolved(v[0]));
            assert(has_resolved(v[1]));
            assert(has_resolved(v[2]));

            assert(a == 10);
            assert(b == 11);
            assert(c == 12);
            assert(false); // FAILS
        }

        fn test_vec2() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let mut v = vec![&mut a, &mut b, &mut c];

            *v[0] = 10;
            *v[1] = 11;
            *v[2] = 12;

            v[2] = &mut d;
            *v[2] = 13;

            assert(has_resolved(v[0]));
            assert(has_resolved(v[1]));
            assert(has_resolved(v[2]));

            assert(a == 10);
            assert(b == 11);
            assert(c == 12);
            assert(d == 13);
        }

        fn fails_vec2() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let mut v = vec![&mut a, &mut b, &mut c];

            *v[0] = 10;
            *v[1] = 11;
            *v[2] = 12;

            v[2] = &mut d;
            *v[2] = 13;

            assert(has_resolved(v[0]));
            assert(has_resolved(v[1]));
            assert(has_resolved(v[2]));

            assert(a == 10);
            assert(b == 11);
            assert(c == 12);
            assert(d == 13);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] test_options_as_mut_slice ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_as_slice_none() {
            let x: Option<u64> = None;
            let s = x.as_slice();
            assert(s@ === seq![]);
        }

        fn test_as_slice_some() {
            let x: Option<u64> = Some(20);
            let s = x.as_slice();
            assert(s@ === seq![20]);
        }

        fn test_as_mut_slice_none() {
            let mut x: Option<u64> = None;
            let s = x.as_mut_slice();
            assert(s@ === seq![]);
            assert(x.is_none());
        }

        fn test_as_mut_slice_some() {
            let mut x: Option<u64> = Some(20);
            let s = x.as_mut_slice();
            assert(s@ === seq![20]);
            s[0] = 30;
            assert(x === Some(30));
        }

        fn fail_as_slice_none() {
            let x: Option<u64> = None;
            let s = x.as_slice();
            assert(s@ === seq![]);
            assert(false); // FAILS
        }

        fn fail_as_slice_some() {
            let x: Option<u64> = Some(20);
            let s = x.as_slice();
            assert(s@ === seq![20]);
            assert(false); // FAILS
        }

        fn fail_as_mut_slice_none() {
            let mut x: Option<u64> = None;
            let s = x.as_mut_slice();
            assert(s@ === seq![]);
            assert(x.is_none());
            assert(false); // FAILS
        }

        fn fail_as_mut_slice_some() {
            let mut x: Option<u64> = Some(20);
            let s = x.as_mut_slice();
            assert(s@ === seq![20]);
            s[0] = 30;
            assert(x === Some(30));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] test_option_insert_and_get_or_insert ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_insert_none() {
            let mut x: Option<u64> = None;
            let r = x.insert(20);
            assert(*r == 20);
            *r = 21;
            assert(x === Some(21));
        }

        fn test_insert_some() {
            let mut x: Option<u64> = Some(5);
            let r = x.insert(20);
            assert(*r == 20);
            *r = 21;
            assert(x === Some(21));
        }

        fn test_get_or_insert_none() {
            let mut x: Option<u64> = None;
            let r = x.get_or_insert(20);
            assert(*r == 20);
            *r = 21;
            assert(x === Some(21));
        }

        fn test_get_or_insert_some() {
            let mut x: Option<u64> = Some(5);
            let r = x.get_or_insert(20);
            assert(*r == 5);
            *r = 21;
            assert(x === Some(21));
        }

        fn fail_insert_none() {
            let mut x: Option<u64> = None;
            let r = x.insert(20);
            assert(*r == 20);
            *r = 21;
            assert(x === Some(21));
            assert(false); // FAILS
        }

        fn fail_insert_some() {
            let mut x: Option<u64> = Some(5);
            let r = x.insert(20);
            assert(*r == 20);
            *r = 21;
            assert(x === Some(21));
            assert(false); // FAILS
        }

        fn fail_get_or_insert_none() {
            let mut x: Option<u64> = None;
            let r = x.get_or_insert(20);
            assert(*r == 20);
            *r = 21;
            assert(x === Some(21));
            assert(false); // FAILS
        }

        fn fail_get_or_insert_some() {
            let mut x: Option<u64> = Some(5);
            let r = x.get_or_insert(20);
            assert(*r == 5);
            *r = 21;
            assert(x === Some(21));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}
