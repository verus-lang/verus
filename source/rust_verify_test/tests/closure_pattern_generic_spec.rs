#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Demonstrates that str_starts_with_pred/str_ends_with_pred/str_contains_pred/
// str_find_pred/str_rfind_pred's exact guarantees are all recoverable through
// the generic Pattern trait spec once PatternSpecImpl covers FnMut(char) ->
// bool closures too - see PR #2741's discussion with @parno.
test_verify_one_file_with_options! {
    #[test] generic_starts_with_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::PatternSpec;

        fn generic_starts_with_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: bool)
            requires
                s@.len() > 0 ==> pred.requires((s@[0],)),
            ensures
                s@.len() == 0 ==> !res,
                res ==> (s@.len() > 0 && pred.ensures((s@[0],), true)),
                (s@.len() > 0 && !res) ==> pred.ensures((s@[0],), false),
        {
            s.starts_with(pred)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] generic_ends_with_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::PatternSpec;

        fn generic_ends_with_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: bool)
            requires
                s@.len() > 0 ==> pred.requires((s@[s@.len() - 1],)),
            ensures
                s@.len() == 0 ==> !res,
                res ==> (s@.len() > 0 && pred.ensures((s@[s@.len() - 1],), true)),
                (s@.len() > 0 && !res) ==> pred.ensures((s@[s@.len() - 1],), false),
        {
            s.ends_with(pred)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] generic_contains_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::PatternSpec;

        fn generic_contains_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: bool)
            requires
                forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
            ensures
                res ==> exists|i: int| 0 <= i < s@.len() && pred.ensures((#[trigger] s@[i],), true),
                !res ==> forall|i: int| 0 <= i < s@.len() ==> pred.ensures((#[trigger] s@[i],), false),
        {
            let res = s.contains(pred);
            proof {
                if !res {
                    assert forall|i: int| 0 <= i < s@.len() implies pred.ensures(
                        (#[trigger] s@[i],),
                        false,
                    ) by {
                        assert(pred.not_matches_at_witness(s@, i));
                    };
                }
            }
            res
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] generic_find_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::{PatternSpec, StringSliceAdditionalSpecFns};
        use vstd::utf8::{char_at_byte_offset, encode_scalar, encode_utf8, encode_utf8_concat, encode_utf8_push};

        fn generic_find_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: Option<usize>)
            requires
                forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
            ensures
                res is None ==> forall|i: int|
                    0 <= i < s@.len() ==> pred.ensures((#[trigger] s@[i],), false),
                res is Some ==> exists|i: int|
                    0 <= i < s@.len() && pred.ensures((#[trigger] s@[i],), true)
                        && res.unwrap() as int == encode_utf8(s@.subrange(0, i)).len()
                        && forall|j: int| 0 <= j < i ==> pred.ensures((#[trigger] s@[j],), false),
        {
            let res = s.find(pred);
            proof {
                assert(s.spec_bytes() =~= encode_utf8(s@));
                if res is None {
                    assert forall|i: int| 0 <= i < s@.len() implies pred.ensures(
                        (#[trigger] s@[i],),
                        false,
                    ) by {
                        let k = encode_utf8(s@.subrange(0, i)).len() as int;
                        let j = encode_utf8(s@.subrange(0, i + 1)).len() as int;
                        assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i).push(s@[i]));
                        encode_utf8_push(s@.subrange(0, i), s@[i]);
                        assert(s@.subrange(0, i + 1) + s@.subrange(i + 1, s@.len() as int) =~= s@);
                        encode_utf8_concat(s@.subrange(0, i + 1), s@.subrange(i + 1, s@.len() as int));
                        assert(s.spec_bytes().subrange(k, j) =~= encode_scalar(s@[i] as u32));
                        assert(pred.not_matches_at_bytes_witness(s.spec_bytes(), k, j));
                    };
                }
                if res is Some {
                    let byte_i = res.unwrap() as int;
                    assert(exists|byte_j: int|
                        byte_i <= byte_j <= s.spec_bytes().len() as int && pred.matches_at_bytes(
                            s.spec_bytes(),
                            byte_i,
                            byte_j,
                        ));
                    let byte_j = choose|byte_j: int|
                        byte_i <= byte_j <= s.spec_bytes().len() as int && pred.matches_at_bytes(
                            s.spec_bytes(),
                            byte_i,
                            byte_j,
                        );
                    assert(exists|c: char|
                        pred.ensures((c,), true) && s.spec_bytes().subrange(byte_i, byte_j)
                            =~= encode_scalar(c as u32));
                    let c = choose|c: char|
                        pred.ensures((c,), true) && s.spec_bytes().subrange(byte_i, byte_j)
                            =~= encode_scalar(c as u32);
                    vstd::utf8::char_is_scalar(c);
                    let char_i = char_at_byte_offset(s@, byte_i, byte_j, c);

                    assert forall|j: int| 0 <= j < char_i implies pred.ensures(
                        (#[trigger] s@[j],),
                        false,
                    ) by {
                        let k = encode_utf8(s@.subrange(0, j)).len() as int;
                        let jj = encode_utf8(s@.subrange(0, j + 1)).len() as int;
                        assert(s@.subrange(0, j + 1) =~= s@.subrange(0, j).push(s@[j]));
                        encode_utf8_push(s@.subrange(0, j), s@[j]);
                        assert(s@.subrange(0, j + 1) + s@.subrange(j + 1, s@.len() as int) =~= s@);
                        encode_utf8_concat(s@.subrange(0, j + 1), s@.subrange(j + 1, s@.len() as int));
                        assert(s.spec_bytes().subrange(k, jj) =~= encode_scalar(s@[j] as u32));
                        vstd::utf8::lemma_encode_utf8_len_strictly_monotonic(s@, j, char_i);
                        assert(k < byte_i);
                        if j + 1 < s@.len() {
                            vstd::utf8::lemma_encode_utf8_len_strictly_monotonic(
                                s@,
                                j + 1,
                                s@.len() as int,
                            );
                        } else {
                            assert(s@.subrange(0, j + 1) =~= s@);
                        }
                        assert(jj <= s.spec_bytes().len() as int);
                        assert(pred.not_matches_at_bytes_witness(s.spec_bytes(), k, jj));
                    };
                }
            }
            res
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] generic_rfind_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::{PatternSpec, StringSliceAdditionalSpecFns};
        use vstd::utf8::{char_at_byte_offset, encode_scalar, encode_utf8, encode_utf8_concat, encode_utf8_push};

        fn generic_rfind_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: Option<usize>)
            requires
                forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
            ensures
                res is None ==> forall|i: int|
                    0 <= i < s@.len() ==> pred.ensures((#[trigger] s@[i],), false),
                res is Some ==> exists|i: int|
                    0 <= i < s@.len() && pred.ensures((#[trigger] s@[i],), true)
                        && res.unwrap() as int == encode_utf8(s@.subrange(0, i)).len()
                        && forall|j: int| i < j < s@.len() ==> pred.ensures((#[trigger] s@[j],), false),
        {
            let res = s.rfind(pred);
            proof {
                assert(s.spec_bytes() =~= encode_utf8(s@));
                if res is None {
                    assert forall|i: int| 0 <= i < s@.len() implies pred.ensures(
                        (#[trigger] s@[i],),
                        false,
                    ) by {
                        let k = encode_utf8(s@.subrange(0, i)).len() as int;
                        let j = encode_utf8(s@.subrange(0, i + 1)).len() as int;
                        assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i).push(s@[i]));
                        encode_utf8_push(s@.subrange(0, i), s@[i]);
                        assert(s@.subrange(0, i + 1) + s@.subrange(i + 1, s@.len() as int) =~= s@);
                        encode_utf8_concat(s@.subrange(0, i + 1), s@.subrange(i + 1, s@.len() as int));
                        assert(s.spec_bytes().subrange(k, j) =~= encode_scalar(s@[i] as u32));
                        assert(pred.not_matches_at_bytes_witness(s.spec_bytes(), k, j));
                    };
                }
                if res is Some {
                    let byte_i = res.unwrap() as int;
                    assert(exists|byte_j: int|
                        byte_i <= byte_j <= s.spec_bytes().len() as int && pred.matches_at_bytes(
                            s.spec_bytes(),
                            byte_i,
                            byte_j,
                        ));
                    let byte_j = choose|byte_j: int|
                        byte_i <= byte_j <= s.spec_bytes().len() as int && pred.matches_at_bytes(
                            s.spec_bytes(),
                            byte_i,
                            byte_j,
                        );
                    assert(exists|c: char|
                        pred.ensures((c,), true) && s.spec_bytes().subrange(byte_i, byte_j)
                            =~= encode_scalar(c as u32));
                    let c = choose|c: char|
                        pred.ensures((c,), true) && s.spec_bytes().subrange(byte_i, byte_j)
                            =~= encode_scalar(c as u32);
                    vstd::utf8::char_is_scalar(c);
                    let char_i = char_at_byte_offset(s@, byte_i, byte_j, c);

                    assert forall|j: int| char_i < j < s@.len() implies pred.ensures(
                        (#[trigger] s@[j],),
                        false,
                    ) by {
                        let k = encode_utf8(s@.subrange(0, j)).len() as int;
                        let jj = encode_utf8(s@.subrange(0, j + 1)).len() as int;
                        assert(s@.subrange(0, j + 1) =~= s@.subrange(0, j).push(s@[j]));
                        encode_utf8_push(s@.subrange(0, j), s@[j]);
                        assert(s@.subrange(0, j + 1) + s@.subrange(j + 1, s@.len() as int) =~= s@);
                        encode_utf8_concat(s@.subrange(0, j + 1), s@.subrange(j + 1, s@.len() as int));
                        assert(s.spec_bytes().subrange(k, jj) =~= encode_scalar(s@[j] as u32));
                        vstd::utf8::lemma_encode_utf8_len_strictly_monotonic(s@, char_i, j);
                        assert(byte_i < k);
                        if j + 1 < s@.len() {
                            vstd::utf8::lemma_encode_utf8_len_strictly_monotonic(
                                s@,
                                j + 1,
                                s@.len() as int,
                            );
                        } else {
                            assert(s@.subrange(0, j + 1) =~= s@);
                        }
                        assert(jj <= s.spec_bytes().len() as int);
                        assert(pred.not_matches_at_bytes_witness(s.spec_bytes(), k, jj));
                    };
                }
            }
            res
        }
    } => Ok(())
}
