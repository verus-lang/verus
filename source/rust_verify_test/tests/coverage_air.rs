// Branch-condition (MC/DC) coverage tests: AIR (air crate) as reached from Verus programs.
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for air/src/parser.rs:702 atom 1 `filter.len() <= 1`
test_verify_one_file_with_options! {
    #[test] air_assert_filter2 ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (\"a\") (f g) true)");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected statement, found: (assert")
}

// Independence pair for air/src/parser.rs:694 atom 1 `is_symbol(x)`
test_verify_one_file_with_options! {
    #[test] air_assign_bad ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assign x# 1)");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected statement, found: (assign x# 1)")
}

// Independence pair for air/src/parser.rs:702 atom 0 `s == "assert"`; air/src/printer.rs:624 atom 5 `a == "assume"`
test_verify_one_file_with_options! {
    #[test] air_assume_labels ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assume (\"a\") () true)");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected statement, found: (assume")
}

// Independence pair for air/src/parser.rs:211 atom 1 `filter.len() <= 1`
test_verify_one_file_with_options! {
    #[test] air_axiom_location_filter2 ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assume (axiom_location (\"a\") (f g) true))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: (\"a\")")
}

// Independence pair for air/src/parser.rs:23 atom 2 `nodes.len() == 3`; air/src/parser.rs:38 atom 1 `nodes[1] == Node::Atom("FloatingP...`
test_verify_one_file_with_options! {
    #[test] air_bitvec_typ_len4 ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (forall ((y (_ BitVec 8 9))) true))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected type, found: (_ BitVec 8 9)")
}

// Independence pair for air/src/parser.rs:372 atom 2 `nodes[1] == Node::Atom("extract"....`
test_verify_one_file_with_options! {
    #[test] air_extract_misspelled ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (= ((_ extrac 3 0) 1) 1))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: ((_ extrac 3 0) 1)")
}

// Independence pair for air/src/parser.rs:38 atom 2 `nodes.len() == 4`
test_verify_one_file_with_options! {
    #[test] air_float_typ_len5 ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (forall ((y (_ FloatingPoint 8 24 1))) true))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected type, found: (_ FloatingPoint 8 24 1)")
}

// Independence pair for air/src/parser.rs:691 atom 1 `is_symbol(x)`
test_verify_one_file_with_options! {
    #[test] air_havoc_bad ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(havoc x#)");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected statement, found: (havoc x#)")
}

// Independence pair for air/src/parser.rs:162 atom 1 `label.ends_with("\"")`
test_verify_one_file_with_options! {
    #[test] air_label_half_quoted ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (\"a\"x) () true)");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected quoted string, found: \"a\"x")
}

// Independence pair for air/src/parser.rs:202 atom 1 `filter.len() <= 1`
test_verify_one_file_with_options! {
    #[test] air_location_filter2 ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (location (\"a\") (f g) true))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: (\"a\")")
}

// Independence pair for air/src/parser.rs:219 atom 1 `is_symbol(snap)`
test_verify_one_file_with_options! {
    #[test] air_old_bad_snap ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (= (old s# x!) 0))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: s#")
}

// Independence pair for air/src/parser.rs:219 atom 2 `is_symbol(x)`
test_verify_one_file_with_options! {
    #[test] air_old_bad_var ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (= (old s x#) 0))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: x#")
}

// Independence pair for air/src/parser.rs:582 atom 1 `qid.is_none()`; air/src/parser.rs:586 atom 0 `consume_skolemid`
test_verify_one_file_with_options! {
    #[test] air_qid_twice ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (forall ((y Int)) (! true :qid a :qid b)))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected quantifier pattern, qid, or skolemid; found b")
}

// Independence pair for air/src/parser.rs:586 atom 1 `skolemid.is_none()`
test_verify_one_file_with_options! {
    #[test] air_skolemid_twice ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (forall ((y Int)) (! true :qid a :skolemid skolem_a :skolemid c)))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected quantifier pattern, qid, or skolemid; found c")
}

// Independence pair for air/src/parser.rs:698 atom 1 `is_symbol(snap)`
test_verify_one_file_with_options! {
    #[test] air_snapshot_bad ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(snapshot s#)");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected statement, found: (snapshot s#)")
}

// Independence pair for air/src/parser.rs:324 atom 1 `nodes[0] == Node::Atom("_".to_str...`; air/src/parser.rs:372 atom 1 `nodes[0] == Node::Atom("_".to_str...`
test_verify_one_file_with_options! {
    #[test] air_to_fp_head_x ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (fp.isZero ((x to_fp 8 24) RNE 1.0)))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: ((x to_fp 8 24) RNE 1.0)")
}

// Independence pair for air/src/parser.rs:353 atom 1; air/src/parser.rs:387 atom 1; air/src/parser.rs:443 atom 1; air/src/parser.rs:450 atom 1
test_verify_one_file_with_options! {
    #[test] air_to_ubv_head_x ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (= ((x fp.to_ubv 8) 1) 1))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: ((x fp.to_ubv 8) 1)")
}

// Independence pair for air/src/parser.rs:23 atom 0 `nodes[0] == Node::Atom("_".to_str...`; air/src/parser.rs:38 atom 0 `nodes[0] == Node::Atom("_".to_str...`
test_verify_one_file_with_options! {
    #[test] air_typ_head_not_underscore ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t(x: int, b: bool) {
            inline_air_stmt("(assert (forall ((y (x BitVec 8))) true))");
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected type, found: (x BitVec 8)")
}

// Independence pair for air/src/var_to_const.rs:24 atom 0 `snapshots.contains_key(snap)`
test_verify_one_file_with_options! {
    #[test] old_in_lifted_lambda ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t() {
            inline_air_stmt("(snapshot S)");
            inline_air_stmt("(assume (= (apply Int (lambda ((y Int)) (old S y)) 3) 3))");
        }
    } => Ok(())
}

// Independence pair for air/src/parser.rs:372 atoms 0, 1, 2; air/src/parser.rs:387 atoms 0, 1, 2, 3; air/src/parser.rs:694 atom 0
test_verify_one_file_with_options! {
    #[test] parser_001_inline_air_exprs_stmts ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        pub struct S { pub a: u32, pub b: int }
        fn t(s: S, x: int, b: bool) {
            let mut k: u8 = 0;
            k = 1;
            proof {
                inline_air_stmt("(assert (= (+ x! 1) (+ 1 x!)))");
                inline_air_stmt("(assert (let ((y 1)) (= (+ y x!) (+ x! 1))))");
                inline_air_stmt("(assert (exists ((y Int)) (= y x!)))");
                inline_air_stmt("(assert (= (_ bv5 8) (_ bv5 8)))");
                inline_air_stmt("(assert (= ((_ extract 3 0) (_ bv5 8)) (_ bv5 4)))");
                inline_air_stmt("(assert (= ((_ zero_extend 4) (_ bv5 4)) (_ bv5 8)))");
                inline_air_stmt("(assert (= ((_ sign_extend 4) (_ bv5 4)) (_ bv5 8)))");
                inline_air_stmt("(assert (= (concat (_ bv0 4) (_ bv5 4)) (_ bv5 8)))");
                inline_air_stmt("(assert (= (ite b! 1 1) 1))");
                inline_air_stmt("(assert (forall ((y Int)) (! (= y y) :pattern ((+ y 1)) :qid q1 :skolemid skolem_q1)))");
                inline_air_stmt("(assert (= 1.5 1.5))");
                inline_air_stmt("(snapshot s1)");
                inline_air_stmt("(assert (= (old s1 x!) x!))");
                inline_air_stmt("(block (assume true) (assert true))");
                inline_air_stmt("(switch (assume b!) (assume (not b!)))");
                inline_air_stmt("(breakable lab (block (assume true) (break lab)))");
                inline_air_stmt("(deadend (assert true))");
                inline_air_stmt("(assert (\"msg\") () true)");
                inline_air_stmt("(assert (location (\"m1\") () true))");
            }
        }
    } => Ok(())
}

// Independence pair for air/src/parser.rs:23 atoms 0, 1, 2; air/src/parser.rs:38 atoms 0, 1, 2; air/src/parser.rs:211 atoms 0, 1; air/src/parser.rs:287 atom 0; air/src/parser.rs:324 atom 2; air/src/parser.rs:340 atoms 0, 1; air/src/parser.rs:353 atoms 0, 1, 2, 3; air/src/parser.rs:450 atoms 0, 1, 2; air/src/parser.rs:691 atoms 0, 1; air/src/parser.rs:694 atoms 0, 1
test_verify_one_file_with_options! {
    #[test] parser_002_inline_air_float_lambda_update ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        pub struct S { pub a: u32, pub b: int }
        fn t(s: S, x: int, b: bool) {
            let mut k: u8 = 0;
            k = 1;
            proof {
                inline_air_stmt("(assert (= ((_ update-field test_crate!S./S/?a) s! 3) ((_ update-field test_crate!S./S/?a) s! 3)))");
                inline_air_stmt("(assert (= (apply Int (lambda ((y Int)) y) 3) 3))");
                inline_air_stmt("(assert (= (choose ((y Int)) (= y 3) y) 3))");
                inline_air_stmt("(assert (= (array 1 2) (array 1 2)))");
                inline_air_stmt("(assert (fp.eq ((_ to_fp 8 24) (_ bv0 32)) ((_ to_fp 8 24) (_ bv0 32))))");
                inline_air_stmt("(assert (fp.isZero ((_ to_fp 8 24) RNE 0.0)))");
                inline_air_stmt("(assert (fp.isZero ((_ to_fp_unsigned 8 24) RTZ (_ bv0 8))))");
                inline_air_stmt("(assert (= ((_ fp.to_sbv 8) RTZ ((_ to_fp 8 24) RNE 1.0)) (_ bv1 8)))");
                inline_air_stmt("(assert (= ((_ fp.to_ubv 8) roundTowardZero ((_ to_fp 8 24) RNE 1.0)) (_ bv1 8)))");
                inline_air_stmt("(assert (fp.eq (fp.roundToIntegral RNA ((_ to_fp 8 24) RNE 1.0)) ((_ to_fp 8 24) RNE 1.0)))");
                inline_air_stmt("(assert (fp.eq (fp.roundToIntegral roundNearestTiesToAway ((_ to_fp 8 24) roundNearestTiesToEven 1.0)) ((_ to_fp 8 24) roundTowardPositive 1.0)))");
                inline_air_stmt("(assert (fp.eq (fp.add roundTowardNegative ((_ to_fp 8 24) RTP 1.0) ((_ to_fp 8 24) RTN 1.0)) (fp.add RTZ ((_ to_fp 8 24) RNA 1.0) ((_ to_fp 8 24) RNE 1.0))))");
                inline_air_stmt("(assert (fp.isNormal (fp (_ bv0 1) (_ bv127 8) (_ bv0 23))))");
                inline_air_stmt("(assert (forall ((f Float32)) (= f f)))");
                inline_air_stmt("(assert (forall ((f Float16)) (= f f)))");
                inline_air_stmt("(assert (forall ((f Float64)) (= f f)))");
                inline_air_stmt("(assert (forall ((f Float128)) (= f f)))");
                inline_air_stmt("(assert (forall ((f (_ FloatingPoint 5 7))) (= f f)))");
                inline_air_stmt("(assert (forall ((f (_ BitVec 8))) (= f f)))");
                inline_air_stmt("(assert (forall ((f Real)) (= f f)))");
                inline_air_stmt("(assert (forall ((f Fun)) (= f f)))");
                inline_air_stmt("(assert (forall ((y Int) (z Int)) ((_ linear-order 0) y y)))");
                inline_air_stmt("(assert (forall ((y Int)) ((_ tree-order 0) y y)))");
                inline_air_stmt("(assert (forall ((y Int)) ((_ piecewise-linear-order 0) y y)))");
                inline_air_stmt("(havoc k@)");
                inline_air_stmt("(assign k@ 3)");
                inline_air_stmt("(assert (= k@ 3))");
                inline_air_stmt("(assert (\"msg\") (filt) true)");
                inline_air_stmt("(assert (location (\"m1\") (filt) true))");
                inline_air_stmt("(assume (axiom_location (\"m1\") () true))");
            }
        }
    } => Ok(())
}

// Independence pair for air/src/parser.rs:162 atom 0 `label.starts_with("\"")`
test_verify_one_file_with_options! {
    #[test] parser_066_label_unquoted ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        pub struct S { pub a: u32, pub b: int }
        fn t(s: S, x: int, b: bool) {
            let mut k: u8 = 0;
            k = 1;
            proof {
                inline_air_stmt("(assert (msg) () true)");
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected quoted string, found: msg")
}

// Independence pair for air/src/parser.rs:340 atom 1 `signed`
test_verify_one_file_with_options! {
    #[test] parser_072_to_fp_unsigned_one_arg ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        pub struct S { pub a: u32, pub b: int }
        fn t(s: S, x: int, b: bool) {
            let mut k: u8 = 0;
            k = 1;
            proof {
                inline_air_stmt("(assert (fp.isZero ((_ to_fp_unsigned 8 24) (_ bv0 32))))");
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Invalid inline AIR statement: expected expression, found: ((_ to_fp_unsigned 8 24) (_ bv0 32))")
}

// Independence pair for air/src/typecheck.rs:166 atom 0 `arg_typs.len() > 0`
test_verify_one_file_with_options! {
    #[test] plus_no_args_unsat_ctx ["-V allow-inline-air"] => verus_code! {
        use vstd::prelude::*;

        proof fn t()
            requires false,
        {
            inline_air_stmt("(assume (= (+) 0))");
        }
    } => Ok(())
}
