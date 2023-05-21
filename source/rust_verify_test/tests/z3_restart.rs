#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_with_bitvec_nlarith verus_code! {
        #[verifier(spinoff_prover)] /* vattr */
        proof fn test6(x: u32, y: u32, z: u32)
            requires
                x < 0xfff,
        {
            assert(x * x + x == x * (x + 1)) by(nonlinear_arith)
                requires(x < 0xfff)
            {
            }
            assert(x * x + x == x * (x + 1));

            assert(x < 0xfff ==> x & y < 0xfff) by(bit_vector);
            assert(x & y < 0xfff);

            assert(x * y * z == y * x * z) by(nonlinear_arith);
        }
    } => Ok(())
}

// From https://github.com/verus-lang/verus/blob/ad92b2a8908a219ec84c277d2bb701934e9a8d9c/source/rust_verify/tests/adts_generics.rs#L1
test_verify_one_file! {
    #[test] test_box_unbox_struct verus_code! {
        #[derive(Eq, PartialEq)]
        struct Thing<A> {
            a: A,
        }

        #[verifier(spinoff_prover)] /* vattr */
        proof fn one(v: int) {
            let t1 = Thing { a: v };
            let t2 = Thing { a: v };
            let a: int = t2.a;
        }

        fn two(v: Thing<u8>) {
            assert(v.a >= 0);
        }
    } => Ok(())
}

// From https://github.com/verus-lang/verus/blob/826e59f3774927f1cc61dd87e39e015b1ec51abf/source/rust_verify/tests/nonlinear.rs#L46
test_verify_one_file! {
    #[test] test_with_nlarith verus_code! {
        #[verifier(nonlinear)] /* vattr */
        // #[verifier(spinoff_prover)] /* vattr */ is implied for nonlinear queries
        proof fn lemma_div_pos_is_pos(x: int, d: int)
            requires
                0 <= x,
                0 < d,
            ensures
                0 <= x / d,
        {
        }
    } => Ok(())
}

// From https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_basic.rs
test_verify_one_file! {
    #[test] test_with_bv verus_code! {
        #[verifier(bit_vector)] /* vattr */
        #[verifier(spinoff_prover)] /* vattr */
        proof fn bit_or32_auto()
            ensures
                forall|a: u32, b: u32| #[trigger] (a | b) == b | a,
                forall|a: u32, b: u32, c:u32| #[trigger] ((a | b) | c) == a | (b | c),
                forall|a: u32| #[trigger] (a | a) == a,
                forall|a: u32| #[trigger] (a | 0) == a,
                forall|a: u32| #[trigger] (a | 0xffff_ffffu32) == 0xffff_ffffu32,
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        #[verifier(spinoff_prover)] /* vattr */
        proof fn test6(b: u32, b2: u32) {
            assert(b * b2 == b2 * b) by(nonlinear_arith);
            assert(b << 2 == mul(b, 4)) by(bit_vector);
            assert(((b << 2) as int) == (b as int) * 4);  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// From https://github.com/verus-lang/verus/blob/826e59f3774927f1cc61dd87e39e015b1ec51abf/source/rust_verify/tests/nonlinear.rs#L46
test_verify_one_file! {
    #[test] test2_fails verus_code! {
        #[verifier(nonlinear)] /* vattr */
        // #[verifier(spinoff_prover)] /* vattr */ is implied for nonlinear queries
        proof fn wrong_lemma_2(x: int, y: int, z: int)
            requires
                x > y,
                3 <= z,
            ensures
                y * z > x // FAILS
        {
        }
    } => Err(e) => assert_one_fails(e)
}

// From https://github.com/verus-lang/verus/blob/21a4774a6fb18295fe5bbcd6abb3e19c6df1e851/source/rust_verify/tests/multiset.rs#L63
test_verify_one_file! {
    #[test] multiset_basics verus_code! {
        use vstd::multiset::*;

        #[verifier(spinoff_prover)] /* vattr */
        pub proof fn commutative<V>(a: Multiset<V>, b: Multiset<V>)
            ensures
                a.add(b) === b.add(a),
        {
            assert(a.add(b) =~= b.add(a));
        }

        #[verifier(spinoff_prover)] /* vattr */
        pub proof fn associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>)
            ensures
                a.add(b.add(c)) ===
                a.add(b).add(c)
        {
            assert(a.add(b.add(c)) =~=
                a.add(b).add(c));
        }

        #[verifier(spinoff_prover)] /* vattr */
        pub proof fn insert2<V>(a: V, b: V)
            ensures
                Multiset::empty().insert(a).insert(b) ===
                Multiset::empty().insert(b).insert(a)
        {
            assert(
                Multiset::empty().insert(a).insert(b) =~=
                Multiset::empty().insert(b).insert(a));
        }

        #[verifier(spinoff_prover)] /* vattr */
        pub proof fn insert2_count<V>(a: V, b: V, c: V)
            requires
                a !== b && b !== c && c !== a,
        {
            assert(Multiset::empty().insert(a).insert(b).count(a) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(b) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(c) == 0);
        }

        #[verifier(spinoff_prover)] /* vattr */
        pub proof fn add_sub_cancel<V>(a: Multiset<V>, b: Multiset<V>)
            ensures
                a.add(b).sub(b) === a,
        {
            assert(a.add(b).sub(b) =~= a);
        }

        #[verifier(spinoff_prover)] /* vattr */
        pub proof fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>)
            requires
                b.le(a),
            ensures
                a.sub(b).add(b) === a
        {
            assert(a.sub(b).add(b) =~= a);
            assert(false) // FAILS
        }

    } => Err(err) => assert_one_fails(err)
}
