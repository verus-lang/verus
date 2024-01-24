use crate::ast::Path;
use crate::def::*;
use crate::sst_to_air::path_to_air_ident;
use air::ast::Ident;
use air::printer::{macro_push_node, str_to_node};
use air::{node, nodes, nodes_vec};
use sise::Node;

pub struct PreludeConfig {
    pub arch_word_bits: crate::ast::ArchWordBits,
}

pub(crate) fn prelude_nodes(config: PreludeConfig) -> Vec<Node> {
    #[allow(non_snake_case)]
    let FuelId = str_to_node(FUEL_ID);
    #[allow(non_snake_case)]
    let Fuel = str_to_node(FUEL_TYPE);
    let zero = str_to_node(ZERO);
    let succ = str_to_node(SUCC);
    let fuel_bool = str_to_node(FUEL_BOOL);
    let fuel_bool_default = str_to_node(FUEL_BOOL_DEFAULT);
    let fuel_defaults = str_to_node(FUEL_DEFAULTS);
    let u_hi = str_to_node(U_HI);
    let i_lo = str_to_node(I_LO);
    let i_hi = str_to_node(I_HI);
    let u_clip = str_to_node(U_CLIP);
    let i_clip = str_to_node(I_CLIP);
    let nat_clip = str_to_node(NAT_CLIP);
    let u_inv = str_to_node(U_INV);
    let i_inv = str_to_node(I_INV);
    let arch_size = str_to_node(ARCH_SIZE);
    #[allow(non_snake_case)]
    let Add = str_to_node(ADD);
    #[allow(non_snake_case)]
    let Sub = str_to_node(SUB);
    #[allow(non_snake_case)]
    let Mul = str_to_node(MUL);
    #[allow(non_snake_case)]
    let EucDiv = str_to_node(EUC_DIV);
    #[allow(non_snake_case)]
    let EucMod = str_to_node(EUC_MOD);
    let check_decrease_int = str_to_node(CHECK_DECREASE_INT);
    let check_decrease_height = str_to_node(CHECK_DECREASE_HEIGHT);
    let height = str_to_node(HEIGHT);
    let height_le = nodes!(_ partial-order 0);
    let height_lt = str_to_node(HEIGHT_LT);
    let height_rec_fun = str_to_node(HEIGHT_REC_FUN);
    let closure_req = str_to_node(CLOSURE_REQ);
    let closure_ens = str_to_node(CLOSURE_ENS);
    #[allow(non_snake_case)]
    let Poly = str_to_node(POLY);
    #[allow(non_snake_case)]
    let Height = str_to_node(T_HEIGHT);
    let box_int = str_to_node(BOX_INT);
    let box_bool = str_to_node(BOX_BOOL);
    let unbox_int = str_to_node(UNBOX_INT);
    let unbox_bool = str_to_node(UNBOX_BOOL);

    let box_strslice = str_to_node(BOX_STRSLICE);
    let unbox_strslice = str_to_node(UNBOX_STRSLICE);

    let box_char = str_to_node(BOX_CHAR);
    let unbox_char = str_to_node(UNBOX_CHAR);

    let typ = str_to_node(TYPE);
    let type_id_bool = str_to_node(TYPE_ID_BOOL);
    let type_id_int = str_to_node(TYPE_ID_INT);
    let type_id_char = str_to_node(TYPE_ID_CHAR);
    let type_id_nat = str_to_node(TYPE_ID_NAT);
    let type_id_uint = str_to_node(TYPE_ID_UINT);
    let type_id_sint = str_to_node(TYPE_ID_SINT);
    let type_id_const_int = str_to_node(TYPE_ID_CONST_INT);
    let decoration = str_to_node(DECORATION);
    let decorate_nil = str_to_node(DECORATE_NIL);
    let decorate_ref = str_to_node(DECORATE_REF);
    let decorate_mut_ref = str_to_node(DECORATE_MUT_REF);
    let decorate_box = str_to_node(DECORATE_BOX);
    let decorate_rc = str_to_node(DECORATE_RC);
    let decorate_arc = str_to_node(DECORATE_ARC);
    let decorate_ghost = str_to_node(DECORATE_GHOST);
    let decorate_tracked = str_to_node(DECORATE_TRACKED);
    let decorate_never = str_to_node(DECORATE_NEVER);
    let has_type = str_to_node(HAS_TYPE);
    let as_type = str_to_node(AS_TYPE);
    let mk_fun = str_to_node(MK_FUN);
    let const_int = str_to_node(CONST_INT);
    let ext_eq = str_to_node(EXT_EQ);

    let uint_xor = str_to_node(UINT_XOR);
    let uint_and = str_to_node(UINT_AND);
    let uint_or = str_to_node(UINT_OR);
    let uint_shr = str_to_node(UINT_SHR);
    let uint_shl = str_to_node(UINT_SHL);
    let uint_not = str_to_node(UINT_NOT);
    let singular_mod = str_to_node(SINGULAR_MOD);

    let strslice = str_to_node(STRSLICE);
    #[allow(non_snake_case)]
    let Char = str_to_node(CHAR);

    let strslice_is_ascii = str_to_node(STRSLICE_IS_ASCII);
    let strslice_len = str_to_node(STRSLICE_LEN);
    let strslice_get_char = str_to_node(STRSLICE_GET_CHAR);
    let type_id_strslice = str_to_node(TYPE_ID_STRSLICE);
    let new_strlit = str_to_node(STRSLICE_NEW_STRLIT);
    let from_strlit = str_to_node(STRSLICE_FROM_STRLIT);

    let from_unicode = str_to_node(CHAR_FROM_UNICODE);
    let to_unicode = str_to_node(CHAR_TO_UNICODE);

    let type_id_array = str_to_node(TYPE_ID_ARRAY);
    let type_id_slice = str_to_node(TYPE_ID_SLICE);

    nodes_vec!(
        // Fuel
        (declare-sort [FuelId] 0)
        (declare-sort [Fuel] 0)
        (declare-const [zero] [Fuel])
        (declare-fun [succ] ([Fuel]) [Fuel])
        (declare-fun [fuel_bool] ([FuelId]) Bool)
        (declare-fun [fuel_bool_default] ([FuelId]) Bool)
        (declare-const [fuel_defaults] Bool)
        (axiom (=> [fuel_defaults]
            (forall ((id [FuelId])) (!
                (= ([fuel_bool] id) ([fuel_bool_default] id))
                :pattern (([fuel_bool] id))
                :qid prelude_fuel_defaults
                :skolemid skolem_prelude_fuel_defaults
            ))
        ))

        // Chars
        (declare-sort [Char] 0)
        (declare-fun [from_unicode] (Int) [Char])
        (declare-fun [to_unicode] ([Char]) Int)

        // Strings
        (declare-sort [strslice] 0)
        (declare-fun [strslice_is_ascii] ([strslice]) Bool)
        (declare-fun [strslice_len] ([strslice]) Int)
        (declare-fun [strslice_get_char] ([strslice] Int) [Char])
        (declare-fun [new_strlit] (Int) [strslice])
        (declare-fun [from_strlit] ([strslice]) Int)

        // Polymorphism
        (declare-sort [Poly] 0)
        (declare-sort [Height] 0)
        (declare-fun [box_int] (Int) [Poly])
        (declare-fun [box_bool] (Bool) [Poly])
        (declare-fun [unbox_int] ([Poly]) Int)
        (declare-fun [unbox_bool] ([Poly]) Bool)
        (declare-fun [box_strslice] ([strslice]) [Poly])
        (declare-fun [unbox_strslice] ([Poly]) [strslice])
        (declare-fun [box_char] ([Char]) [Poly])
        (declare-fun [unbox_char] ([Poly]) [Char])
        (declare-sort [typ] 0)
        (declare-const [type_id_bool] [typ])
        (declare-const [type_id_int] [typ])
        (declare-const [type_id_nat] [typ])
        (declare-const [type_id_strslice] [typ])
        (declare-const [type_id_char] [typ])
        (declare-fun [type_id_uint] (Int) [typ])
        (declare-fun [type_id_sint] (Int) [typ])
        (declare-fun [type_id_const_int] (Int) [typ])
        (declare-sort [decoration] 0)
        (declare-const [decorate_nil] [decoration])
        (declare-fun [decorate_ref] ([decoration]) [decoration])
        (declare-fun [decorate_mut_ref] ([decoration]) [decoration])
        (declare-fun [decorate_box] ([decoration]) [decoration])
        (declare-fun [decorate_rc] ([decoration]) [decoration])
        (declare-fun [decorate_arc] ([decoration]) [decoration])
        (declare-fun [decorate_ghost] ([decoration]) [decoration])
        (declare-fun [decorate_tracked] ([decoration]) [decoration])
        (declare-fun [decorate_never] ([decoration]) [decoration])
        (declare-fun [type_id_array] ([decoration] [typ] [decoration] [typ]) [typ])
        (declare-fun [type_id_slice] ([decoration] [typ]) [typ])
        (declare-fun [has_type] ([Poly] [typ]) Bool)
        (declare-fun [as_type] ([Poly] [typ]) [Poly])
        (declare-fun [mk_fun] (Fun) Fun)
        (declare-fun [const_int] ([typ]) Int)
        (axiom (forall ((i Int)) (!
            (= i ([const_int] ([type_id_const_int] i)))
            :pattern (([type_id_const_int] i))
            :qid prelude_type_id_const_int
            :skolemid skolem_prelude_type_id_const_int
        )))
        (axiom (forall ((b Bool)) (!
            ([has_type] ([box_bool] b) [type_id_bool])
            :pattern (([has_type] ([box_bool] b) [type_id_bool]))
            :qid prelude_has_type_bool
            :skolemid skolem_prelude_has_type_bool
        )))
        (axiom (forall ((x [Poly]) (t [typ])) (!
            (and
                ([has_type] ([as_type] x t) t)
                (=>
                    ([has_type] x t)
                    (= x ([as_type] x t))
                )
            )
            :pattern (([as_type] x t))
            :qid prelude_as_type
            :skolemid skolem_prelude_as_type
        )))
        (axiom (forall ((x Fun)) (!
            (= (mk_fun x) x)
            :pattern (([mk_fun] x))
            :qid prelude_mk_fun
            :skolemid skolem_prelude_mk_fun
        )))
        (axiom (forall ((x Bool)) (!
            (= x ([unbox_bool] ([box_bool] x)))
            :pattern (([box_bool] x))
            :qid prelude_unbox_box_bool
            :skolemid skolem_prelude_unbox_box_bool
        )))
        (axiom (forall ((x Int)) (!
            (= x ([unbox_int] ([box_int] x)))
            :pattern (([box_int] x))
            :qid prelude_unbox_box_int
            :skolemid skolem_prelude_unbox_box_int
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_bool])
                (= x ([box_bool] ([unbox_bool] x)))
            )
            :pattern (([has_type] x [type_id_bool]))
            :qid prelude_box_unbox_bool
            :skolemid skolem_prelude_box_unbox_bool
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_int])
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x [type_id_int]))
            :qid prelude_box_unbox_int
            :skolemid skolem_prelude_box_unbox_int
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_nat])
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x [type_id_nat]))
            :qid prelude_box_unbox_nat
            :skolemid skolem_prelude_box_unbox_nat
        )))
        (axiom (forall ((bits Int) (x [Poly])) (!
            (=>
                ([has_type] x ([type_id_uint] bits))
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x ([type_id_uint] bits)))
            :qid prelude_box_unbox_uint
            :skolemid skolem_prelude_box_unbox_uint
        )))
        (axiom (forall ((bits Int) (x [Poly])) (!
            (=>
                ([has_type] x ([type_id_sint] bits))
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x ([type_id_sint] bits)))
            :qid prelude_box_unbox_sint
            :skolemid skolem_prelude_box_unbox_sint
        )))

        // String literals
        (axiom (forall ((x Int)) (!
            (= ([from_strlit] ([new_strlit] x)) x)
            :pattern (([new_strlit] x))
            :qid prelude_strlit_injective
            :skolemid skolem_prelude_strlit_injective
        )))

        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_strslice])
                (= x ([box_strslice] ([unbox_strslice] x)))
            )
            :pattern (([has_type] x [type_id_strslice]))
            :qid prelude_box_unbox_strslice
            :skolemid skolem_prelude_box_unbox_strslice
        )))
        (axiom (forall ((x [strslice])) (!
            (= x ([unbox_strslice] ([box_strslice] x)))
            :pattern (([box_strslice] x))
            :qid prelude_unbox_box_strslice
            :skolemid skolem_prelude_unbox_box_strslice
        )))
        (axiom (forall ((x [strslice])) (!
            ([has_type] ([box_strslice] x) [type_id_strslice])
            :pattern ((has_type ([box_strslice] x) [type_id_strslice]))
            :qid prelude_has_type_strslice
            :skolemid skolem_prelude_has_type_strslice
        )))

        // Extensional equality
        (declare-fun [ext_eq] (Bool [typ] [Poly] [Poly]) Bool)
        (axiom (forall ((deep Bool) (t [typ]) (x [Poly]) (y [Poly])) (!
            (= (= x y) ([ext_eq] deep t x y))
            :pattern (([ext_eq] deep t x y))
            :qid prelude_ext_eq
            :skolemid skolem_prelude_ext_eq
        )))

        // Integers
        // TODO: make this more configurable via options or HeaderExpr directives
        (declare-const [arch_size] Int) // number of bits for usize/isize
        (axiom
            {
                match config.arch_word_bits {
                    crate::ast::ArchWordBits::Either32Or64 => nodes!(or (= [arch_size] 32) (= [arch_size] 64)),
                    crate::ast::ArchWordBits::Exactly(bits) => nodes!(= [arch_size] {str_to_node(&bits.to_string())}),
                }
            }
        )
        (declare-fun [u_hi] (Int) Int) // \
        (declare-fun [i_lo] (Int) Int) // - convert number of bits to integer ranges
        (declare-fun [i_hi] (Int) Int) // /
        (axiom (= ([u_hi] 8) {str_to_node(&0x100u16.to_string())}))
        (axiom (= ([u_hi] 16) {str_to_node(&0x10000u32.to_string())}))
        (axiom (= ([u_hi] 32) {str_to_node(&0x100000000u64.to_string())}))
        (axiom (= ([u_hi] 64) {str_to_node(&0x10000000000000000u128.to_string())}))
        (axiom (= ([u_hi] 128) (+ 1 {str_to_node(&0xffffffffffffffffffffffffffffffffu128.to_string())})))
        (axiom (= ([i_lo] 8) (- {str_to_node(&0x80u8.to_string())})))
        (axiom (= ([i_lo] 16) (- {str_to_node(&0x8000u16.to_string())})))
        (axiom (= ([i_lo] 32) (- {str_to_node(&0x80000000u32.to_string())})))
        (axiom (= ([i_lo] 64) (- {str_to_node(&0x8000000000000000u64.to_string())})))
        (axiom (= ([i_lo] 128) (- {str_to_node(&0x80000000000000000000000000000000u128.to_string())})))
        (axiom (= ([i_hi] 8) {str_to_node(&0x80u8.to_string())}))
        (axiom (= ([i_hi] 16) {str_to_node(&0x8000u16.to_string())}))
        (axiom (= ([i_hi] 32) {str_to_node(&0x80000000u32.to_string())}))
        (axiom (= ([i_hi] 64) {str_to_node(&0x8000000000000000u64.to_string())}))
        (axiom (= ([i_hi] 128) {str_to_node(&0x80000000000000000000000000000000u128.to_string())}))
        // clip functions f(num_bits, value)
        (declare-fun [nat_clip] (Int) Int)
        (declare-fun [u_clip] (Int Int) Int)
        (declare-fun [i_clip] (Int Int) Int)
        (axiom (forall ((i Int)) (!
            (and
                (<= 0 ([nat_clip] i))
                (=> (<= 0 i) (= i ([nat_clip] i)))
            )
            :pattern (([nat_clip] i))
            :qid prelude_nat_clip
            :skolemid skolem_prelude_nat_clip
        )))
        (axiom (forall ((bits Int) (i Int)) (!
            (and
                (<= 0 ([u_clip] bits i))
                (< ([u_clip] bits i) ([u_hi] bits))
                (=> (and (<= 0 i) (< i ([u_hi] bits)))
                    (= i ([u_clip] bits i))
                )
            )
            :pattern (([u_clip] bits i))
            :qid prelude_u_clip
            :skolemid skolem_prelude_u_clip
        )))
        (axiom (forall ((bits Int) (i Int)) (!
            (and
                (<= ([i_lo] bits) ([i_clip] bits i))
                (< ([i_clip] bits i) ([i_hi] bits))
                (=> (and (<= ([i_lo] bits) i) (< i ([i_hi] bits)))
                    (= i ([i_clip] bits i))
                )
            )
            :pattern (([i_clip] bits i))
            :qid prelude_i_clip
            :skolemid skolem_prelude_i_clip
        )))
        // type invariants inv(num_bits, value)
        (declare-fun [u_inv] (Int Int) Bool)
        (declare-fun [i_inv] (Int Int) Bool)
        (axiom (forall ((bits Int) (i Int)) (!
            (= ([u_inv] bits i)
                (and (<= 0 i) (< i ([u_hi] bits))
            ))
            :pattern (([u_inv] bits i))
            :qid prelude_u_inv
            :skolemid skolem_prelude_u_inv
        )))
        (axiom (forall ((bits Int) (i Int)) (!
            (= ([i_inv] bits i)
                (and (<= ([i_lo] bits) i) (< i ([i_hi] bits))
            ))
            :pattern (([i_inv] bits i))
            :qid prelude_i_inv
            :skolemid skolem_prelude_i_inv
        )))
        (axiom (forall ((x Int)) (!
            ([has_type] ([box_int] x) [type_id_int])
            :pattern (([has_type] ([box_int] x) [type_id_int]))
            :qid prelude_has_type_int
            :skolemid skolem_prelude_has_type_int
        )))
        (axiom (forall ((x Int)) (!
            (=>
                (<= 0 x)
                ([has_type] ([box_int] x) [type_id_nat])
            )
            :pattern (([has_type] ([box_int] x) [type_id_nat]))
            :qid prelude_has_type_nat
            :skolemid skolem_prelude_has_type_nat
        )))
        (axiom (forall ((bits Int) (x Int)) (!
            (=>
                ([u_inv] bits x)
                ([has_type] ([box_int] x) ([type_id_uint] bits))
            )
            :pattern (([has_type] ([box_int] x) ([type_id_uint] bits)))
            :qid prelude_has_type_uint
            :skolemid skolem_prelude_has_type_uint
        )))
        (axiom (forall ((bits Int) (x Int)) (!
            (=>
                ([i_inv] bits x)
                ([has_type] ([box_int] x) ([type_id_sint] bits))
            )
            :pattern (([has_type] ([box_int] x) ([type_id_sint] bits)))
            :qid prelude_has_type_sint
            :skolemid skolem_prelude_has_type_sint
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_nat])
                (<= 0 ([unbox_int] x))
            )
            :pattern (([has_type] x [type_id_nat]))
            :qid prelude_unbox_int
            :skolemid skolem_prelude_unbox_int
        )))
        (axiom (forall ((bits Int) (x [Poly])) (!
            (=>
                ([has_type] x ([type_id_uint] bits))
                ([u_inv] bits ([unbox_int] x))
            )
            :pattern (([has_type] x ([type_id_uint] bits)))
            :qid prelude_unbox_uint
            :skolemid skolem_prelude_unbox_uint
        )))
        (axiom (forall ((bits Int) (x [Poly])) (!
            (=>
                ([has_type] x ([type_id_sint] bits))
                ([i_inv] bits ([unbox_int] x))
            )
            :pattern (([has_type] x ([type_id_sint] bits)))
            :qid prelude_unbox_sint
            :skolemid skolem_prelude_unbox_sint
        )))

        // With smt.arith.nl=false, Z3 sometimes fails to prove obvious formulas
        // that happen to contain *, div, or mod (e.g. failing to prove P ==> P).
        // So wrap nonlinear occurrences of *, div, mod in a function for better stability:
        (declare-fun [Add] (Int Int) Int)
        (declare-fun [Sub] (Int Int) Int)
        (declare-fun [Mul] (Int Int) Int)
        (declare-fun [EucDiv] (Int Int) Int)
        (declare-fun [EucMod] (Int Int) Int)
        (axiom (forall ((x Int) (y Int)) (!
            (= ([Add] x y) (+ x y))
            :pattern (([Add] x y))
            :qid prelude_add
            :skolemid skolem_prelude_add
        )))
        (axiom (forall ((x Int) (y Int)) (!
            (= ([Sub] x y) (- x y))
            :pattern (([Sub] x y))
            :qid prelude_sub
            :skolemid skolem_prelude_sub
        )))
        (axiom (forall ((x Int) (y Int)) (!
            (= ([Mul] x y) (* x y))
            :pattern (([Mul] x y))
            :qid prelude_mul
            :skolemid skolem_prelude_mul
        )))
        (axiom (forall ((x Int) (y Int)) (!
            (= ([EucDiv] x y) (div x y))
            :pattern (([EucDiv] x y))
            :qid prelude_eucdiv
            :skolemid skolem_prelude_eucdiv
        )))
        (axiom (forall ((x Int) (y Int)) (!
            (= ([EucMod] x y) (mod x y))
            :pattern (([EucMod] x y))
            :qid prelude_eucmod
            :skolemid skolem_prelude_eucmod
        )))

        // These axioms are important to make sure that the nonlinear operations
        // commute with casting-to-ints
        // (e.g., (a * b) as int == (a as int) * (b as int))
        // where applicable.
        //
        // Without these, there can be really unintuitive proof failures.
        //
        // Right now I'm intending these to be the minimal necessary to achieve
        // the above goal - for anything more specific, the user can use the
        // nonlinear_arith solver.

        // Axiom to ensure multiplication of nats are in-bounds
        (axiom (forall ((x Int) (y Int)) (!
            (=>
              (and (<= 0 x) (<= 0 y))
              (<= 0 ([Mul] x y))
            )
            :pattern (([Mul] x y))
            :qid prelude_mul_nats
            :skolemid skolem_prelude_mul_nats
        )))

        // Axiom to ensure division of unsigned types are in-bounds
        // By saying that (x / y) <= x, we can ensure that if x fits in an n-bit integer
        // for any n, then (x / y) also fits in an n-bit integer.
        // Axiom only applies for y != 0
        (axiom (forall ((x Int) (y Int)) (!
            (=>
              (and (<= 0 x) (< 0 y))
              (and
                (<= 0 ([EucDiv] x y))
                (<= ([EucDiv] x y) x)
              )
            )
            :pattern (([EucDiv] x y))
            :qid prelude_div_unsigned_in_bounds
            :skolemid skolem_prelude_div_unsigned_in_bounds
        )))

        // Axiom to ensure modulo of unsigned types are in-bounds
        (axiom (forall ((x Int) (y Int)) (!
            (=>
              (and (<= 0 x) (< 0 y))
              (and
                (<= 0 ([EucMod] x y))
                (< ([EucMod] x y) y)
              )
            )
            :pattern (([EucMod] x y))
            :qid prelude_mod_unsigned_in_bounds
            :skolemid skolem_prelude_mod_unsigned_in_bounds
        )))

        // Chars
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_char])
                (= x ([box_char] ([unbox_char] x)))
            )
            :pattern (([has_type] x [type_id_char]))
            :qid prelude_box_unbox_char
            :skolemid skolem_prelude_box_unbox_char
        )))
        (axiom (forall ((x [Char])) (!
            (= x ([unbox_char] ([box_char] x)))
            :pattern (([box_char] x))
            :qid prelude_unbox_box_char
            :skolemid skolem_prelude_unbox_box_char
        )))
        (axiom (forall ((x [Char])) (!
            ([has_type] ([box_char] x) [type_id_char])
            :pattern ((has_type ([box_char] x) [type_id_char]))
            :qid prelude_has_type_char
            :skolemid skolem_prelude_has_type_char
        )))
        (axiom (forall ((x Int)) (!
            (=>
                (and
                    (<= 0 x)
                    (< x ([u_hi] 32))
                )
                (= x ([to_unicode] ([from_unicode] x)))
            )
            :pattern (([from_unicode] x))
            :qid prelude_char_injective
            :skolemid skolem_prelude_char_injective
        )))
        (axiom (forall ((c [Char])) (!
            (and
                (<= 0 ([to_unicode] c))
                (< ([to_unicode] c) ([u_hi] 32))
            )
            :pattern (([to_unicode] c))
            :qid prelude_to_unicode_bounds
            :skolemid skolem_prelude_to_unicode_bounds
        )))

        // Decreases
        (declare-fun [height] ([Poly]) [Height])
        (declare-fun [height_lt] ([Height] [Height]) Bool)
        (axiom (forall ((x [Height]) (y [Height])) (!
            (= ([height_lt] x y) (and ([height_le] x y) (not (= x y))))
            :pattern (([height_lt] x y))
            :qid prelude_height_lt
            :skolemid skolem_prelude_height_lt
        )))
        (declare-fun [height_rec_fun] ([Poly]) [Poly])
        (declare-fun [check_decrease_int] (Int Int Bool) Bool)
        (axiom (forall ((cur Int) (prev Int) (otherwise Bool)) (!
            (= ([check_decrease_int] cur prev otherwise)
                (or
                    (and (<= 0 cur) (< cur prev))
                    (and (= cur prev) otherwise)
                )
            )
            :pattern (([check_decrease_int] cur prev otherwise))
            :qid prelude_check_decrease_int
            :skolemid skolem_prelude_check_decrease_int
        )))
        (declare-fun [check_decrease_height] ([Poly] [Poly] Bool) Bool)
        (axiom (forall ((cur [Poly]) (prev [Poly]) (otherwise Bool)) (!
            (= ([check_decrease_height] cur prev otherwise)
                (or
                    ([height_lt] ([height] cur) ([height] prev))
                    (and (= ([height] cur) ([height] prev)) otherwise)
                )
            )
            :pattern (([check_decrease_height] cur prev otherwise))
            :qid prelude_check_decrease_height
            :skolemid skolem_prelude_check_decrease_height
        )))

        // uninterpreted integer versions for bitvector Ops. first argument is bit-width
        (declare-fun [uint_xor] (Int [Poly] [Poly]) Int)
        (declare-fun [uint_and] (Int [Poly] [Poly]) Int)
        (declare-fun [uint_or]  (Int [Poly] [Poly]) Int)
        (declare-fun [uint_shr] (Int [Poly] [Poly]) Int)
        (declare-fun [uint_shl] (Int [Poly] [Poly]) Int)
        (declare-fun [uint_not] (Int [Poly]) Int)

        (declare-fun [singular_mod] (Int Int) Int)
        (axiom (forall ((x Int) (y Int)) (!
            (=>
                (not (= y 0))
                (= ([EucMod] x y) ([singular_mod] x y)
            ))
            :pattern (([singular_mod] x y))
            :qid prelude_singularmod
            :skolemid skolem_prelude_singularmod
        )))

        // closure-related

        // Each takes 2 type params:
        //
        //  - Closure type (e.g., anonymous closure type)
        //  - Closure Param type (as tuple type)
        //
        // And 2-3 value params:
        //
        //  - the closure
        //  - param value (as tuple)
        //  - ret value (for closure_ens only)
        //
        // Also for the closure type param, we exclude the decoration.
        // This is useful because it's pretty easy to write code that instantiates
        // type parameters with either `F` or `&F` (where F: Fn(...))
        // So we need to be able to handle both.

        (declare-fun [closure_req] (/*[decoration] skipped */ [typ] [decoration] [typ] [Poly] [Poly]) Bool)
        (declare-fun [closure_ens] (/*[decoration] skipped */ [typ] [decoration] [typ] [Poly] [Poly] [Poly]) Bool)
    )
}

pub(crate) fn datatype_height_axiom(
    typ_name1: &Path,
    typ_name2: &Option<Path>,
    is_variant_ident: &Ident,
    field: &Ident,
    recursive_function_field: bool,
) -> Node {
    let height = str_to_node(HEIGHT);
    let height_lt = str_to_node(HEIGHT_LT);
    let height_rec_fun = str_to_node(HEIGHT_REC_FUN);
    let field = str_to_node(field.as_str());
    let is_variant = str_to_node(is_variant_ident.as_str());
    let typ1 = str_to_node(path_to_air_ident(typ_name1).as_str());
    let box_t1 = str_to_node(prefix_box(typ_name1).as_str());
    let field_of_x = match typ_name2 {
        Some(typ2) => {
            let box_t2 = str_to_node(prefix_box(&typ2).as_str());
            node!(([box_t2] ([field] x)))
        }
        // for a field with generic type, [field]'s return type is already "Poly"
        None => node!(([field] x)),
    };
    let field_of_x =
        if recursive_function_field { node!(([height_rec_fun][field_of_x])) } else { field_of_x };
    node!(
        (axiom (forall ((x [typ1])) (!
            (=>
                ([is_variant] x)
                ([height_lt]
                    ([height] [field_of_x])
                    ([height] ([box_t1] x))
                )
            )
            :pattern (([height] [field_of_x]))
            :qid prelude_datatype_height
            :skolemid skolem_prelude_datatype_height
        )))
    )
}

pub(crate) fn datatype_height_axioms(
    typ_name1: &Path,
    typ_name2: &Option<Path>,
    is_variant_ident: &Ident,
    field: &Ident,
    recursive_function_field: bool,
) -> Vec<Node> {
    let axiom1 = datatype_height_axiom(typ_name1, typ_name2, is_variant_ident, field, false);
    if recursive_function_field {
        let axiom2 = datatype_height_axiom(typ_name1, typ_name2, is_variant_ident, field, true);
        vec![axiom1, axiom2]
    } else {
        vec![axiom1]
    }
}
