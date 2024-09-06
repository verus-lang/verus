use crate::ast::Path;
use crate::def::*;
use crate::sst_to_air::path_to_air_ident;
use air::ast::Ident;
use air::context::SmtSolver;
use air::printer::{macro_push_node, str_to_node};
use air::{node, nodes, nodes_vec};
use sise::Node;

pub struct PreludeConfig {
    pub arch_word_bits: crate::ast::ArchWordBits,
    pub solver: SmtSolver,
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
    let char_clip = str_to_node(CHAR_CLIP);
    let u_inv = str_to_node(U_INV);
    let i_inv = str_to_node(I_INV);
    let char_inv = str_to_node(CHAR_INV);
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
    let height_axioms = match config.solver {
        SmtSolver::Z3 => nodes_vec!(
        (axiom (forall ((x [Height]) (y [Height])) (!
            (= ([height_lt] x y) (and ([height_le] x y) (not (= x y))))
            :pattern (([height_lt] x y))
            :qid prelude_height_lt
            :skolemid skolem_prelude_height_lt
            )))),
        SmtSolver::Cvc5 => nodes_vec!(
                    (declare-fun partial-order (Height Height) Bool)
                    (axiom (forall ((x Height)) (partial-order x x)))
                    (axiom (forall ((x Height) (y Height)) (=> (and (partial-order x y) (partial-order y x)) (= x y))))
                    (axiom (forall ((x Height) (y Height) (z Height)) (=> (and (partial-order x y) (partial-order y z)) (partial-order x z))))
                    (axiom (forall ((x Height) (y Height)) (= (height_lt x y) (and (partial-order x y) (not (= x y))))))),
    };
    let box_int = str_to_node(BOX_INT);
    let box_bool = str_to_node(BOX_BOOL);
    let box_fndef = str_to_node(BOX_FNDEF);
    let unbox_int = str_to_node(UNBOX_INT);
    let unbox_bool = str_to_node(UNBOX_BOOL);
    let unbox_fndef = str_to_node(UNBOX_FNDEF);

    #[allow(non_snake_case)]
    let FnDef = str_to_node(FNDEF_TYPE);
    #[allow(non_snake_case)]
    let FnDefSingleton = str_to_node(FNDEF_SINGLETON);

    let char_lo_1 = str_to_node(&format!("{}", crate::unicode::CHAR_RANGE_1_MIN));
    let char_hi_1 = str_to_node(&format!("{}", crate::unicode::CHAR_RANGE_1_MAX));
    let char_lo_2 = str_to_node(&format!("{}", crate::unicode::CHAR_RANGE_2_MIN));
    let char_hi_2 = str_to_node(&format!("{}", crate::unicode::CHAR_RANGE_2_MAX));

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
    let decorate_const_ptr = str_to_node(DECORATE_CONST_PTR);
    let has_type = str_to_node(HAS_TYPE);
    let as_type = str_to_node(AS_TYPE);
    let mk_fun = str_to_node(MK_FUN);
    let const_int = str_to_node(CONST_INT);
    let ext_eq = str_to_node(EXT_EQ);

    let bit_xor = str_to_node(BIT_XOR);
    let bit_and = str_to_node(BIT_AND);
    let bit_or = str_to_node(BIT_OR);
    let bit_shr = str_to_node(BIT_SHR);
    let bit_shl = str_to_node(BIT_SHL);
    let bit_not = str_to_node(BIT_NOT);
    let singular_mod = str_to_node(SINGULAR_MOD);

    let type_id_array = str_to_node(TYPE_ID_ARRAY);
    let type_id_slice = str_to_node(TYPE_ID_SLICE);
    let type_id_strslice = str_to_node(TYPE_ID_STRSLICE);
    let type_id_ptr = str_to_node(TYPE_ID_PTR);
    let type_id_global = str_to_node(TYPE_ID_GLOBAL);

    let mut prelude = nodes_vec!(
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

        // FnDef
        (declare-datatypes (([FnDef] 0)) ((([FnDefSingleton]))))

        // Polymorphism
        (declare-sort [Poly] 0)
        (declare-sort [Height] 0)
        (declare-fun [box_int] (Int) [Poly])
        (declare-fun [box_bool] (Bool) [Poly])
        (declare-fun [box_fndef] ([FnDef]) [Poly])
        (declare-fun [unbox_int] ([Poly]) Int)
        (declare-fun [unbox_bool] ([Poly]) Bool)
        (declare-fun [unbox_fndef] ([Poly]) [FnDef])
        (declare-sort [typ] 0)
        (declare-const [type_id_bool] [typ])
        (declare-const [type_id_int] [typ])
        (declare-const [type_id_nat] [typ])
        (declare-const [type_id_char] [typ])
        (declare-fun [type_id_uint] (Int) [typ])
        (declare-fun [type_id_sint] (Int) [typ])
        (declare-fun [type_id_const_int] (Int) [typ])
        (declare-sort [decoration] 0)
        (declare-const [decorate_nil] [decoration])
        (declare-fun [decorate_ref] ([decoration]) [decoration])
        (declare-fun [decorate_mut_ref] ([decoration]) [decoration])
        (declare-fun [decorate_box] ([decoration] [typ] [decoration]) [decoration])
        (declare-fun [decorate_rc] ([decoration] [typ] [decoration]) [decoration])
        (declare-fun [decorate_arc] ([decoration] [typ] [decoration]) [decoration])
        (declare-fun [decorate_ghost] ([decoration]) [decoration])
        (declare-fun [decorate_tracked] ([decoration]) [decoration])
        (declare-fun [decorate_never] ([decoration]) [decoration])
        (declare-fun [decorate_const_ptr] ([decoration]) [decoration])
        (declare-fun [type_id_array] ([decoration] [typ] [decoration] [typ]) [typ])
        (declare-fun [type_id_slice] ([decoration] [typ]) [typ])
        (declare-const [type_id_strslice] [typ])
        (declare-const [type_id_global] [typ])
        (declare-fun [type_id_ptr] ([decoration] [typ]) [typ])
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
            (= ([mk_fun] x) x)
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
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_char])
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x [type_id_char]))
            :qid prelude_box_unbox_char
            :skolemid skolem_prelude_box_unbox_char
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
        (declare-fun [char_clip] (Int) Int)
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
        (axiom (forall ((i Int)) (!
            (and
                (or
                    (and (<= [char_lo_1] ([char_clip] i)) (<= ([char_clip] i) [char_hi_1]))
                    (and (<= [char_lo_2] ([char_clip] i)) (<= ([char_clip] i) [char_hi_2]))
                )
                (=>
                    (or
                        (and (<= [char_lo_1] i) (<= i [char_hi_1]))
                        (and (<= [char_lo_2] i) (<= i [char_hi_2]))
                    )
                    (= i ([char_clip] i))
                )
            )
            :pattern (([char_clip] i))
            :qid prelude_char_clip
            :skolemid skolem_prelude_char_clip
        )))

        // type invariants inv(num_bits, value)
        (declare-fun [u_inv] (Int Int) Bool)
        (declare-fun [i_inv] (Int Int) Bool)
        (declare-fun [char_inv] (Int) Bool)
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
        (axiom (forall ((i Int)) (!
            (= ([char_inv] i)
                (or
                    (and (<= [char_lo_1] i) (<= i [char_hi_1]))
                    (and (<= [char_lo_2] i) (<= i [char_hi_2]))
                )
            )
            :pattern (([char_inv] i))
            :qid prelude_char_inv
            :skolemid skolem_prelude_char_inv
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
        (axiom (forall ((x Int)) (!
            (=>
                ([char_inv] x)
                ([has_type] ([box_int] x) [type_id_char])
            )
            :pattern (([has_type] ([box_int] x) [type_id_char]))
            :qid prelude_has_type_char
            :skolemid skolem_prelude_has_type_char
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

        // uninterpreted integer versions for bitvector Ops.
        // These all apply on unbounded ints (an unbounded int can be written
        // as infinite binary string; negative integers have 1s going infinitely to the left).
        //
        // For XOR, AND, OR, SHR, and signed-NOT,
        // the unbounded int versions are identical
        // to the finite-width versions (axioms for these are below).
        //
        // For SHL and unsigned-NOT, we can add a clip around the unbounded-function to
        // get the finite-width operation.
        //
        // Note: BitShr/BitShl are underspecified if second argument is negative

        (declare-fun [bit_xor] ([Poly] [Poly]) Int)
        (declare-fun [bit_and] ([Poly] [Poly]) Int)
        (declare-fun [bit_or]  ([Poly] [Poly]) Int)
        (declare-fun [bit_shr] ([Poly] [Poly]) Int)
        (declare-fun [bit_shl] ([Poly] [Poly]) Int)
        (declare-fun [bit_not] ([Poly]) Int)

        // bounds on bit-ops

        // For XOR, AND, and OR:
        // If the two arguments fit in uN/iN, then the output fits in uN/iN
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([u_inv] bits ([unbox_int] x)) ([u_inv] bits ([unbox_int] y)))
              ([u_inv] bits ([bit_xor] x y))
            )
            :pattern (([u_clip] bits ([bit_xor] x y)))
            :qid prelude_bit_xor_u_inv
            :skolemid skolem_prelude_bit_xor_u_inv
        )))
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([i_inv] bits ([unbox_int] x)) ([i_inv] bits ([unbox_int] y)))
              ([i_inv] bits ([bit_xor] x y))
            )
            :pattern (([i_clip] bits ([bit_xor] x y)))
            :qid prelude_bit_xor_i_inv
            :skolemid skolem_prelude_bit_xor_i_inv
        )))
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([u_inv] bits ([unbox_int] x)) ([u_inv] bits ([unbox_int] y)))
              ([u_inv] bits ([bit_or] x y))
            )
            :pattern (([u_clip] bits ([bit_or] x y)))
            :qid prelude_bit_or_u_inv
            :skolemid skolem_prelude_bit_or_u_inv
        )))
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([i_inv] bits ([unbox_int] x)) ([i_inv] bits ([unbox_int] y)))
              ([i_inv] bits ([bit_or] x y))
            )
            :pattern (([i_clip] bits ([bit_or] x y)))
            :qid prelude_bit_or_i_inv
            :skolemid skolem_prelude_bit_or_i_inv
        )))
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([u_inv] bits ([unbox_int] x)) ([u_inv] bits ([unbox_int] y)))
              ([u_inv] bits ([bit_and] x y))
            )
            :pattern (([u_clip] bits ([bit_and] x y)))
            :qid prelude_bit_and_u_inv
            :skolemid skolem_prelude_bit_and_u_inv
        )))
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([i_inv] bits ([unbox_int] x)) ([i_inv] bits ([unbox_int] y)))
              ([i_inv] bits ([bit_and] x y))
            )
            :pattern (([i_clip] bits ([bit_and] x y)))
            :qid prelude_bit_and_i_inv
            :skolemid skolem_prelude_bit_and_i_inv
        )))

        // For shr, if the *first* argument fits in uN/iN,
        // and the second arg is >= 0, then the output fits in uN/iN
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([u_inv] bits ([unbox_int] x)) (<= 0 ([unbox_int] y)))
              ([u_inv] bits ([bit_shr] x y))
            )
            :pattern (([u_clip] bits ([bit_shr] x y)))
            :qid prelude_bit_shr_u_inv
            :skolemid skolem_prelude_bit_shr_u_inv
        )))
        (axiom (forall ((x [Poly]) (y [Poly]) (bits Int)) (!
            (=>
              (and ([i_inv] bits ([unbox_int] x)) (<= 0 ([unbox_int] y)))
              ([i_inv] bits ([bit_shr] x y))
            )
            :pattern (([i_clip] bits ([bit_shr] x y)))
            :qid prelude_bit_shr_i_inv
            :skolemid skolem_prelude_bit_shr_i_inv
        )))

        // Nothing for shl

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

        // Decreases
        (declare-fun [height] ([Poly]) [Height])
        (declare-fun [height_lt] ([Height] [Height]) Bool)
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
    );
    prelude.extend(height_axioms);
    prelude
}

pub(crate) fn array_functions(box_array: &str) -> Vec<Node> {
    let box_array = str_to_node(box_array);
    let array_new = str_to_node(ARRAY_NEW);
    let array_index = str_to_node(ARRAY_INDEX);
    let typ = str_to_node(TYPE);
    let decoration = str_to_node(DECORATION);
    let has_type = str_to_node(HAS_TYPE);
    let type_id_array = str_to_node(TYPE_ID_ARRAY);
    let type_id_int = str_to_node(TYPE_ID_INT);
    let type_id_const_int = str_to_node(TYPE_ID_CONST_INT);
    #[allow(non_snake_case)]
    let Poly = str_to_node(POLY);

    nodes_vec!(
        // array literals
        (declare-fun [array_new] ([decoration] [typ] Int Fun) [Poly])
        (declare-fun [array_index] ([decoration] [typ] [decoration] [typ] Fun Poly) [Poly])
        (axiom (forall ((Tdcr [decoration]) (T [typ]) (N Int) (Fn Fun)) (!
            (= ([array_new] Tdcr T N Fn) ([box_array] Fn))
            :pattern (([array_new] Tdcr T N Fn))
            :qid prelude_array_new
            :skolemid skolem_prelude_array_new
        )))
        (axiom
            (forall ((Tdcr [decoration]) (T [typ]) (N Int) (Fn Fun)) (!
                (=>
                    (forall ((i Int)) (!
                        (=> (and (<= 0 i) (< i N))
                            ([has_type] (apply [Poly] Fn i) T)
                        )
                        :pattern (([has_type] (apply [Poly] Fn i) T))
                        :qid prelude_has_type_array_elts
                        :skolemid skolem_prelude_has_type_array_elts
                    ))
                    ([has_type] ([array_new] Tdcr T N Fn) ([type_id_array] Tdcr T $ ([type_id_const_int] N)))
                )
                :pattern (([array_new] Tdcr T N Fn))
                :qid prelude_has_type_array_new
                :skolemid skolem_prelude_has_type_array_new
            ))
        )
        (axiom (forall ((Tdcr [decoration]) (T [typ]) (Ndcr [decoration]) (N [typ]) (Fn Fun) (i Poly)) (!
            (=>
                (and
                    ([has_type] ([box_array] Fn) ([type_id_array] Tdcr T Ndcr N))
                    ([has_type] i [type_id_int])
                )
                ([has_type] ([array_index] Tdcr T $ N Fn i) T)
            )
            :pattern (([array_index] Tdcr T $ N Fn i) ([has_type] ([box_array] Fn) ([type_id_array] Tdcr T Ndcr N)))
            :qid prelude_has_type_array_index
            :skolemid skolem_prelude_has_type_array_index
        )))
        // AIR declares axioms about the array in terms of (apply [Poly] Fn i),
        // which is hard for vstd axioms to trigger on.
        // Rewrite as ([array_index] ...), which vstd can more easily trigger on.
        // (Note that there's no axiom in the reverse direction converting array_index to apply,
        // because that would create a matching loop on i via I and %I.)
        (axiom (forall ((Tdcr [decoration]) (T [typ]) (N Int) (Fn Fun) (i Int)) (!
            (= ([array_index] Tdcr T $ ([type_id_const_int] N) Fn (I i)) (apply [Poly] Fn i))
            :pattern (([array_new] Tdcr T N Fn) (apply [Poly] Fn i))
            :qid prelude_array_index_trigger
            :skolemid skolem_prelude_array_index_trigger
        )))
    )
}

pub(crate) fn strslice_functions(strslice_name: &str) -> Vec<Node> {
    let strslice = str_to_node(strslice_name);
    let strslice_is_ascii = str_to_node(STRSLICE_IS_ASCII);
    let strslice_len = str_to_node(STRSLICE_LEN);
    let strslice_get_char = str_to_node(STRSLICE_GET_CHAR);
    let new_strlit = str_to_node(STRSLICE_NEW_STRLIT);
    let from_strlit = str_to_node(STRSLICE_FROM_STRLIT);
    nodes_vec!(
        // Strings
        (declare-fun [strslice_is_ascii] ([strslice]) Bool)
        (declare-fun [strslice_len] ([strslice]) Int)
        (declare-fun [strslice_get_char] ([strslice] Int) Int)
        (declare-fun [new_strlit] (Int) [strslice])
        (declare-fun [from_strlit] ([strslice]) Int)

        // String literals
        (axiom (forall ((x Int)) (!
            (= ([from_strlit] ([new_strlit] x)) x)
            :pattern (([new_strlit] x))
            :qid prelude_strlit_injective
            :skolemid skolem_prelude_strlit_injective
        )))
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
    let qid = str_to_node(format!("prelude_datatype_height_{}", field).as_str());
    let skolem_id = str_to_node(format!("skolem_prelude_datatype_height_{}", field).as_str());
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
            :qid [qid]
            :skolemid [skolem_id]
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
