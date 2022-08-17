use crate::ast::Path;
use crate::def::*;
use crate::sst_to_air::{fun_to_air_ident, path_to_air_ident};
use air::ast::Ident;
use air::printer::{macro_push_node, str_to_node};
use air::{node, nodes, nodes_vec};
use sise::Node;

#[derive(Copy, Clone, Debug)]
pub enum ArchWordBits {
    Either32Or64,
    Exactly(u32),
}

impl ArchWordBits {
    pub fn min_bits(&self) -> u32 {
        match self {
            ArchWordBits::Either32Or64 => 32,
            ArchWordBits::Exactly(v) => *v,
        }
    }
}

impl Default for ArchWordBits {
    fn default() -> Self {
        ArchWordBits::Either32Or64
    }
}

pub struct PreludeConfig {
    pub arch_word_bits: ArchWordBits,
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
    let Mul = str_to_node(MUL);
    #[allow(non_snake_case)]
    let EucDiv = str_to_node(EUC_DIV);
    #[allow(non_snake_case)]
    let EucMod = str_to_node(EUC_MOD);
    let check_decrease_int =
        str_to_node(&suffix_global_id(&fun_to_air_ident(&check_decrease_int())));
    let height = str_to_node(&suffix_global_id(&fun_to_air_ident(&height())));
    #[allow(non_snake_case)]
    let Poly = str_to_node(POLY);
    let box_int = str_to_node(BOX_INT);
    let box_bool = str_to_node(BOX_BOOL);
    let unbox_int = str_to_node(UNBOX_INT);
    let unbox_bool = str_to_node(UNBOX_BOOL);

    let box_strslice = str_to_node(BOX_STRSLICE);
    let unbox_strslice = str_to_node(UNBOX_STRSLICE);

    let typ = str_to_node(TYPE);
    let type_id_bool = str_to_node(TYPE_ID_BOOL);
    let type_id_int = str_to_node(TYPE_ID_INT);
    let type_id_nat = str_to_node(TYPE_ID_NAT);
    let type_id_uint = str_to_node(TYPE_ID_UINT);
    let type_id_sint = str_to_node(TYPE_ID_SINT);
    let has_type = str_to_node(HAS_TYPE);
    let as_type = str_to_node(AS_TYPE);
    let mk_fun = str_to_node(MK_FUN);

    let uint_xor = str_to_node(UINT_XOR);
    let uint_and = str_to_node(UINT_AND);
    let uint_or = str_to_node(UINT_OR);
    let uint_shr = str_to_node(UINT_SHR);
    let uint_shl = str_to_node(UINT_SHL);
    let uint_not = str_to_node(UINT_NOT);

    let strslice = strslice();

    let strslice_is_ascii = strslice_is_ascii();
    let strslice_len = strslice_len();
    let strslice_get_char = strslice_get_char();
    let type_id_strslice = str_to_node(TYPE_ID_STRSLICE);
    let new_strlit = strslice_new_strlit();

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
        (declare-sort [strslice] 0)
        (declare-fun [strslice_is_ascii] ([strslice]) Bool)
        (declare-fun [strslice_len] ([strslice]) Int)
        (declare-fun [strslice_get_char] ([strslice] Int) Int)
        (declare-fun [new_strlit] (Int) [strslice])

        // Polymorphism
        (declare-sort [Poly] 0)
        (declare-fun [box_int] (Int) [Poly])
        (declare-fun [box_bool] (Bool) [Poly])
        (declare-fun [unbox_int] ([Poly]) Int)
        (declare-fun [unbox_bool] ([Poly]) Bool)
        (declare-fun [box_strslice] ([strslice]) [Poly])
        (declare-fun [unbox_strslice] ([Poly]) [strslice])
        (declare-sort [typ] 0)
        (declare-const [type_id_bool] [typ])
        (declare-const [type_id_int] [typ])
        (declare-const [type_id_nat] [typ])
        (declare-const [type_id_strslice] [typ])
        (declare-fun [type_id_uint] (Int) [typ])
        (declare-fun [type_id_sint] (Int) [typ])
        (declare-fun [has_type] ([Poly] [typ]) Bool)
        (declare-fun [as_type] ([Poly] [typ]) Poly)
        (declare-fun [mk_fun] (Fun) Fun)
        (axiom ([has_type] ([box_bool] true) BOOL))
        (axiom ([has_type] ([box_bool] false) BOOL))
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

        // Integers
        // TODO: make this more configurable via options or HeaderExpr directives
        (declare-const [arch_size] Int) // number of bits for usize/isize
        (axiom
            {
                match config.arch_word_bits {
                    ArchWordBits::Either32Or64 => nodes!(or (= [arch_size] 32) (= [arch_size] 64)),
                    ArchWordBits::Exactly(bits) => nodes!(= [arch_size] {str_to_node(&bits.to_string())}),
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
        (axiom (forall ((x Poly)) (!
            (=>
                ([has_type] x [type_id_nat])
                (<= 0 ([unbox_int] x))
            )
            :pattern (([has_type] x [type_id_nat]))
            :qid prelude_unbox_int
            :skolemid skolem_prelude_unbox_int
        )))
        (axiom (forall ((bits Int) (x Poly)) (!
            (=>
                ([has_type] x ([type_id_uint] bits))
                ([u_inv] bits ([unbox_int] x))
            )
            :pattern (([has_type] x ([type_id_uint] bits)))
            :qid prelude_unbox_uint
            :skolemid skolem_prelude_unbox_uint
        )))
        (axiom (forall ((bits Int) (x Poly)) (!
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
        (declare-fun [Mul] (Int Int) Int)
        (declare-fun [EucDiv] (Int Int) Int)
        (declare-fun [EucMod] (Int Int) Int)
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

        // Decreases
        (declare-fun [check_decrease_int] (Int Int Bool) Bool)
        (axiom (forall ((cur Int) (prev Int) (otherwise Bool)) (!
            (= ([check_decrease_int] cur prev otherwise)
                (or
                    (and (<= 0 cur) (< cur prev))
                    (and (= cur prev) otherwise)
                )
            )
            :pattern (([check_decrease_int] cur prev otherwise))
            :qid prelude_check_decreases
            :skolemid skolem_prelude_check_decreases
        )))
        (declare-fun [height] (Poly) Int)
        (axiom (forall ((x Poly)) (!
            (<= 0 ([height] x))
            :pattern (([height] x))
            :qid prelude_height
            :skolemid skolem_prelude_height
        )))

        // uninterpreted integer versions for bitvector Ops. first argument is bit-width
        (declare-fun [uint_xor] (Int Poly Poly) Int)
        (declare-fun [uint_and] (Int Poly Poly) Int)
        (declare-fun [uint_or]  (Int Poly Poly) Int)
        (declare-fun [uint_shr] (Int Poly Poly) Int)
        (declare-fun [uint_shl] (Int Poly Poly) Int)
        (declare-fun [uint_not] (Int Poly) Int)
    )
}

pub(crate) fn datatype_height_axiom(typ_name1: &Path, typ_name2: &Path, field: &Ident) -> Node {
    let height = str_to_node(&suffix_global_id(&fun_to_air_ident(&height())));
    let field = str_to_node(field.as_str());
    let typ1 = str_to_node(path_to_air_ident(typ_name1).as_str());
    let box_t1 = str_to_node(prefix_box(typ_name1).as_str());
    let box_t2 = str_to_node(prefix_box(typ_name2).as_str());
    node!(
        (axiom (forall ((x [typ1])) (!
            (<
                ([height] ([box_t2] ([field] x)))
                ([height] ([box_t1] x))
            )
            :pattern (([height] ([box_t2] ([field] x))))
            :qid prelude_datatype_height
            :skolemid skolem_prelude_datatype_height
        )))
    )
}
