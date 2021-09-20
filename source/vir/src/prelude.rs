use crate::def::*;
use crate::sst_to_air::path_to_air_ident;
use air::ast::Ident;
use air::printer::{macro_push_node, str_to_node};
use air::{node, nodes_vec};
use sise::Node;

pub(crate) fn prelude_nodes() -> Vec<Node> {
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
    let check_decrease_int =
        str_to_node(&suffix_global_id(&path_to_air_ident(&check_decrease_int())));
    #[allow(non_snake_case)]
    let Unit = str_to_node(UNIT);
    #[allow(non_snake_case)]
    let Poly = str_to_node(POLY);
    let box_int = str_to_node(BOX_INT);
    let box_bool = str_to_node(BOX_BOOL);
    let unbox_int = str_to_node(UNBOX_INT);
    let unbox_bool = str_to_node(UNBOX_BOOL);
    let typ = str_to_node(TYPE);
    let type_id_bool = str_to_node(TYPE_ID_BOOL);
    let type_id_int = str_to_node(TYPE_ID_INT);
    let type_id_nat = str_to_node(TYPE_ID_NAT);
    let type_id_uint = str_to_node(TYPE_ID_UINT);
    let type_id_sint = str_to_node(TYPE_ID_SINT);
    let has_type = str_to_node(HAS_TYPE);

    nodes_vec!(
        (declare-datatypes () (([Unit] (mk_unit))))

        // Fuel
        (declare-sort [FuelId])
        (declare-sort [Fuel])
        (declare-const [zero] [Fuel])
        (declare-fun [succ] ([Fuel]) [Fuel])
        (declare-fun [fuel_bool] ([FuelId]) Bool)
        (declare-fun [fuel_bool_default] ([FuelId]) Bool)
        (declare-const [fuel_defaults] Bool)
        (axiom (=> [fuel_defaults]
            (forall ((id [FuelId])) (!
                (= ([fuel_bool] id) ([fuel_bool_default] id))
                :pattern (([fuel_bool] id))
            ))
        ))

        // Polymorphism
        (declare-sort [Poly])
        (declare-fun [box_int] (Int) [Poly])
        (declare-fun [box_bool] (Bool) [Poly])
        (declare-fun [unbox_int] ([Poly]) Int)
        (declare-fun [unbox_bool] ([Poly]) Bool)
        (declare-sort [typ])
        (declare-const [type_id_bool] [typ])
        (declare-const [type_id_int] [typ])
        (declare-const [type_id_nat] [typ])
        (declare-fun [type_id_uint] (Int) [typ])
        (declare-fun [type_id_sint] (Int) [typ])
        (declare-fun [has_type] ([Poly] [typ]) Bool)
        (axiom (forall ((x Bool)) (!
            (= x ([unbox_bool] ([box_bool] x)))
            :pattern (([box_bool] x))
        )))
        (axiom (forall ((x Int)) (!
            (= x ([unbox_int] ([box_int] x)))
            :pattern (([box_int] x))
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_bool])
                (= x ([box_bool] ([unbox_bool] x)))
            )
            :pattern (([has_type] x [type_id_bool]))
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_int])
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x [type_id_int]))
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id_nat])
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x [type_id_nat]))
        )))
        (axiom (forall ((bits Int) (x [Poly])) (!
            (=>
                ([has_type] x ([type_id_uint] bits))
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x ([type_id_uint] bits)))
        )))
        (axiom (forall ((bits Int) (x [Poly])) (!
            (=>
                ([has_type] x ([type_id_sint] bits))
                (= x ([box_int] ([unbox_int] x)))
            )
            :pattern (([has_type] x ([type_id_sint] bits)))
        )))

        // Integers
        // TODO: make this more configurable via options or HeaderExpr directives
        (declare-const [arch_size] Int) // number of bits for usize/isize
        (axiom (or (= [arch_size] 32) (= [arch_size] 64)))
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
        )))
        // type invariants inv(num_bits, value)
        (declare-fun [u_inv] (Int Int) Bool)
        (declare-fun [i_inv] (Int Int) Bool)
        (axiom (forall ((bits Int) (i Int)) (!
            (= ([u_inv] bits i)
                (and (<= 0 i) (< i ([u_hi] bits))
            ))
            :pattern (([u_inv] bits i))
        )))
        (axiom (forall ((bits Int) (i Int)) (!
            (= ([i_inv] bits i)
                (and (<= ([i_lo] bits) i) (< i ([i_hi] bits))
            ))
            :pattern (([i_inv] bits i))
        )))
        (axiom (forall ((x Poly)) (!
            (=>
                ([has_type] x [type_id_nat])
                (<= 0 ([unbox_int] x))
            )
            :pattern (([has_type] x [type_id_nat]))
        )))
        (axiom (forall ((bits Int) (x Poly)) (!
            (=>
                ([has_type] x ([type_id_uint] bits))
                ([u_inv] bits ([unbox_int] x))
            )
            :pattern (([has_type] x ([type_id_uint] bits)))
        )))
        (axiom (forall ((bits Int) (x Poly)) (!
            (=>
                ([has_type] x ([type_id_sint] bits))
                ([i_inv] bits ([unbox_int] x))
            )
            :pattern (([has_type] x ([type_id_sint] bits)))
        )))

        // Decreases
        (declare-fun [check_decrease_int] (Int Int) Bool)
        (axiom (forall ((cur Int) (prev Int)) (!
            (= ([check_decrease_int] cur prev)
                (and (<= 0 cur) (< cur prev))
            )
            :pattern (([check_decrease_int] cur prev))
        )))
    )
}

pub(crate) fn datatype_box_axioms(typ_name: &Ident) -> Vec<Node> {
    let typ = str_to_node(typ_name.as_str());
    let type_id = str_to_node(prefix_type_id(typ_name).as_str());
    let box_t = str_to_node(prefix_box(typ_name).as_str());
    let unbox_t = str_to_node(prefix_unbox(typ_name).as_str());
    #[allow(non_snake_case)]
    let Poly = str_to_node(POLY);
    let has_type = str_to_node(HAS_TYPE);
    nodes_vec!(
        (axiom (forall ((x [typ])) (!
            (= x ([unbox_t] ([box_t] x)))
            :pattern (([box_t] x))
        )))
        (axiom (forall ((x [Poly])) (!
            (=>
                ([has_type] x [type_id])
                (= x ([box_t] ([unbox_t] x)))
            )
            :pattern (([has_type] x [type_id]))
        )))
    )
}
