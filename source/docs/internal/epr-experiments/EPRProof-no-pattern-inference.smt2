(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
))))
(declare-sort Dummy 0)
(declare-fun no_arg () Dummy)
(declare-sort Char 0)
(declare-fun char%from_unicode (Int) Char)
(declare-fun char%to_unicode (Char) Int)
(declare-sort StrSlice 0)
(declare-fun str%strslice_is_ascii (StrSlice) Bool)
(declare-fun str%strslice_len (StrSlice) Int)
(declare-fun str%strslice_get_char (StrSlice Int) Char)
(declare-fun str%new_strlit (Int) StrSlice)
(declare-fun str%from_strlit (StrSlice) Int)
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun S (StrSlice) Poly)
(declare-fun %S (Poly) StrSlice)
(declare-fun C (Char) Poly)
(declare-fun %C (Poly) Char)
(declare-fun D (Dummy) Poly)
(declare-fun %D (Poly) Dummy)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const STRSLICE Type)
(declare-const CHAR Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-const DUMMY Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr) Dcr)
(declare-fun RC (Dcr) Dcr)
(declare-fun ARC (Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
   :skolemid skolem_prelude_type_id_const_int
)))
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
   :skolemid skolem_prelude_has_type_bool
)))
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Int)) (!
   (= (str%from_strlit (str%new_strlit x)) x)
   :pattern ((str%new_strlit x))
   :qid prelude_strlit_injective
   :skolemid skolem_prelude_strlit_injective
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x STRSLICE)
    (= x (S (%S x)))
   )
   :pattern ((has_type x STRSLICE))
   :qid prelude_box_unbox_strslice
   :skolemid skolem_prelude_box_unbox_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (= x (%S (S x)))
   :pattern ((S x))
   :qid prelude_unbox_box_strslice
   :skolemid skolem_prelude_unbox_box_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (has_type (S x) STRSLICE)
   :pattern ((has_type (S x) STRSLICE))
   :qid prelude_has_type_strslice
   :skolemid skolem_prelude_has_type_strslice
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
   :skolemid skolem_prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (C (%C x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))
(assert
 (forall ((x Char)) (!
   (= x (%C (C x)))
   :pattern ((C x))
   :qid prelude_unbox_box_char
   :skolemid skolem_prelude_unbox_box_char
)))
(assert
 (forall ((x Char)) (!
   (has_type (C x) CHAR)
   :pattern ((has_type (C x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Int)) (!
   (=>
    (and
     (<= 0 x)
     (< x (uHi 32))
    )
    (= x (char%to_unicode (char%from_unicode x)))
   )
   :pattern ((char%from_unicode x))
   :qid prelude_char_injective
   :skolemid skolem_prelude_char_injective
)))
(assert
 (forall ((c Char)) (!
   (and
    (<= 0 (char%to_unicode c))
    (< (char%to_unicode c) (uHi 32))
   )
   :pattern ((char%to_unicode c))
   :qid prelude_to_unicode_bounds
   :skolemid skolem_prelude_to_unicode_bounds
)))
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(assert
 (forall ((x Height) (y Height)) (!
   (= (height_lt x y) (and
     ((_ partial-order 0) x y)
     (not (= x y))
   ))
   :pattern ((height_lt x y))
   :qid prelude_height_lt
   :skolemid skolem_prelude_height_lt
)))
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))
(declare-fun uintxor (Int Poly Poly) Int)
(declare-fun uintand (Int Poly Poly) Int)
(declare-fun uintor (Int Poly Poly) Int)
(declare-fun uintshr (Int Poly Poly) Int)
(declare-fun uintshl (Int Poly Poly) Int)
(declare-fun uintnot (Int Poly) Int)
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
   :skolemid skolem_prelude_singularmod
)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)

;; MODULE 'module EPRProof'

;; Fuel
(declare-const fuel%delmap_epr!EPRModel.impl&%0.erase. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%0.erase_unbounded. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%0.set. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%0.contains. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%0.g_l_b. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%1.new. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%1.get. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%1.get_internal. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%1.set. FuelId)
(declare-const fuel%delmap_epr!EPRModel.impl&%1.set_unbounded. FuelId)
(declare-const fuel%delmap_epr!EPRProof.m_has_key. FuelId)
(declare-const fuel%delmap_epr!EPRProof.dmap_invariant. FuelId)
(assert
 (distinct fuel%delmap_epr!EPRModel.impl&%0.erase. fuel%delmap_epr!EPRModel.impl&%0.erase_unbounded.
  fuel%delmap_epr!EPRModel.impl&%0.set. fuel%delmap_epr!EPRModel.impl&%0.contains.
  fuel%delmap_epr!EPRModel.impl&%0.g_l_b. fuel%delmap_epr!EPRModel.impl&%1.new. fuel%delmap_epr!EPRModel.impl&%1.get.
  fuel%delmap_epr!EPRModel.impl&%1.get_internal. fuel%delmap_epr!EPRModel.impl&%1.set.
  fuel%delmap_epr!EPRModel.impl&%1.set_unbounded. fuel%delmap_epr!EPRProof.m_has_key.
  fuel%delmap_epr!EPRProof.dmap_invariant.
))

;; Datatypes
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-fun TYPE%delmap_epr!EPRModel.SOMapModel. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%delmap_epr!EPRModel.DMapModel. (Dcr Type Dcr Type) Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x@ tuple%0.)) (!
   (= x@ (%Poly%tuple%0. (Poly%tuple%0. x@)))
   :pattern ((Poly%tuple%0. x@))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%tuple%0.)
    (= x@ (Poly%tuple%0. (%Poly%tuple%0. x@)))
   )
   :pattern ((has_type x@ TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x@ tuple%0.)) (!
   (has_type (Poly%tuple%0. x@) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x@) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))

;; Traits
(declare-fun tr_bound%delmap_epr!VerusClone. (Dcr Type) Bool)
(declare-fun tr_bound%delmap_epr!Key. (Dcr Type) Bool)

;; Function-Decl delmap_epr::EPRModel::SOMapModel::m
(declare-fun delmap_epr!EPRModel.impl&%0.m.? (Dcr Type Dcr Type Poly Poly Poly) Bool)

;; Function-Decl delmap_epr::EPRModel::SOMapModel::gap
(declare-fun delmap_epr!EPRModel.impl&%0.gap.? (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)

;; Function-Decl delmap_epr::EPRModel::SOMapModel::erase
(declare-fun delmap_epr!EPRModel.impl&%0.erase.? (Dcr Type Dcr Type Poly Poly Poly
  Poly
 ) Bool
)

;; Function-Decl delmap_epr::EPRModel::SOMapModel::erase_unbounded
(declare-fun delmap_epr!EPRModel.impl&%0.erase_unbounded.? (Dcr Type Dcr Type Poly
  Poly Poly
 ) Bool
)

;; Function-Decl delmap_epr::EPRModel::SOMapModel::set
(declare-fun delmap_epr!EPRModel.impl&%0.set.? (Dcr Type Dcr Type Poly Poly Poly Poly)
 Bool
)

;; Function-Decl delmap_epr::EPRModel::SOMapModel::contains
(declare-fun delmap_epr!EPRModel.impl&%0.contains.? (Dcr Type Dcr Type Poly Poly)
 Bool
)

;; Function-Decl delmap_epr::EPRModel::SOMapModel::g_l_b
(declare-fun delmap_epr!EPRModel.impl&%0.g_l_b.? (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)

;; Function-Decl delmap_epr::EPRModel::DMapModel::m
(declare-fun delmap_epr!EPRModel.impl&%1.m.? (Dcr Type Dcr Type Poly Poly Poly) Bool)

;; Function-Decl delmap_epr::EPRModel::DMapModel::lows
(declare-fun delmap_epr!EPRModel.impl&%1.lows.? (Dcr Type Dcr Type Poly) Poly)

;; Function-Decl delmap_epr::EPRModel::DMapModel::new
(declare-fun delmap_epr!EPRModel.impl&%1.new.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl delmap_epr::EPRModel::DMapModel::get
(declare-fun delmap_epr!EPRModel.impl&%1.get.? (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)

;; Function-Decl delmap_epr::EPRModel::DMapModel::get_internal
(declare-fun delmap_epr!EPRModel.impl&%1.get_internal.? (Dcr Type Dcr Type Poly Poly
  Poly Poly
 ) Bool
)

;; Function-Decl delmap_epr::EPRModel::DMapModel::set
(declare-fun delmap_epr!EPRModel.impl&%1.set.? (Dcr Type Dcr Type Poly Poly Poly Poly
  Poly Poly Poly Poly Poly
 ) Bool
)

;; Function-Decl delmap_epr::EPRModel::DMapModel::set_unbounded
(declare-fun delmap_epr!EPRModel.impl&%1.set_unbounded.? (Dcr Type Dcr Type Poly Poly
  Poly Poly Poly
 ) Bool
)

;; Function-Decl delmap_epr::EPRModel::key_zero
(declare-fun delmap_epr!EPRModel.key_zero.? (Dcr Type) Poly)

;; Function-Decl delmap_epr::EPRModel::key_le
(declare-fun delmap_epr!EPRModel.key_le.? (Dcr Type Poly Poly) Bool)

;; Function-Decl delmap_epr::EPRProof::m_has_key
(declare-fun delmap_epr!EPRProof.m_has_key.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl delmap_epr::EPRProof::dmap_invariant
(declare-fun delmap_epr!EPRProof.dmap_invariant.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Axioms delmap_epr::EPRModel::SOMapModel::contains
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%0.contains.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%0.contains.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (k~4@ Poly)) (!
    (= (delmap_epr!EPRModel.impl&%0.contains.? K&. K& ID&. ID& self~2@ k~4@) (exists ((id~12$
        Poly
       )
      ) (!
       (and
        (has_type id~12$ ID&)
        (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~4@ id~12$)
       )
       :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~4@ id~12$))
       :qid user_delmap_epr__EPRModel__SOMapModel__contains_0
       :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__contains_0
    )))
    :pattern ((delmap_epr!EPRModel.impl&%0.contains.? K&. K& ID&. ID& self~2@ k~4@))
    :qid internal_delmap_epr!EPRModel.impl&__0.contains.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__0.contains.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::SOMapModel::erase
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%0.erase.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%0.erase.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (new~4@ Poly) (lo~6@
     Poly
    ) (hi~8@ Poly)
   ) (!
    (= (delmap_epr!EPRModel.impl&%0.erase.? K&. K& ID&. ID& self~2@ new~4@ lo~6@ hi~8@)
     (and
      (forall ((k~17$ Poly) (id~19$ Poly)) (!
        (=>
         (and
          (has_type k~17$ K&)
          (has_type id~19$ ID&)
         )
         (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& new~4@ k~17$ id~19$) (and
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~17$ id~19$)
           (not (and
             (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~17$)
             (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~17$))
        )))))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& new~4@ k~17$ id~19$))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~17$ id~19$))
        :qid user_delmap_epr__EPRModel__SOMapModel__erase_1
        :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__erase_1
      ))
      (forall ((x~68$ Poly) (y~70$ Poly)) (!
        (=>
         (and
          (has_type x~68$ K&)
          (has_type y~70$ K&)
         )
         (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& new~4@ x~68$ y~70$) (or
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~68$ y~70$)
           (and
            (and
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~68$ lo~6@)
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ hi~8@ y~70$)
            )
            (or
             (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
             (not (exists ((id~12$ Poly)) (!
                (and
                 (has_type id~12$ ID&)
                 (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ hi~8@ id~12$)
                )
                :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ hi~8@ id~12$))
                :qid user_delmap_epr__EPRModel__SOMapModel__erase_2
                :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__erase_2
        ))))))))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& new~4@ x~68$ y~70$))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~68$ y~70$))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~68$ lo~6@)
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ hi~8@ y~70$)
        )
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~68$ lo~6@)
         (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
        )
        :qid user_delmap_epr__EPRModel__SOMapModel__erase_3
        :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__erase_3
    ))))
    :pattern ((delmap_epr!EPRModel.impl&%0.erase.? K&. K& ID&. ID& self~2@ new~4@ lo~6@
      hi~8@
    ))
    :qid internal_delmap_epr!EPRModel.impl&__0.erase.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__0.erase.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::SOMapModel::erase_unbounded
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%0.erase_unbounded.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%0.erase_unbounded.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (new~4@ Poly) (lo~6@
     Poly
    )
   ) (!
    (= (delmap_epr!EPRModel.impl&%0.erase_unbounded.? K&. K& ID&. ID& self~2@ new~4@ lo~6@)
     (and
      (forall ((k~15$ Poly) (id~17$ Poly)) (!
        (=>
         (and
          (has_type k~15$ K&)
          (has_type id~17$ ID&)
         )
         (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& new~4@ k~15$ id~17$) (and
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~15$ id~17$)
           (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~15$))
        )))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& new~4@ k~15$ id~17$))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~15$ id~17$))
        :qid user_delmap_epr__EPRModel__SOMapModel__erase_unbounded_4
        :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__erase_unbounded_4
      ))
      (forall ((x~57$ Poly) (y~59$ Poly)) (!
        (=>
         (and
          (has_type x~57$ K&)
          (has_type y~59$ K&)
         )
         (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& new~4@ x~57$ y~59$) (or
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~57$ y~59$)
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~57$ lo~6@)
        )))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& new~4@ x~57$ y~59$))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~57$ y~59$))
        :qid user_delmap_epr__EPRModel__SOMapModel__erase_unbounded_5
        :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__erase_unbounded_5
    ))))
    :pattern ((delmap_epr!EPRModel.impl&%0.erase_unbounded.? K&. K& ID&. ID& self~2@ new~4@
      lo~6@
    ))
    :qid internal_delmap_epr!EPRModel.impl&__0.erase_unbounded.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__0.erase_unbounded.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::SOMapModel::set
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%0.set.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%0.set.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (new~4@ Poly) (key~6@
     Poly
    ) (val~8@ Poly)
   ) (!
    (= (delmap_epr!EPRModel.impl&%0.set.? K&. K& ID&. ID& self~2@ new~4@ key~6@ val~8@)
     (and
      (forall ((k~17$ Poly) (id~19$ Poly)) (!
        (=>
         (and
          (has_type k~17$ K&)
          (has_type id~19$ ID&)
         )
         (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& new~4@ k~17$ id~19$) (ite
           (= key~6@ k~17$)
           (= id~19$ val~8@)
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~17$ id~19$)
        )))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& new~4@ k~17$ id~19$))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~17$ id~19$))
        :qid user_delmap_epr__EPRModel__SOMapModel__set_6
        :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__set_6
      ))
      (forall ((x~74$ Poly) (y~76$ Poly)) (!
        (=>
         (and
          (has_type x~74$ K&)
          (has_type y~76$ K&)
         )
         (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& new~4@ x~74$ y~76$) (and
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~74$ y~76$)
           (not (and
             (not (delmap_epr!EPRModel.key_le.? K&. K& key~6@ x~74$))
             (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ key~6@))
        )))))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& new~4@ x~74$ y~76$))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~74$ y~76$))
        :pattern ((delmap_epr!EPRModel.key_le.? K&. K& key~6@ x~74$) (delmap_epr!EPRModel.key_le.?
          K&. K& y~76$ key~6@
        ))
        :qid user_delmap_epr__EPRModel__SOMapModel__set_7
        :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__set_7
    ))))
    :pattern ((delmap_epr!EPRModel.impl&%0.set.? K&. K& ID&. ID& self~2@ new~4@ key~6@
      val~8@
    ))
    :qid internal_delmap_epr!EPRModel.impl&__0.set.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__0.set.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::SOMapModel::g_l_b
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%0.g_l_b.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%0.g_l_b.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (k~4@ Poly) (glb~6@
     Poly
    )
   ) (!
    (= (delmap_epr!EPRModel.impl&%0.g_l_b.? K&. K& ID&. ID& self~2@ k~4@ glb~6@) (and
      (and
       (and
        (delmap_epr!EPRModel.key_le.? K&. K& glb~6@ k~4@)
        (exists ((id~24$ Poly)) (!
          (and
           (has_type id~24$ ID&)
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ glb~6@ id~24$)
          )
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ glb~6@ id~24$))
          :qid user_delmap_epr__EPRModel__SOMapModel__g_l_b_8
          :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__g_l_b_8
       )))
       (=>
        (exists ((id~46$ Poly)) (!
          (and
           (has_type id~46$ ID&)
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~4@ id~46$)
          )
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~4@ id~46$))
          :qid user_delmap_epr__EPRModel__SOMapModel__g_l_b_9
          :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__g_l_b_9
        ))
        (= glb~6@ k~4@)
      ))
      (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ glb~6@ k~4@)
    ))
    :pattern ((delmap_epr!EPRModel.impl&%0.g_l_b.? K&. K& ID&. ID& self~2@ k~4@ glb~6@))
    :qid internal_delmap_epr!EPRModel.impl&__0.g_l_b.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__0.g_l_b.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::DMapModel::lows
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly)) (!
   (=>
    (has_type self~2@ (TYPE%delmap_epr!EPRModel.DMapModel. K&. K& ID&. ID&))
    (has_type (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& self~2@) (TYPE%delmap_epr!EPRModel.SOMapModel.
      K&. K& ID&. ID&
   )))
   :pattern ((delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& self~2@))
   :qid internal_delmap_epr!EPRModel.impl&__1.lows.?_pre_post_definition
   :skolemid skolem_internal_delmap_epr!EPRModel.impl&__1.lows.?_pre_post_definition
)))

;; Function-Axioms delmap_epr::EPRModel::key_zero
(assert
 (forall ((K&. Dcr) (K& Type)) (!
   (has_type (delmap_epr!EPRModel.key_zero.? K&. K&) K&)
   :pattern ((delmap_epr!EPRModel.key_zero.? K&. K&))
   :qid internal_delmap_epr!EPRModel.key_zero.?_pre_post_definition
   :skolemid skolem_internal_delmap_epr!EPRModel.key_zero.?_pre_post_definition
)))

;; Function-Axioms delmap_epr::EPRModel::DMapModel::new
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%1.new.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%1.new.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (id_zero~4@ Poly))
   (!
    (= (delmap_epr!EPRModel.impl&%1.new.? K&. K& ID&. ID& self~2@ id_zero~4@) (and
      (and
       (forall ((k~14$ Poly) (id~16$ Poly)) (!
         (=>
          (and
           (has_type k~14$ K&)
           (has_type id~16$ ID&)
          )
          (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~14$ id~16$) (= id~16$
            id_zero~4@
         )))
         :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~14$ id~16$))
         :qid user_delmap_epr__EPRModel__DMapModel__new_10
         :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__new_10
       ))
       (forall ((k~48$ Poly) (id~50$ Poly)) (!
         (=>
          (and
           (has_type k~48$ K&)
           (has_type id~50$ ID&)
          )
          (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& self~2@
            ) k~48$ id~50$
           ) (and
            (= k~48$ (delmap_epr!EPRModel.key_zero.? K&. K&))
            (= id~50$ id_zero~4@)
         )))
         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& self~2@
           ) k~48$ id~50$
         ))
         :qid user_delmap_epr__EPRModel__DMapModel__new_11
         :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__new_11
      )))
      (forall ((k~97$ Poly) (j~99$ Poly)) (!
        (=>
         (and
          (has_type k~97$ K&)
          (has_type j~99$ K&)
         )
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& self~2@
          ) k~97$ j~99$
        ))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& self~2@
          ) k~97$ j~99$
        ))
        :qid user_delmap_epr__EPRModel__DMapModel__new_12
        :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__new_12
    ))))
    :pattern ((delmap_epr!EPRModel.impl&%1.new.? K&. K& ID&. ID& self~2@ id_zero~4@))
    :qid internal_delmap_epr!EPRModel.impl&__1.new.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__1.new.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::DMapModel::get_internal
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%1.get_internal.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%1.get_internal.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (k~4@ Poly) (id~6@
     Poly
    ) (glb~8@ Poly)
   ) (!
    (= (delmap_epr!EPRModel.impl&%1.get_internal.? K&. K& ID&. ID& self~2@ k~4@ id~6@ glb~8@)
     (and
      (and
       (and
        (and
         (delmap_epr!EPRModel.key_le.? K&. K& glb~8@ k~4@)
         (exists ((id~24$ Poly)) (!
           (and
            (has_type id~24$ ID&)
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& self~2@
             ) glb~8@ id~24$
           ))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& self~2@
             ) glb~8@ id~24$
           ))
           :qid user_delmap_epr__EPRModel__DMapModel__get_internal_13
           :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__get_internal_13
        )))
        (=>
         (exists ((id~46$ Poly)) (!
           (and
            (has_type id~46$ ID&)
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& self~2@
             ) k~4@ id~46$
           ))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& self~2@
             ) k~4@ id~46$
           ))
           :qid user_delmap_epr__EPRModel__DMapModel__get_internal_14
           :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__get_internal_14
         ))
         (= glb~8@ k~4@)
       ))
       (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
         K&. K& ID&. ID& self~2@
        ) glb~8@ k~4@
      ))
      (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
        K&. K& ID&. ID& self~2@
       ) glb~8@ id~6@
    )))
    :pattern ((delmap_epr!EPRModel.impl&%1.get_internal.? K&. K& ID&. ID& self~2@ k~4@
      id~6@ glb~8@
    ))
    :qid internal_delmap_epr!EPRModel.impl&__1.get_internal.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__1.get_internal.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::DMapModel::get
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%1.get.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%1.get.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (k~4@ Poly) (id~6@
     Poly
    )
   ) (!
    (= (delmap_epr!EPRModel.impl&%1.get.? K&. K& ID&. ID& self~2@ k~4@ id~6@) (exists (
       (glb~14$ Poly)
      ) (!
       (and
        (has_type glb~14$ K&)
        (and
         (and
          (and
           (and
            (delmap_epr!EPRModel.key_le.? K&. K& glb~14$ k~4@)
            (exists ((id~24$ Poly)) (!
              (and
               (has_type id~24$ ID&)
               (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& self~2@
                ) glb~14$ id~24$
              ))
              :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& self~2@
                ) glb~14$ id~24$
              ))
              :qid user_delmap_epr__EPRModel__DMapModel__get_15
              :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__get_15
           )))
           (=>
            (exists ((id~46$ Poly)) (!
              (and
               (has_type id~46$ ID&)
               (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& self~2@
                ) k~4@ id~46$
              ))
              :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& self~2@
                ) k~4@ id~46$
              ))
              :qid user_delmap_epr__EPRModel__DMapModel__get_16
              :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__get_16
            ))
            (= glb~14$ k~4@)
          ))
          (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& self~2@
           ) glb~14$ k~4@
         ))
         (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& self~2@
          ) glb~14$ id~6@
       )))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& glb~14$ k~4@))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& self~2@
         ) glb~14$ k~4@
       ))
       :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& self~2@
         ) glb~14$ id~6@
       ))
       :qid user_delmap_epr__EPRModel__DMapModel__get_17
       :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__get_17
    )))
    :pattern ((delmap_epr!EPRModel.impl&%1.get.? K&. K& ID&. ID& self~2@ k~4@ id~6@))
    :qid internal_delmap_epr!EPRModel.impl&__1.get.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__1.get.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::DMapModel::set
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%1.set.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%1.set.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (new~4@ Poly) (lo~6@
     Poly
    ) (hi~8@ Poly) (dst~10@ Poly) (hi_id~12@ Poly) (hi_glb~14@ Poly) (lows_1~16@ Poly)
    (lows_2~18@ Poly)
   ) (!
    (= (delmap_epr!EPRModel.impl&%1.set.? K&. K& ID&. ID& self~2@ new~4@ lo~6@ hi~8@ dst~10@
      hi_id~12@ hi_glb~14@ lows_1~16@ lows_2~18@
     ) (and
      (and
       (and
        (and
         (and
          (and
           (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ lo~6@))
           (and
            (and
             (and
              (and
               (delmap_epr!EPRModel.key_le.? K&. K& hi_glb~14@ hi~8@)
               (exists ((id~24$ Poly)) (!
                 (and
                  (has_type id~24$ ID&)
                  (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                    K&. K& ID&. ID& self~2@
                   ) hi_glb~14@ id~24$
                 ))
                 :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                    K&. K& ID&. ID& self~2@
                   ) hi_glb~14@ id~24$
                 ))
                 :qid user_delmap_epr__EPRModel__DMapModel__set_18
                 :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_18
              )))
              (=>
               (exists ((id~46$ Poly)) (!
                 (and
                  (has_type id~46$ ID&)
                  (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                    K&. K& ID&. ID& self~2@
                   ) hi~8@ id~46$
                 ))
                 :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                    K&. K& ID&. ID& self~2@
                   ) hi~8@ id~46$
                 ))
                 :qid user_delmap_epr__EPRModel__DMapModel__set_19
                 :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_19
               ))
               (= hi_glb~14@ hi~8@)
             ))
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
               K&. K& ID&. ID& self~2@
              ) hi_glb~14@ hi~8@
            ))
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& self~2@
             ) hi_glb~14@ hi_id~12@
          )))
          (forall ((k~50$ Poly)) (!
            (=>
             (has_type k~50$ K&)
             (=>
              (and
               (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~50$)
               (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~50$))
              )
              (forall ((id~79$ Poly)) (!
                (=>
                 (has_type id~79$ ID&)
                 (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~50$ id~79$) (= id~79$
                   dst~10@
                )))
                :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~50$ id~79$))
                :qid user_delmap_epr__EPRModel__DMapModel__set_20
                :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_20
            ))))
            :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~50$))
            :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~50$))
            :qid user_delmap_epr__EPRModel__DMapModel__set_21
            :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_21
         )))
         (forall ((k~113$ Poly)) (!
           (=>
            (has_type k~113$ K&)
            (=>
             (not (and
               (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~113$)
               (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~113$))
             ))
             (forall ((id~143$ Poly)) (!
               (=>
                (has_type id~143$ ID&)
                (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~113$ id~143$) (delmap_epr!EPRModel.impl&%1.m.?
                  K&. K& ID&. ID& self~2@ k~113$ id~143$
               )))
               :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~113$ id~143$))
               :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~113$ id~143$))
               :qid user_delmap_epr__EPRModel__DMapModel__set_22
               :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_22
           ))))
           :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~113$))
           :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~113$))
           :qid user_delmap_epr__EPRModel__DMapModel__set_23
           :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_23
        )))
        (and
         (forall ((k~17$ Poly) (id~19$ Poly)) (!
           (=>
            (and
             (has_type k~17$ K&)
             (has_type id~19$ ID&)
            )
            (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$) (ite
              (= hi~8@ k~17$)
              (= id~19$ hi_id~12@)
              (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                K&. K& ID&. ID& self~2@
               ) k~17$ id~19$
           ))))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& self~2@
             ) k~17$ id~19$
           ))
           :qid user_delmap_epr__EPRModel__DMapModel__set_24
           :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_24
         ))
         (forall ((x~74$ Poly) (y~76$ Poly)) (!
           (=>
            (and
             (has_type x~74$ K&)
             (has_type y~76$ K&)
            )
            (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~74$ y~76$) (and
              (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                K&. K& ID&. ID& self~2@
               ) x~74$ y~76$
              )
              (not (and
                (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ x~74$))
                (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ hi~8@))
           )))))
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~74$ y~76$))
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& self~2@
             ) x~74$ y~76$
           ))
           :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ x~74$) (delmap_epr!EPRModel.key_le.?
             K&. K& y~76$ hi~8@
           ))
           :qid user_delmap_epr__EPRModel__DMapModel__set_25
           :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_25
       ))))
       (and
        (forall ((k~17$ Poly) (id~19$ Poly)) (!
          (=>
           (and
            (has_type k~17$ K&)
            (has_type id~19$ ID&)
           )
           (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$) (and
             (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$)
             (not (and
               (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~17$)
               (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~17$))
          )))))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$))
          :qid user_delmap_epr__EPRModel__DMapModel__set_26
          :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_26
        ))
        (forall ((x~68$ Poly) (y~70$ Poly)) (!
          (=>
           (and
            (has_type x~68$ K&)
            (has_type y~70$ K&)
           )
           (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~68$ y~70$) (or
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ y~70$)
             (and
              (and
               (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
               (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ hi~8@ y~70$)
              )
              (or
               (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
               (not (exists ((id~12$ Poly)) (!
                  (and
                   (has_type id~12$ ID&)
                   (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ hi~8@ id~12$)
                  )
                  :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ hi~8@ id~12$))
                  :qid user_delmap_epr__EPRModel__DMapModel__set_27
                  :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_27
          ))))))))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~68$ y~70$))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ y~70$))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ hi~8@ y~70$)
          )
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
           (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
          )
          :qid user_delmap_epr__EPRModel__DMapModel__set_28
          :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_28
      ))))
      (and
       (forall ((k~17$ Poly) (id~19$ Poly)) (!
         (=>
          (and
           (has_type k~17$ K&)
           (has_type id~19$ ID&)
          )
          (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& new~4@
            ) k~17$ id~19$
           ) (ite
            (= lo~6@ k~17$)
            (= id~19$ dst~10@)
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$)
         )))
         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& new~4@
           ) k~17$ id~19$
         ))
         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$))
         :qid user_delmap_epr__EPRModel__DMapModel__set_29
         :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_29
       ))
       (forall ((x~74$ Poly) (y~76$ Poly)) (!
         (=>
          (and
           (has_type x~74$ K&)
           (has_type y~76$ K&)
          )
          (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& new~4@
            ) x~74$ y~76$
           ) (and
            (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~74$ y~76$)
            (not (and
              (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$))
              (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ lo~6@))
         )))))
         :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& new~4@
           ) x~74$ y~76$
         ))
         :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~74$ y~76$))
         :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$) (delmap_epr!EPRModel.key_le.?
           K&. K& y~76$ lo~6@
         ))
         :qid user_delmap_epr__EPRModel__DMapModel__set_30
         :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_30
    )))))
    :pattern ((delmap_epr!EPRModel.impl&%1.set.? K&. K& ID&. ID& self~2@ new~4@ lo~6@ hi~8@
      dst~10@ hi_id~12@ hi_glb~14@ lows_1~16@ lows_2~18@
    ))
    :qid internal_delmap_epr!EPRModel.impl&__1.set.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__1.set.?_definition
))))

;; Function-Axioms delmap_epr::EPRModel::DMapModel::set_unbounded
(assert
 (fuel_bool_default fuel%delmap_epr!EPRModel.impl&%1.set_unbounded.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRModel.impl&%1.set_unbounded.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly) (new~4@ Poly) (lo~6@
     Poly
    ) (dst~8@ Poly) (lows_2~10@ Poly)
   ) (!
    (= (delmap_epr!EPRModel.impl&%1.set_unbounded.? K&. K& ID&. ID& self~2@ new~4@ lo~6@
      dst~8@ lows_2~10@
     ) (and
      (and
       (and
        (forall ((k~21$ Poly)) (!
          (=>
           (has_type k~21$ K&)
           (=>
            (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~21$)
            (forall ((id~41$ Poly)) (!
              (=>
               (has_type id~41$ ID&)
               (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~21$ id~41$) (= id~41$
                 dst~8@
              )))
              :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~21$ id~41$))
              :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_31
              :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_31
          ))))
          :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~21$))
          :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_32
          :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_32
        ))
        (forall ((k~75$ Poly)) (!
          (=>
           (has_type k~75$ K&)
           (=>
            (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~75$))
            (forall ((id~96$ Poly)) (!
              (=>
               (has_type id~96$ ID&)
               (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~75$ id~96$) (delmap_epr!EPRModel.impl&%1.m.?
                 K&. K& ID&. ID& self~2@ k~75$ id~96$
              )))
              :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& new~4@ k~75$ id~96$))
              :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~75$ id~96$))
              :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_33
              :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_33
          ))))
          :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~75$))
          :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_34
          :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_34
       )))
       (and
        (forall ((k~15$ Poly) (id~17$ Poly)) (!
          (=>
           (and
            (has_type k~15$ K&)
            (has_type id~17$ ID&)
           )
           (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~15$ id~17$) (and
             (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
               K&. K& ID&. ID& self~2@
              ) k~15$ id~17$
             )
             (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~15$))
          )))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~15$ id~17$))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& self~2@
            ) k~15$ id~17$
          ))
          :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_35
          :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_35
        ))
        (forall ((x~57$ Poly) (y~59$ Poly)) (!
          (=>
           (and
            (has_type x~57$ K&)
            (has_type y~59$ K&)
           )
           (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~57$ y~59$) (or
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
               K&. K& ID&. ID& self~2@
              ) x~57$ y~59$
             )
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
               K&. K& ID&. ID& self~2@
              ) x~57$ lo~6@
          ))))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~57$ y~59$))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& self~2@
            ) x~57$ y~59$
          ))
          :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_36
          :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_36
      ))))
      (and
       (forall ((k~17$ Poly) (id~19$ Poly)) (!
         (=>
          (and
           (has_type k~17$ K&)
           (has_type id~19$ ID&)
          )
          (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& new~4@
            ) k~17$ id~19$
           ) (ite
            (= lo~6@ k~17$)
            (= id~19$ dst~8@)
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~17$ id~19$)
         )))
         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& new~4@
           ) k~17$ id~19$
         ))
         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~17$ id~19$))
         :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_37
         :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_37
       ))
       (forall ((x~74$ Poly) (y~76$ Poly)) (!
         (=>
          (and
           (has_type x~74$ K&)
           (has_type y~76$ K&)
          )
          (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& new~4@
            ) x~74$ y~76$
           ) (and
            (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~74$ y~76$)
            (not (and
              (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$))
              (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ lo~6@))
         )))))
         :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& new~4@
           ) x~74$ y~76$
         ))
         :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~74$ y~76$))
         :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$) (delmap_epr!EPRModel.key_le.?
           K&. K& y~76$ lo~6@
         ))
         :qid user_delmap_epr__EPRModel__DMapModel__set_unbounded_38
         :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__set_unbounded_38
    )))))
    :pattern ((delmap_epr!EPRModel.impl&%1.set_unbounded.? K&. K& ID&. ID& self~2@ new~4@
      lo~6@ dst~8@ lows_2~10@
    ))
    :qid internal_delmap_epr!EPRModel.impl&__1.set_unbounded.?_definition
    :skolemid skolem_internal_delmap_epr!EPRModel.impl&__1.set_unbounded.?_definition
))))

;; Function-Axioms delmap_epr::EPRProof::m_has_key
(assert
 (fuel_bool_default fuel%delmap_epr!EPRProof.m_has_key.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRProof.m_has_key.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (k~4@ Poly)) (!
    (= (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~4@) (exists ((id~12$ Poly))
      (!
       (and
        (has_type id~12$ ID&)
        (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~4@ id~12$)
       )
       :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~4@ id~12$))
       :qid user_delmap_epr__EPRProof__m_has_key_39
       :skolemid skolem_user_delmap_epr__EPRProof__m_has_key_39
    )))
    :pattern ((delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~4@))
    :qid internal_delmap_epr!EPRProof.m_has_key.?_definition
    :skolemid skolem_internal_delmap_epr!EPRProof.m_has_key.?_definition
))))

;; Function-Axioms delmap_epr::EPRProof::dmap_invariant
(assert
 (fuel_bool_default fuel%delmap_epr!EPRProof.dmap_invariant.)
)
(assert
 (=>
  (fuel_bool fuel%delmap_epr!EPRProof.dmap_invariant.)
  (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly)) (!
    (= (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@) (and
      (and
       (and
        (exists ((id~13$ Poly)) (!
          (and
           (has_type id~13$ ID&)
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm~2@
            ) (delmap_epr!EPRModel.key_zero.? K&. K&) id~13$
          ))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm~2@
            ) (delmap_epr!EPRModel.key_zero.? K&. K&) id~13$
          ))
          :qid user_delmap_epr__EPRProof__dmap_invariant_40
          :skolemid skolem_user_delmap_epr__EPRProof__dmap_invariant_40
        ))
        (forall ((k~34$ Poly)) (!
          (=>
           (has_type k~34$ K&)
           (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~34$)
          )
          :pattern ((delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~34$))
          :qid user_delmap_epr__EPRProof__dmap_invariant_41
          :skolemid skolem_user_delmap_epr__EPRProof__dmap_invariant_41
       )))
       (forall ((k~50$ Poly) (id~52$ Poly)) (!
         (=>
          (and
           (has_type k~50$ K&)
           (has_type id~52$ ID&)
          )
          (=>
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm~2@
            ) k~50$ id~52$
           )
           (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~50$ id~52$)
         ))
         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) k~50$ id~52$
         ))
         :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~50$ id~52$))
         :qid user_delmap_epr__EPRProof__dmap_invariant_42
         :skolemid skolem_user_delmap_epr__EPRProof__dmap_invariant_42
      )))
      (forall ((i~85$ Poly) (j~87$ Poly) (id_1~89$ Poly) (id_2~91$ Poly)) (!
        (=>
         (and
          (has_type i~85$ K&)
          (has_type j~87$ K&)
          (has_type id_1~89$ ID&)
          (has_type id_2~91$ ID&)
         )
         (=>
          (and
           (and
            (and
             (and
              (delmap_epr!EPRModel.key_le.? K&. K& i~85$ j~87$)
              (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                K&. K& ID&. ID& dm~2@
               ) i~85$ id_1~89$
             ))
             (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ j~87$ id_2~91$)
            )
            (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm~2@
             ) i~85$ j~87$
           ))
           (not (= id_1~89$ id_2~91$))
          )
          (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) j~87$ id_2~91$
        )))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) i~85$ id_1~89$
         ) (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ j~87$ id_2~91$)
        )
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) i~85$ id_1~89$
         ) (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) j~87$ id_2~91$
        ))
        :qid user_delmap_epr__EPRProof__dmap_invariant_43
        :skolemid skolem_user_delmap_epr__EPRProof__dmap_invariant_43
    ))))
    :pattern ((delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@))
    :qid internal_delmap_epr!EPRProof.dmap_invariant.?_definition
    :skolemid skolem_internal_delmap_epr!EPRProof.dmap_invariant.?_definition
))))

;; Function-Specs delmap_epr::EPRModel::SOMapModel::map_properties
(declare-fun ens%delmap_epr!EPRModel.impl&%0.map_properties. (Dcr Type Dcr Type Poly)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly)) (!
   (= (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& self~2@) (forall
     ((k~16$ Poly) (id_1~18$ Poly) (id_2~20$ Poly)) (!
      (=>
       (and
        (has_type k~16$ K&)
        (has_type id_1~18$ ID&)
        (has_type id_2~20$ ID&)
       )
       (=>
        (and
         (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~16$ id_1~18$)
         (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~16$ id_2~20$)
        )
        (= id_1~18$ id_2~20$)
      ))
      :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~16$ id_1~18$)
       (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ k~16$ id_2~20$)
      )
      :qid user_delmap_epr__EPRModel__SOMapModel__map_properties_44
      :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__map_properties_44
   )))
   :pattern ((ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& self~2@))
   :qid internal_ens__delmap_epr!EPRModel.impl&__0.map_properties._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRModel.impl&__0.map_properties._definition
)))

;; Function-Specs delmap_epr::EPRModel::SOMapModel::gap_properties
(declare-fun ens%delmap_epr!EPRModel.impl&%0.gap_properties. (Dcr Type Dcr Type Poly)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly)) (!
   (= (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& self~2@) (and
     (forall ((w~16$ Poly) (x~18$ Poly) (y~20$ Poly) (z~22$ Poly)) (!
       (=>
        (and
         (has_type w~16$ K&)
         (has_type x~18$ K&)
         (has_type y~20$ K&)
         (has_type z~22$ K&)
        )
        (=>
         (and
          (and
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ w~16$ x~18$)
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ y~20$ z~22$)
          )
          (not (delmap_epr!EPRModel.key_le.? K&. K& x~18$ y~20$))
         )
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ w~16$ z~22$)
       ))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ w~16$ x~18$)
        (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ y~20$ z~22$)
       )
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& x~18$ y~20$) (delmap_epr!EPRModel.impl&%0.gap.?
         K&. K& ID&. ID& self~2@ w~16$ z~22$
       ))
       :qid user_delmap_epr__EPRModel__SOMapModel__gap_properties_45
       :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__gap_properties_45
     ))
     (forall ((x~73$ Poly) (y~75$ Poly) (z~77$ Poly)) (!
       (=>
        (and
         (has_type x~73$ K&)
         (has_type y~75$ K&)
         (has_type z~77$ K&)
        )
        (=>
         (and
          (and
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~73$ y~75$)
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ y~75$ z~77$)
          )
          (not (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~73$ z~77$))
         )
         (exists ((id~12$ Poly)) (!
           (and
            (has_type id~12$ ID&)
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ y~75$ id~12$)
           )
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ y~75$ id~12$))
           :qid user_delmap_epr__EPRModel__SOMapModel__gap_properties_46
           :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__gap_properties_46
       ))))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~73$ y~75$)
        (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ y~75$ z~77$)
       )
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~73$ y~75$)
        (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~73$ z~77$)
       )
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ y~75$ z~77$)
        (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ x~73$ z~77$)
       )
       :qid user_delmap_epr__EPRModel__SOMapModel__gap_properties_47
       :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__gap_properties_47
     ))
     (forall ((w~126$ Poly) (x~128$ Poly) (y~130$ Poly) (z~132$ Poly)) (!
       (=>
        (and
         (has_type w~126$ K&)
         (has_type x~128$ K&)
         (has_type y~130$ K&)
         (has_type z~132$ K&)
        )
        (=>
         (and
          (and
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ w~126$ x~128$)
           (delmap_epr!EPRModel.key_le.? K&. K& w~126$ y~130$)
          )
          (delmap_epr!EPRModel.key_le.? K&. K& z~132$ x~128$)
         )
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ y~130$ z~132$)
       ))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ w~126$ x~128$)
        (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ y~130$ z~132$)
       )
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& w~126$ y~130$) (delmap_epr!EPRModel.key_le.?
         K&. K& z~132$ x~128$
       ))
       :qid user_delmap_epr__EPRModel__SOMapModel__gap_properties_48
       :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__gap_properties_48
     ))
     (forall ((l~181$ Poly) (k~183$ Poly) (m~185$ Poly) (id~187$ Poly)) (!
       (=>
        (and
         (has_type l~181$ K&)
         (has_type k~183$ K&)
         (has_type m~185$ K&)
         (has_type id~187$ ID&)
        )
        (=>
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ k~183$ m~185$)
         (not (and
           (and
            (not (delmap_epr!EPRModel.key_le.? K&. K& l~181$ k~183$))
            (not (delmap_epr!EPRModel.key_le.? K&. K& m~185$ l~181$))
           )
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ l~181$ id~187$)
       ))))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& self~2@ k~183$ m~185$)
        (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ l~181$ id~187$)
       )
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& l~181$ k~183$) (delmap_epr!EPRModel.key_le.?
         K&. K& m~185$ l~181$
        ) (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& self~2@ l~181$ id~187$)
       )
       :qid user_delmap_epr__EPRModel__SOMapModel__gap_properties_49
       :skolemid skolem_user_delmap_epr__EPRModel__SOMapModel__gap_properties_49
   ))))
   :pattern ((ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& self~2@))
   :qid internal_ens__delmap_epr!EPRModel.impl&__0.gap_properties._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRModel.impl&__0.gap_properties._definition
)))

;; Function-Specs delmap_epr::EPRModel::DMapModel::map_properties
(declare-fun ens%delmap_epr!EPRModel.impl&%1.map_properties. (Dcr Type Dcr Type Poly)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (self~2@ Poly)) (!
   (= (ens%delmap_epr!EPRModel.impl&%1.map_properties. K&. K& ID&. ID& self~2@) (forall
     ((k~16$ Poly) (id_1~18$ Poly) (id_2~20$ Poly)) (!
      (=>
       (and
        (has_type k~16$ K&)
        (has_type id_1~18$ ID&)
        (has_type id_2~20$ ID&)
       )
       (=>
        (and
         (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~16$ id_1~18$)
         (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~16$ id_2~20$)
        )
        (= id_1~18$ id_2~20$)
      ))
      :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~16$ id_1~18$)
       (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& self~2@ k~16$ id_2~20$)
      )
      :qid user_delmap_epr__EPRModel__DMapModel__map_properties_50
      :skolemid skolem_user_delmap_epr__EPRModel__DMapModel__map_properties_50
   )))
   :pattern ((ens%delmap_epr!EPRModel.impl&%1.map_properties. K&. K& ID&. ID& self~2@))
   :qid internal_ens__delmap_epr!EPRModel.impl&__1.map_properties._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRModel.impl&__1.map_properties._definition
)))

;; Function-Specs delmap_epr::EPRModel::key_le_properties
(declare-fun ens%delmap_epr!EPRModel.key_le_properties. (Dcr Type) Bool)
(assert
 (forall ((K&. Dcr) (K& Type)) (!
   (= (ens%delmap_epr!EPRModel.key_le_properties. K&. K&) (and
     (forall ((x~14$ Poly)) (!
       (=>
        (has_type x~14$ K&)
        (delmap_epr!EPRModel.key_le.? K&. K& (delmap_epr!EPRModel.key_zero.? K&. K&) x~14$)
       )
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& (delmap_epr!EPRModel.key_zero.? K&. K&)
         x~14$
       ))
       :qid user_delmap_epr__EPRModel__key_le_properties_51
       :skolemid skolem_user_delmap_epr__EPRModel__key_le_properties_51
     ))
     (forall ((x~32$ Poly)) (!
       (=>
        (has_type x~32$ K&)
        (delmap_epr!EPRModel.key_le.? K&. K& x~32$ x~32$)
       )
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& x~32$ x~32$))
       :qid user_delmap_epr__EPRModel__key_le_properties_52
       :skolemid skolem_user_delmap_epr__EPRModel__key_le_properties_52
     ))
     (forall ((x~49$ Poly) (y~51$ Poly) (z~53$ Poly)) (!
       (=>
        (and
         (has_type x~49$ K&)
         (has_type y~51$ K&)
         (has_type z~53$ K&)
        )
        (=>
         (and
          (delmap_epr!EPRModel.key_le.? K&. K& x~49$ y~51$)
          (delmap_epr!EPRModel.key_le.? K&. K& y~51$ z~53$)
         )
         (delmap_epr!EPRModel.key_le.? K&. K& x~49$ z~53$)
       ))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& x~49$ y~51$) (delmap_epr!EPRModel.key_le.?
         K&. K& y~51$ z~53$
       ))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& x~49$ y~51$) (delmap_epr!EPRModel.key_le.?
         K&. K& x~49$ z~53$
       ))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& y~51$ z~53$) (delmap_epr!EPRModel.key_le.?
         K&. K& x~49$ z~53$
       ))
       :qid user_delmap_epr__EPRModel__key_le_properties_53
       :skolemid skolem_user_delmap_epr__EPRModel__key_le_properties_53
     ))
     (forall ((x~94$ Poly) (y~96$ Poly)) (!
       (=>
        (and
         (has_type x~94$ K&)
         (has_type y~96$ K&)
        )
        (=>
         (and
          (delmap_epr!EPRModel.key_le.? K&. K& x~94$ y~96$)
          (delmap_epr!EPRModel.key_le.? K&. K& y~96$ x~94$)
         )
         (= x~94$ y~96$)
       ))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& x~94$ y~96$))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& y~96$ x~94$))
       :qid user_delmap_epr__EPRModel__key_le_properties_54
       :skolemid skolem_user_delmap_epr__EPRModel__key_le_properties_54
     ))
     (forall ((x~137$ Poly) (y~139$ Poly)) (!
       (=>
        (and
         (has_type x~137$ K&)
         (has_type y~139$ K&)
        )
        (or
         (delmap_epr!EPRModel.key_le.? K&. K& x~137$ y~139$)
         (delmap_epr!EPRModel.key_le.? K&. K& y~139$ x~137$)
       ))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& x~137$ y~139$))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& y~139$ x~137$))
       :qid user_delmap_epr__EPRModel__key_le_properties_55
       :skolemid skolem_user_delmap_epr__EPRModel__key_le_properties_55
   ))))
   :pattern ((ens%delmap_epr!EPRModel.key_le_properties. K&. K&))
   :qid internal_ens__delmap_epr!EPRModel.key_le_properties._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRModel.key_le_properties._definition
)))

;; Function-Specs delmap_epr::EPRProof::get_postcondition
(declare-fun req%delmap_epr!EPRProof.get_postcondition. (Dcr Type Dcr Type Poly Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%0 Bool)
(declare-const %%global_location_label%%1 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (k~4@ Poly) (id~6@ Poly))
  (!
   (= (req%delmap_epr!EPRProof.get_postcondition. K&. K& ID&. ID& dm~2@ k~4@ id~6@) (
     and
     (=>
      %%global_location_label%%0
      (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@)
     )
     (=>
      %%global_location_label%%1
      (exists ((glb~14$ Poly)) (!
        (and
         (has_type glb~14$ K&)
         (and
          (and
           (and
            (and
             (delmap_epr!EPRModel.key_le.? K&. K& glb~14$ k~4@)
             (exists ((id~24$ Poly)) (!
               (and
                (has_type id~24$ ID&)
                (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                  K&. K& ID&. ID& dm~2@
                 ) glb~14$ id~24$
               ))
               :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                  K&. K& ID&. ID& dm~2@
                 ) glb~14$ id~24$
               ))
               :qid user_delmap_epr__EPRProof__get_postcondition_56
               :skolemid skolem_user_delmap_epr__EPRProof__get_postcondition_56
            )))
            (=>
             (exists ((id~46$ Poly)) (!
               (and
                (has_type id~46$ ID&)
                (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                  K&. K& ID&. ID& dm~2@
                 ) k~4@ id~46$
               ))
               :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                  K&. K& ID&. ID& dm~2@
                 ) k~4@ id~46$
               ))
               :qid user_delmap_epr__EPRProof__get_postcondition_57
               :skolemid skolem_user_delmap_epr__EPRProof__get_postcondition_57
             ))
             (= glb~14$ k~4@)
           ))
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm~2@
            ) glb~14$ k~4@
          ))
          (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) glb~14$ id~6@
        )))
        :pattern ((delmap_epr!EPRModel.key_le.? K&. K& glb~14$ k~4@))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) glb~14$ k~4@
        ))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) glb~14$ id~6@
        ))
        :qid user_delmap_epr__EPRProof__get_postcondition_58
        :skolemid skolem_user_delmap_epr__EPRProof__get_postcondition_58
   )))))
   :pattern ((req%delmap_epr!EPRProof.get_postcondition. K&. K& ID&. ID& dm~2@ k~4@ id~6@))
   :qid internal_req__delmap_epr!EPRProof.get_postcondition._definition
   :skolemid skolem_internal_req__delmap_epr!EPRProof.get_postcondition._definition
)))
(declare-fun ens%delmap_epr!EPRProof.get_postcondition. (Dcr Type Dcr Type Poly Poly
  Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (k~4@ Poly) (id~6@ Poly))
  (!
   (= (ens%delmap_epr!EPRProof.get_postcondition. K&. K& ID&. ID& dm~2@ k~4@ id~6@) (
     delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~4@ id~6@
   ))
   :pattern ((ens%delmap_epr!EPRProof.get_postcondition. K&. K& ID&. ID& dm~2@ k~4@ id~6@))
   :qid internal_ens__delmap_epr!EPRProof.get_postcondition._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRProof.get_postcondition._definition
)))

;; Function-Def delmap_epr::EPRProof::get_postcondition
;; /Users/andreal1/Src/verus-systems-code/ivy/delmap_epr.rs:1111:5: 1111:111 (#0)
(push)
 (declare-const K&. Dcr)
 (declare-const K& Type)
 (declare-const ID&. Dcr)
 (declare-const ID& Type)
 (declare-const dm~2@ Poly)
 (declare-const k~4@ Poly)
 (declare-const id~6@ Poly)
 (declare-const tmp%1@ Poly)
 (declare-const tmp%2@ Poly)
 (declare-const tmp%3@ Bool)
 (assert
  fuel_defaults
 )
 (assert
  (has_type dm~2@ (TYPE%delmap_epr!EPRModel.DMapModel. K&. K& ID&. ID&))
 )
 (assert
  (has_type k~4@ K&)
 )
 (assert
  (has_type id~6@ ID&)
 )
 (assert
  (tr_bound%delmap_epr!Key. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. ID&. ID&)
 )
 (assert
  (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@)
 )
 (assert
  (exists ((glb~14$ Poly)) (!
    (and
     (has_type glb~14$ K&)
     (and
      (and
       (and
        (and
         (delmap_epr!EPRModel.key_le.? K&. K& glb~14$ k~4@)
         (exists ((id~24$ Poly)) (!
           (and
            (has_type id~24$ ID&)
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm~2@
             ) glb~14$ id~24$
           ))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm~2@
             ) glb~14$ id~24$
           ))
           :qid user_delmap_epr__EPRProof__get_postcondition_59
           :skolemid skolem_user_delmap_epr__EPRProof__get_postcondition_59
        )))
        (=>
         (exists ((id~46$ Poly)) (!
           (and
            (has_type id~46$ ID&)
            (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm~2@
             ) k~4@ id~46$
           ))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm~2@
             ) k~4@ id~46$
           ))
           :qid user_delmap_epr__EPRProof__get_postcondition_60
           :skolemid skolem_user_delmap_epr__EPRProof__get_postcondition_60
         ))
         (= glb~14$ k~4@)
       ))
       (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
         K&. K& ID&. ID& dm~2@
        ) glb~14$ k~4@
      ))
      (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
        K&. K& ID&. ID& dm~2@
       ) glb~14$ id~6@
    )))
    :pattern ((delmap_epr!EPRModel.key_le.? K&. K& glb~14$ k~4@))
    :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
       K&. K& ID&. ID& dm~2@
      ) glb~14$ k~4@
    ))
    :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
       K&. K& ID&. ID& dm~2@
      ) glb~14$ id~6@
    ))
    :qid user_delmap_epr__EPRProof__get_postcondition_61
    :skolemid skolem_user_delmap_epr__EPRProof__get_postcondition_61
 )))
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%1 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (ens%delmap_epr!EPRModel.key_le_properties. K&. K&)
     (=>
      (= tmp%1@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm~2@))
      (=>
       (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& tmp%1@)
       (=>
        (= tmp%2@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm~2@))
        (=>
         (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& tmp%2@)
         (=>
          (ens%delmap_epr!EPRModel.impl&%1.map_properties. K&. K& ID&. ID& dm~2@)
          (=>
           (= tmp%3@ (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~4@))
           (and
            (=>
             %%location_label%%0
             tmp%3@
            )
            (=>
             tmp%3@
             (=>
              %%location_label%%1
              (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~4@ id~6@)
 )))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs delmap_epr::EPRProof::new_preserves_inv
(declare-fun req%delmap_epr!EPRProof.new_preserves_inv. (Dcr Type Dcr Type Poly Poly)
 Bool
)
(declare-const %%global_location_label%%2 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (id_zero~4@ Poly))
  (!
   (= (req%delmap_epr!EPRProof.new_preserves_inv. K&. K& ID&. ID& dm~2@ id_zero~4@) (
     =>
     %%global_location_label%%2
     (and
      (and
       (forall ((k~14$ Poly) (id~16$ Poly)) (!
         (=>
          (and
           (has_type k~14$ K&)
           (has_type id~16$ ID&)
          )
          (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~14$ id~16$) (= id~16$ id_zero~4@))
         )
         :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~14$ id~16$))
         :qid user_delmap_epr__EPRProof__new_preserves_inv_62
         :skolemid skolem_user_delmap_epr__EPRProof__new_preserves_inv_62
       ))
       (forall ((k~48$ Poly) (id~50$ Poly)) (!
         (=>
          (and
           (has_type k~48$ K&)
           (has_type id~50$ ID&)
          )
          (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm~2@
            ) k~48$ id~50$
           ) (and
            (= k~48$ (delmap_epr!EPRModel.key_zero.? K&. K&))
            (= id~50$ id_zero~4@)
         )))
         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) k~48$ id~50$
         ))
         :qid user_delmap_epr__EPRProof__new_preserves_inv_63
         :skolemid skolem_user_delmap_epr__EPRProof__new_preserves_inv_63
      )))
      (forall ((k~97$ Poly) (j~99$ Poly)) (!
        (=>
         (and
          (has_type k~97$ K&)
          (has_type j~99$ K&)
         )
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) k~97$ j~99$
        ))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) k~97$ j~99$
        ))
        :qid user_delmap_epr__EPRProof__new_preserves_inv_64
        :skolemid skolem_user_delmap_epr__EPRProof__new_preserves_inv_64
   )))))
   :pattern ((req%delmap_epr!EPRProof.new_preserves_inv. K&. K& ID&. ID& dm~2@ id_zero~4@))
   :qid internal_req__delmap_epr!EPRProof.new_preserves_inv._definition
   :skolemid skolem_internal_req__delmap_epr!EPRProof.new_preserves_inv._definition
)))
(declare-fun ens%delmap_epr!EPRProof.new_preserves_inv. (Dcr Type Dcr Type Poly Poly)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (id_zero~4@ Poly))
  (!
   (= (ens%delmap_epr!EPRProof.new_preserves_inv. K&. K& ID&. ID& dm~2@ id_zero~4@) (
     delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@
   ))
   :pattern ((ens%delmap_epr!EPRProof.new_preserves_inv. K&. K& ID&. ID& dm~2@ id_zero~4@))
   :qid internal_ens__delmap_epr!EPRProof.new_preserves_inv._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRProof.new_preserves_inv._definition
)))

;; Function-Def delmap_epr::EPRProof::new_preserves_inv
;; /Users/andreal1/Src/verus-systems-code/ivy/delmap_epr.rs:1126:5: 1126:108 (#0)
(push)
 (declare-const K&. Dcr)
 (declare-const K& Type)
 (declare-const ID&. Dcr)
 (declare-const ID& Type)
 (declare-const dm~2@ Poly)
 (declare-const id_zero~4@ Poly)
 (declare-const tmp%1@ Bool)
 (declare-const k~55@ Poly)
 (declare-const tmp%2@ Bool)
 (assert
  fuel_defaults
 )
 (assert
  (has_type dm~2@ (TYPE%delmap_epr!EPRModel.DMapModel. K&. K& ID&. ID&))
 )
 (assert
  (has_type id_zero~4@ ID&)
 )
 (assert
  (tr_bound%delmap_epr!Key. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. ID&. ID&)
 )
 (assert
  (and
   (and
    (forall ((k~14$ Poly) (id~16$ Poly)) (!
      (=>
       (and
        (has_type k~14$ K&)
        (has_type id~16$ ID&)
       )
       (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~14$ id~16$) (= id~16$ id_zero~4@))
      )
      :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~14$ id~16$))
      :qid user_delmap_epr__EPRProof__new_preserves_inv_66
      :skolemid skolem_user_delmap_epr__EPRProof__new_preserves_inv_66
    ))
    (forall ((k~48$ Poly) (id~50$ Poly)) (!
      (=>
       (and
        (has_type k~48$ K&)
        (has_type id~50$ ID&)
       )
       (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& dm~2@
         ) k~48$ id~50$
        ) (and
         (= k~48$ (delmap_epr!EPRModel.key_zero.? K&. K&))
         (= id~50$ id_zero~4@)
      )))
      :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
         K&. K& ID&. ID& dm~2@
        ) k~48$ id~50$
      ))
      :qid user_delmap_epr__EPRProof__new_preserves_inv_67
      :skolemid skolem_user_delmap_epr__EPRProof__new_preserves_inv_67
   )))
   (forall ((k~97$ Poly) (j~99$ Poly)) (!
     (=>
      (and
       (has_type k~97$ K&)
       (has_type j~99$ K&)
      )
      (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
        K&. K& ID&. ID& dm~2@
       ) k~97$ j~99$
     ))
     :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
        K&. K& ID&. ID& dm~2@
       ) k~97$ j~99$
     ))
     :qid user_delmap_epr__EPRProof__new_preserves_inv_68
     :skolemid skolem_user_delmap_epr__EPRProof__new_preserves_inv_68
 ))))
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%3 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= tmp%1@ (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
        K&. K& ID&. ID& dm~2@
       ) (delmap_epr!EPRModel.key_zero.? K&. K&) id_zero~4@
     ))
     (and
      (=>
       %%location_label%%0
       tmp%1@
      )
      (=>
       tmp%1@
       (and
        (=>
         (has_type k~55@ K&)
         (=>
          (= tmp%2@ (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~55@ id_zero~4@))
          (and
           (=>
            %%location_label%%1
            tmp%2@
           )
           (=>
            tmp%2@
            (=>
             %%location_label%%2
             (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~55@)
        )))))
        (=>
         (forall ((k~55$ Poly)) (!
           (=>
            (has_type k~55$ K&)
            (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~55$)
           )
           :pattern ((delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~55$))
           :qid user_delmap_epr__EPRProof__new_preserves_inv_65
           :skolemid skolem_user_delmap_epr__EPRProof__new_preserves_inv_65
         ))
         (=>
          %%location_label%%3
          (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@)
 )))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs delmap_epr::EPRProof::set_postcondition
(declare-fun req%delmap_epr!EPRProof.set_postcondition. (Dcr Type Dcr Type Poly Poly
  Poly Poly Poly Poly Poly Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%3 Bool)
(declare-const %%global_location_label%%4 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (dm_~4@ Poly) (lo~6@
    Poly
   ) (hi~8@ Poly) (dst~10@ Poly) (hi_id~12@ Poly) (hi_glb~14@ Poly) (lows_1~16@ Poly)
   (lows_2~18@ Poly)
  ) (!
   (= (req%delmap_epr!EPRProof.set_postcondition. K&. K& ID&. ID& dm~2@ dm_~4@ lo~6@ hi~8@
     dst~10@ hi_id~12@ hi_glb~14@ lows_1~16@ lows_2~18@
    ) (and
     (=>
      %%global_location_label%%3
      (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@)
     )
     (=>
      %%global_location_label%%4
      (and
       (and
        (and
         (and
          (and
           (and
            (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ lo~6@))
            (and
             (and
              (and
               (and
                (delmap_epr!EPRModel.key_le.? K&. K& hi_glb~14@ hi~8@)
                (exists ((id~24$ Poly)) (!
                  (and
                   (has_type id~24$ ID&)
                   (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                     K&. K& ID&. ID& dm~2@
                    ) hi_glb~14@ id~24$
                  ))
                  :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                     K&. K& ID&. ID& dm~2@
                    ) hi_glb~14@ id~24$
                  ))
                  :qid user_delmap_epr__EPRProof__set_postcondition_69
                  :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_69
               )))
               (=>
                (exists ((id~46$ Poly)) (!
                  (and
                   (has_type id~46$ ID&)
                   (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                     K&. K& ID&. ID& dm~2@
                    ) hi~8@ id~46$
                  ))
                  :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                     K&. K& ID&. ID& dm~2@
                    ) hi~8@ id~46$
                  ))
                  :qid user_delmap_epr__EPRProof__set_postcondition_70
                  :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_70
                ))
                (= hi_glb~14@ hi~8@)
              ))
              (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                K&. K& ID&. ID& dm~2@
               ) hi_glb~14@ hi~8@
             ))
             (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
               K&. K& ID&. ID& dm~2@
              ) hi_glb~14@ hi_id~12@
           )))
           (forall ((k~50$ Poly)) (!
             (=>
              (has_type k~50$ K&)
              (=>
               (and
                (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~50$)
                (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~50$))
               )
               (forall ((id~79$ Poly)) (!
                 (=>
                  (has_type id~79$ ID&)
                  (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~50$ id~79$) (= id~79$
                    dst~10@
                 )))
                 :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~50$ id~79$))
                 :qid user_delmap_epr__EPRProof__set_postcondition_71
                 :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_71
             ))))
             :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~50$))
             :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~50$))
             :qid user_delmap_epr__EPRProof__set_postcondition_72
             :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_72
          )))
          (forall ((k~113$ Poly)) (!
            (=>
             (has_type k~113$ K&)
             (=>
              (not (and
                (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~113$)
                (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~113$))
              ))
              (forall ((id~143$ Poly)) (!
                (=>
                 (has_type id~143$ ID&)
                 (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~113$ id~143$) (delmap_epr!EPRModel.impl&%1.m.?
                   K&. K& ID&. ID& dm~2@ k~113$ id~143$
                )))
                :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~113$ id~143$))
                :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~113$ id~143$))
                :qid user_delmap_epr__EPRProof__set_postcondition_73
                :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_73
            ))))
            :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~113$))
            :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~113$))
            :qid user_delmap_epr__EPRProof__set_postcondition_74
            :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_74
         )))
         (and
          (forall ((k~17$ Poly) (id~19$ Poly)) (!
            (=>
             (and
              (has_type k~17$ K&)
              (has_type id~19$ ID&)
             )
             (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$) (ite
               (= hi~8@ k~17$)
               (= id~19$ hi_id~12@)
               (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& dm~2@
                ) k~17$ id~19$
            ))))
            :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$))
            :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
               K&. K& ID&. ID& dm~2@
              ) k~17$ id~19$
            ))
            :qid user_delmap_epr__EPRProof__set_postcondition_75
            :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_75
          ))
          (forall ((x~74$ Poly) (y~76$ Poly)) (!
            (=>
             (and
              (has_type x~74$ K&)
              (has_type y~76$ K&)
             )
             (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~74$ y~76$) (and
               (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& dm~2@
                ) x~74$ y~76$
               )
               (not (and
                 (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ x~74$))
                 (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ hi~8@))
            )))))
            :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~74$ y~76$))
            :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
               K&. K& ID&. ID& dm~2@
              ) x~74$ y~76$
            ))
            :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ x~74$) (delmap_epr!EPRModel.key_le.?
              K&. K& y~76$ hi~8@
            ))
            :qid user_delmap_epr__EPRProof__set_postcondition_76
            :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_76
        ))))
        (and
         (forall ((k~17$ Poly) (id~19$ Poly)) (!
           (=>
            (and
             (has_type k~17$ K&)
             (has_type id~19$ ID&)
            )
            (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$) (and
              (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$)
              (not (and
                (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~17$)
                (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~17$))
           )))))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$))
           :qid user_delmap_epr__EPRProof__set_postcondition_77
           :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_77
         ))
         (forall ((x~68$ Poly) (y~70$ Poly)) (!
           (=>
            (and
             (has_type x~68$ K&)
             (has_type y~70$ K&)
            )
            (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~68$ y~70$) (or
              (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ y~70$)
              (and
               (and
                (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
                (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ hi~8@ y~70$)
               )
               (or
                (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
                (not (exists ((id~12$ Poly)) (!
                   (and
                    (has_type id~12$ ID&)
                    (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ hi~8@ id~12$)
                   )
                   :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ hi~8@ id~12$))
                   :qid user_delmap_epr__EPRProof__set_postcondition_78
                   :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_78
           ))))))))
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~68$ y~70$))
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ y~70$))
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
            (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ hi~8@ y~70$)
           )
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
            (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
           )
           :qid user_delmap_epr__EPRProof__set_postcondition_79
           :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_79
       ))))
       (and
        (forall ((k~17$ Poly) (id~19$ Poly)) (!
          (=>
           (and
            (has_type k~17$ K&)
            (has_type id~19$ ID&)
           )
           (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm_~4@
             ) k~17$ id~19$
            ) (ite
             (= lo~6@ k~17$)
             (= id~19$ dst~10@)
             (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$)
          )))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm_~4@
            ) k~17$ id~19$
          ))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$))
          :qid user_delmap_epr__EPRProof__set_postcondition_80
          :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_80
        ))
        (forall ((x~74$ Poly) (y~76$ Poly)) (!
          (=>
           (and
            (has_type x~74$ K&)
            (has_type y~76$ K&)
           )
           (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm_~4@
             ) x~74$ y~76$
            ) (and
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~74$ y~76$)
             (not (and
               (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$))
               (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ lo~6@))
          )))))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm_~4@
            ) x~74$ y~76$
          ))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~74$ y~76$))
          :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$) (delmap_epr!EPRModel.key_le.?
            K&. K& y~76$ lo~6@
          ))
          :qid user_delmap_epr__EPRProof__set_postcondition_81
          :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_81
   )))))))
   :pattern ((req%delmap_epr!EPRProof.set_postcondition. K&. K& ID&. ID& dm~2@ dm_~4@
     lo~6@ hi~8@ dst~10@ hi_id~12@ hi_glb~14@ lows_1~16@ lows_2~18@
   ))
   :qid internal_req__delmap_epr!EPRProof.set_postcondition._definition
   :skolemid skolem_internal_req__delmap_epr!EPRProof.set_postcondition._definition
)))
(declare-fun ens%delmap_epr!EPRProof.set_postcondition. (Dcr Type Dcr Type Poly Poly
  Poly Poly Poly Poly Poly Poly Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (dm_~4@ Poly) (lo~6@
    Poly
   ) (hi~8@ Poly) (dst~10@ Poly) (hi_id~12@ Poly) (hi_glb~14@ Poly) (lows_1~16@ Poly)
   (lows_2~18@ Poly)
  ) (!
   (= (ens%delmap_epr!EPRProof.set_postcondition. K&. K& ID&. ID& dm~2@ dm_~4@ lo~6@ hi~8@
     dst~10@ hi_id~12@ hi_glb~14@ lows_1~16@ lows_2~18@
    ) (and
     (forall ((k~64$ Poly)) (!
       (=>
        (has_type k~64$ K&)
        (=>
         (and
          (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~64$)
          (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~64$))
         )
         (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~64$ dst~10@)
       ))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~64$))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~64$))
       :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~64$ dst~10@))
       :qid user_delmap_epr__EPRProof__set_postcondition_82
       :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_82
     ))
     (forall ((k~103$ Poly)) (!
       (=>
        (has_type k~103$ K&)
        (=>
         (not (and
           (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~103$)
           (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~103$))
         ))
         (forall ((id~133$ Poly)) (!
           (=>
            (has_type id~133$ ID&)
            (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~103$ id~133$) (delmap_epr!EPRModel.impl&%1.m.?
              K&. K& ID&. ID& dm~2@ k~103$ id~133$
           )))
           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~103$ id~133$))
           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~103$ id~133$))
           :qid user_delmap_epr__EPRProof__set_postcondition_83
           :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_83
       ))))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~103$))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~103$))
       :qid user_delmap_epr__EPRProof__set_postcondition_84
       :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_84
     ))
     (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm_~4@)
   ))
   :pattern ((ens%delmap_epr!EPRProof.set_postcondition. K&. K& ID&. ID& dm~2@ dm_~4@
     lo~6@ hi~8@ dst~10@ hi_id~12@ hi_glb~14@ lows_1~16@ lows_2~18@
   ))
   :qid internal_ens__delmap_epr!EPRProof.set_postcondition._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRProof.set_postcondition._definition
)))

;; Function-Def delmap_epr::EPRProof::set_postcondition
;; /Users/andreal1/Src/verus-systems-code/ivy/delmap_epr.rs:1139:5: 1139:218 (#0)
(push)
 (declare-const K&. Dcr)
 (declare-const K& Type)
 (declare-const ID&. Dcr)
 (declare-const ID& Type)
 (declare-const dm~2@ Poly)
 (declare-const dm_~4@ Poly)
 (declare-const lo~6@ Poly)
 (declare-const hi~8@ Poly)
 (declare-const dst~10@ Poly)
 (declare-const hi_id~12@ Poly)
 (declare-const hi_glb~14@ Poly)
 (declare-const lows_1~16@ Poly)
 (declare-const lows_2~18@ Poly)
 (declare-const tmp%1@ Poly)
 (declare-const tmp%2@ Poly)
 (declare-const tmp%3@ Poly)
 (declare-const tmp%4@ Poly)
 (declare-const k~237@ Poly)
 (declare-const tmp%5@ Bool)
 (declare-const tmp%6@ Bool)
 (declare-const tmp%7@ Bool)
 (declare-const tmp%8@ Bool)
 (declare-const k~377@ Poly)
 (declare-const id~379@ Poly)
 (declare-const tmp%9@ Bool)
 (assert
  fuel_defaults
 )
 (assert
  (has_type dm~2@ (TYPE%delmap_epr!EPRModel.DMapModel. K&. K& ID&. ID&))
 )
 (assert
  (has_type dm_~4@ (TYPE%delmap_epr!EPRModel.DMapModel. K&. K& ID&. ID&))
 )
 (assert
  (has_type lo~6@ K&)
 )
 (assert
  (has_type hi~8@ K&)
 )
 (assert
  (has_type dst~10@ ID&)
 )
 (assert
  (has_type hi_id~12@ ID&)
 )
 (assert
  (has_type hi_glb~14@ K&)
 )
 (assert
  (has_type lows_1~16@ (TYPE%delmap_epr!EPRModel.SOMapModel. K&. K& ID&. ID&))
 )
 (assert
  (has_type lows_2~18@ (TYPE%delmap_epr!EPRModel.SOMapModel. K&. K& ID&. ID&))
 )
 (assert
  (tr_bound%delmap_epr!Key. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. ID&. ID&)
 )
 (assert
  (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@)
 )
 (assert
  (and
   (and
    (and
     (and
      (and
       (and
        (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ lo~6@))
        (and
         (and
          (and
           (and
            (delmap_epr!EPRModel.key_le.? K&. K& hi_glb~14@ hi~8@)
            (exists ((id~24$ Poly)) (!
              (and
               (has_type id~24$ ID&)
               (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& dm~2@
                ) hi_glb~14@ id~24$
              ))
              :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& dm~2@
                ) hi_glb~14@ id~24$
              ))
              :qid user_delmap_epr__EPRProof__set_postcondition_91
              :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_91
           )))
           (=>
            (exists ((id~46$ Poly)) (!
              (and
               (has_type id~46$ ID&)
               (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& dm~2@
                ) hi~8@ id~46$
              ))
              :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                 K&. K& ID&. ID& dm~2@
                ) hi~8@ id~46$
              ))
              :qid user_delmap_epr__EPRProof__set_postcondition_92
              :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_92
            ))
            (= hi_glb~14@ hi~8@)
          ))
          (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) hi_glb~14@ hi~8@
         ))
         (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) hi_glb~14@ hi_id~12@
       )))
       (forall ((k~50$ Poly)) (!
         (=>
          (has_type k~50$ K&)
          (=>
           (and
            (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~50$)
            (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~50$))
           )
           (forall ((id~79$ Poly)) (!
             (=>
              (has_type id~79$ ID&)
              (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~50$ id~79$) (= id~79$
                dst~10@
             )))
             :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~50$ id~79$))
             :qid user_delmap_epr__EPRProof__set_postcondition_93
             :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_93
         ))))
         :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~50$))
         :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~50$))
         :qid user_delmap_epr__EPRProof__set_postcondition_94
         :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_94
      )))
      (forall ((k~113$ Poly)) (!
        (=>
         (has_type k~113$ K&)
         (=>
          (not (and
            (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~113$)
            (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~113$))
          ))
          (forall ((id~143$ Poly)) (!
            (=>
             (has_type id~143$ ID&)
             (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~113$ id~143$) (delmap_epr!EPRModel.impl&%1.m.?
               K&. K& ID&. ID& dm~2@ k~113$ id~143$
            )))
            :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~113$ id~143$))
            :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~113$ id~143$))
            :qid user_delmap_epr__EPRProof__set_postcondition_95
            :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_95
        ))))
        :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~113$))
        :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~113$))
        :qid user_delmap_epr__EPRProof__set_postcondition_96
        :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_96
     )))
     (and
      (forall ((k~17$ Poly) (id~19$ Poly)) (!
        (=>
         (and
          (has_type k~17$ K&)
          (has_type id~19$ ID&)
         )
         (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$) (ite
           (= hi~8@ k~17$)
           (= id~19$ hi_id~12@)
           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm~2@
            ) k~17$ id~19$
        ))))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$))
        :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) k~17$ id~19$
        ))
        :qid user_delmap_epr__EPRProof__set_postcondition_97
        :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_97
      ))
      (forall ((x~74$ Poly) (y~76$ Poly)) (!
        (=>
         (and
          (has_type x~74$ K&)
          (has_type y~76$ K&)
         )
         (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~74$ y~76$) (and
           (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm~2@
            ) x~74$ y~76$
           )
           (not (and
             (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ x~74$))
             (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ hi~8@))
        )))))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~74$ y~76$))
        :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
           K&. K& ID&. ID& dm~2@
          ) x~74$ y~76$
        ))
        :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ x~74$) (delmap_epr!EPRModel.key_le.?
          K&. K& y~76$ hi~8@
        ))
        :qid user_delmap_epr__EPRProof__set_postcondition_98
        :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_98
    ))))
    (and
     (forall ((k~17$ Poly) (id~19$ Poly)) (!
       (=>
        (and
         (has_type k~17$ K&)
         (has_type id~19$ ID&)
        )
        (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$) (and
          (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$)
          (not (and
            (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~17$)
            (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~17$))
       )))))
       :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$))
       :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ k~17$ id~19$))
       :qid user_delmap_epr__EPRProof__set_postcondition_99
       :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_99
     ))
     (forall ((x~68$ Poly) (y~70$ Poly)) (!
       (=>
        (and
         (has_type x~68$ K&)
         (has_type y~70$ K&)
        )
        (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~68$ y~70$) (or
          (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ y~70$)
          (and
           (and
            (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
            (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ hi~8@ y~70$)
           )
           (or
            (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
            (not (exists ((id~12$ Poly)) (!
               (and
                (has_type id~12$ ID&)
                (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ hi~8@ id~12$)
               )
               :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_1~16@ hi~8@ id~12$))
               :qid user_delmap_epr__EPRProof__set_postcondition_100
               :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_100
       ))))))))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~68$ y~70$))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ y~70$))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
        (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ hi~8@ y~70$)
       )
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_1~16@ x~68$ lo~6@)
        (delmap_epr!EPRModel.key_le.? K&. K& y~70$ hi~8@)
       )
       :qid user_delmap_epr__EPRProof__set_postcondition_101
       :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_101
   ))))
   (and
    (forall ((k~17$ Poly) (id~19$ Poly)) (!
      (=>
       (and
        (has_type k~17$ K&)
        (has_type id~19$ ID&)
       )
       (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& dm_~4@
         ) k~17$ id~19$
        ) (ite
         (= lo~6@ k~17$)
         (= id~19$ dst~10@)
         (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$)
      )))
      :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
         K&. K& ID&. ID& dm_~4@
        ) k~17$ id~19$
      ))
      :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~18@ k~17$ id~19$))
      :qid user_delmap_epr__EPRProof__set_postcondition_102
      :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_102
    ))
    (forall ((x~74$ Poly) (y~76$ Poly)) (!
      (=>
       (and
        (has_type x~74$ K&)
        (has_type y~76$ K&)
       )
       (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& dm_~4@
         ) x~74$ y~76$
        ) (and
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~74$ y~76$)
         (not (and
           (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$))
           (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ lo~6@))
      )))))
      :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
         K&. K& ID&. ID& dm_~4@
        ) x~74$ y~76$
      ))
      :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~18@ x~74$ y~76$))
      :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$) (delmap_epr!EPRModel.key_le.?
        K&. K& y~76$ lo~6@
      ))
      :qid user_delmap_epr__EPRProof__set_postcondition_103
      :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_103
 )))))
 (declare-const %%switch_label%%0 Bool)
 (declare-const %%switch_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 ;; assertion failed
 (declare-const %%location_label%%4 Bool)
 ;; assertion failed
 (declare-const %%location_label%%5 Bool)
 ;; assertion failed
 (declare-const %%location_label%%6 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%7 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%8 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%9 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (ens%delmap_epr!EPRModel.key_le_properties. K&. K&)
     (=>
      (= tmp%1@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm~2@))
      (=>
       (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& tmp%1@)
       (=>
        (= tmp%2@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm~2@))
        (=>
         (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& tmp%2@)
         (=>
          (ens%delmap_epr!EPRModel.impl&%1.map_properties. K&. K& ID&. ID& dm~2@)
          (=>
           (= tmp%3@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm_~4@))
           (=>
            (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& tmp%3@)
            (=>
             (= tmp%4@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm_~4@))
             (=>
              (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& tmp%4@)
              (=>
               (ens%delmap_epr!EPRModel.impl&%1.map_properties. K&. K& ID&. ID& dm_~4@)
               (=>
                (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& lows_1~16@)
                (=>
                 (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& lows_1~16@)
                 (=>
                  (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& lows_2~18@)
                  (=>
                   (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& lows_2~18@)
                   (and
                    (=>
                     (has_type k~237@ K&)
                     (or
                      (and
                       (=>
                        (and
                         (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~237@)
                         (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~237@))
                        )
                        (=>
                         (= tmp%5@ (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~237@ dst~10@))
                         (and
                          (=>
                           %%location_label%%0
                           tmp%5@
                          )
                          (=>
                           tmp%5@
                           %%switch_label%%1
                       ))))
                       (=>
                        (not (and
                          (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~237@)
                          (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~237@))
                        ))
                        (=>
                         (= tmp%6@ (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~237@))
                         (and
                          (=>
                           %%location_label%%1
                           tmp%6@
                          )
                          (=>
                           tmp%6@
                           %%switch_label%%1
                      )))))
                      (and
                       (not %%switch_label%%1)
                       (=>
                        %%location_label%%2
                        (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm_~4@ k~237@)
                    ))))
                    (=>
                     (forall ((k~237$ Poly)) (!
                       (=>
                        (has_type k~237$ K&)
                        (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm_~4@ k~237$)
                       )
                       :pattern ((delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm_~4@ k~237$))
                       :qid user_delmap_epr__EPRProof__set_postcondition_88
                       :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_88
                     ))
                     (or
                      (and
                       (=>
                        (= lo~6@ (delmap_epr!EPRModel.key_zero.? K&. K&))
                        (=>
                         (= tmp%7@ (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                            K&. K& ID&. ID& dm_~4@
                           ) (delmap_epr!EPRModel.key_zero.? K&. K&) dst~10@
                         ))
                         (and
                          (=>
                           %%location_label%%3
                           tmp%7@
                          )
                          (=>
                           tmp%7@
                           %%switch_label%%0
                       ))))
                       (=>
                        (not (= lo~6@ (delmap_epr!EPRModel.key_zero.? K&. K&)))
                        (=>
                         (= tmp%8@ (exists ((id~352$ Poly)) (!
                            (and
                             (has_type id~352$ ID&)
                             (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                               K&. K& ID&. ID& dm_~4@
                              ) (delmap_epr!EPRModel.key_zero.? K&. K&) id~352$
                            ))
                            :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                               K&. K& ID&. ID& dm_~4@
                              ) (delmap_epr!EPRModel.key_zero.? K&. K&) id~352$
                            ))
                            :qid user_delmap_epr__EPRProof__set_postcondition_89
                            :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_89
                         )))
                         (and
                          (=>
                           %%location_label%%4
                           tmp%8@
                          )
                          (=>
                           tmp%8@
                           %%switch_label%%0
                      )))))
                      (and
                       (not %%switch_label%%0)
                       (and
                        (=>
                         (has_type k~377@ K&)
                         (=>
                          (has_type id~379@ ID&)
                          (=>
                           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                             K&. K& ID&. ID& dm_~4@
                            ) k~377@ id~379@
                           )
                           (=>
                            (= tmp%9@ (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~377@))
                            (and
                             (=>
                              %%location_label%%5
                              tmp%9@
                             )
                             (=>
                              tmp%9@
                              (=>
                               %%location_label%%6
                               (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~377@ id~379@)
                        )))))))
                        (=>
                         (forall ((k~377$ Poly) (id~379$ Poly)) (!
                           (=>
                            (and
                             (has_type k~377$ K&)
                             (has_type id~379$ ID&)
                            )
                            (=>
                             (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                               K&. K& ID&. ID& dm_~4@
                              ) k~377$ id~379$
                             )
                             (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~377$ id~379$)
                           ))
                           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                              K&. K& ID&. ID& dm_~4@
                             ) k~377$ id~379$
                           ))
                           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~377$ id~379$))
                           :qid user_delmap_epr__EPRProof__set_postcondition_90
                           :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_90
                         ))
                         (and
                          (=>
                           %%location_label%%7
                           (forall ((k~64$ Poly)) (!
                             (=>
                              (has_type k~64$ K&)
                              (=>
                               (and
                                (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~64$)
                                (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~64$))
                               )
                               (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~64$ dst~10@)
                             ))
                             :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~64$))
                             :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~64$))
                             :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~64$ dst~10@))
                             :qid user_delmap_epr__EPRProof__set_postcondition_85
                             :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_85
                          )))
                          (and
                           (=>
                            %%location_label%%8
                            (forall ((k~103$ Poly)) (!
                              (=>
                               (has_type k~103$ K&)
                               (=>
                                (not (and
                                  (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~103$)
                                  (not (delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~103$))
                                ))
                                (forall ((id~133$ Poly)) (!
                                  (=>
                                   (has_type id~133$ ID&)
                                   (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~103$ id~133$) (delmap_epr!EPRModel.impl&%1.m.?
                                     K&. K& ID&. ID& dm~2@ k~103$ id~133$
                                  )))
                                  :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~103$ id~133$))
                                  :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~103$ id~133$))
                                  :qid user_delmap_epr__EPRProof__set_postcondition_86
                                  :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_86
                              ))))
                              :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~103$))
                              :pattern ((delmap_epr!EPRModel.key_le.? K&. K& hi~8@ k~103$))
                              :qid user_delmap_epr__EPRProof__set_postcondition_87
                              :skolemid skolem_user_delmap_epr__EPRProof__set_postcondition_87
                           )))
                           (=>
                            %%location_label%%9
                            (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm_~4@)
 )))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs delmap_epr::EPRProof::set_unbounded_postcondition
(declare-fun req%delmap_epr!EPRProof.set_unbounded_postcondition. (Dcr Type Dcr Type
  Poly Poly Poly Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%5 Bool)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (dm_~4@ Poly) (lo~6@
    Poly
   ) (dst~8@ Poly) (lows_2~10@ Poly)
  ) (!
   (= (req%delmap_epr!EPRProof.set_unbounded_postcondition. K&. K& ID&. ID& dm~2@ dm_~4@
     lo~6@ dst~8@ lows_2~10@
    ) (and
     (=>
      %%global_location_label%%5
      (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@)
     )
     (=>
      %%global_location_label%%6
      (and
       (and
        (and
         (forall ((k~21$ Poly)) (!
           (=>
            (has_type k~21$ K&)
            (=>
             (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~21$)
             (forall ((id~41$ Poly)) (!
               (=>
                (has_type id~41$ ID&)
                (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~21$ id~41$) (= id~41$
                  dst~8@
               )))
               :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~21$ id~41$))
               :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_104
               :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_104
           ))))
           :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~21$))
           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_105
           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_105
         ))
         (forall ((k~75$ Poly)) (!
           (=>
            (has_type k~75$ K&)
            (=>
             (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~75$))
             (forall ((id~96$ Poly)) (!
               (=>
                (has_type id~96$ ID&)
                (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~75$ id~96$) (delmap_epr!EPRModel.impl&%1.m.?
                  K&. K& ID&. ID& dm~2@ k~75$ id~96$
               )))
               :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~75$ id~96$))
               :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~75$ id~96$))
               :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_106
               :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_106
           ))))
           :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~75$))
           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_107
           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_107
        )))
        (and
         (forall ((k~15$ Poly) (id~17$ Poly)) (!
           (=>
            (and
             (has_type k~15$ K&)
             (has_type id~17$ ID&)
            )
            (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~15$ id~17$) (and
              (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                K&. K& ID&. ID& dm~2@
               ) k~15$ id~17$
              )
              (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~15$))
           )))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~15$ id~17$))
           :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm~2@
             ) k~15$ id~17$
           ))
           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_108
           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_108
         ))
         (forall ((x~57$ Poly) (y~59$ Poly)) (!
           (=>
            (and
             (has_type x~57$ K&)
             (has_type y~59$ K&)
            )
            (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~57$ y~59$) (or
              (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                K&. K& ID&. ID& dm~2@
               ) x~57$ y~59$
              )
              (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                K&. K& ID&. ID& dm~2@
               ) x~57$ lo~6@
           ))))
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~57$ y~59$))
           :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm~2@
             ) x~57$ y~59$
           ))
           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_109
           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_109
       ))))
       (and
        (forall ((k~17$ Poly) (id~19$ Poly)) (!
          (=>
           (and
            (has_type k~17$ K&)
            (has_type id~19$ ID&)
           )
           (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm_~4@
             ) k~17$ id~19$
            ) (ite
             (= lo~6@ k~17$)
             (= id~19$ dst~8@)
             (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~17$ id~19$)
          )))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm_~4@
            ) k~17$ id~19$
          ))
          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~17$ id~19$))
          :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_110
          :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_110
        ))
        (forall ((x~74$ Poly) (y~76$ Poly)) (!
          (=>
           (and
            (has_type x~74$ K&)
            (has_type y~76$ K&)
           )
           (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
              K&. K& ID&. ID& dm_~4@
             ) x~74$ y~76$
            ) (and
             (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~74$ y~76$)
             (not (and
               (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$))
               (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ lo~6@))
          )))))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
             K&. K& ID&. ID& dm_~4@
            ) x~74$ y~76$
          ))
          :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~74$ y~76$))
          :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$) (delmap_epr!EPRModel.key_le.?
            K&. K& y~76$ lo~6@
          ))
          :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_111
          :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_111
   )))))))
   :pattern ((req%delmap_epr!EPRProof.set_unbounded_postcondition. K&. K& ID&. ID& dm~2@
     dm_~4@ lo~6@ dst~8@ lows_2~10@
   ))
   :qid internal_req__delmap_epr!EPRProof.set_unbounded_postcondition._definition
   :skolemid skolem_internal_req__delmap_epr!EPRProof.set_unbounded_postcondition._definition
)))
(declare-fun ens%delmap_epr!EPRProof.set_unbounded_postcondition. (Dcr Type Dcr Type
  Poly Poly Poly Poly Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (ID&. Dcr) (ID& Type) (dm~2@ Poly) (dm_~4@ Poly) (lo~6@
    Poly
   ) (dst~8@ Poly) (lows_2~10@ Poly)
  ) (!
   (= (ens%delmap_epr!EPRProof.set_unbounded_postcondition. K&. K& ID&. ID& dm~2@ dm_~4@
     lo~6@ dst~8@ lows_2~10@
    ) (and
     (forall ((k~48$ Poly)) (!
       (=>
        (has_type k~48$ K&)
        (=>
         (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~48$)
         (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~48$ dst~8@)
       ))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~48$))
       :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~48$ dst~8@))
       :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_112
       :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_112
     ))
     (forall ((k~78$ Poly)) (!
       (=>
        (has_type k~78$ K&)
        (=>
         (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~78$))
         (forall ((id~99$ Poly)) (!
           (=>
            (has_type id~99$ ID&)
            (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~78$ id~99$) (delmap_epr!EPRModel.impl&%1.m.?
              K&. K& ID&. ID& dm~2@ k~78$ id~99$
           )))
           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~78$ id~99$))
           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~78$ id~99$))
           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_113
           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_113
       ))))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~78$))
       :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_114
       :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_114
     ))
     (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm_~4@)
   ))
   :pattern ((ens%delmap_epr!EPRProof.set_unbounded_postcondition. K&. K& ID&. ID& dm~2@
     dm_~4@ lo~6@ dst~8@ lows_2~10@
   ))
   :qid internal_ens__delmap_epr!EPRProof.set_unbounded_postcondition._definition
   :skolemid skolem_internal_ens__delmap_epr!EPRProof.set_unbounded_postcondition._definition
)))

;; Function-Def delmap_epr::EPRProof::set_unbounded_postcondition
;; /Users/andreal1/Src/verus-systems-code/ivy/delmap_epr.rs:1177:5: 1177:170 (#0)
(push)
 (declare-const K&. Dcr)
 (declare-const K& Type)
 (declare-const ID&. Dcr)
 (declare-const ID& Type)
 (declare-const dm~2@ Poly)
 (declare-const dm_~4@ Poly)
 (declare-const lo~6@ Poly)
 (declare-const dst~8@ Poly)
 (declare-const lows_2~10@ Poly)
 (declare-const tmp%1@ Poly)
 (declare-const tmp%2@ Poly)
 (declare-const tmp%3@ Poly)
 (declare-const tmp%4@ Poly)
 (declare-const k~193@ Poly)
 (declare-const tmp%5@ Bool)
 (declare-const tmp%6@ Bool)
 (declare-const tmp%7@ Bool)
 (declare-const tmp%8@ Bool)
 (declare-const k~324@ Poly)
 (declare-const id~326@ Poly)
 (declare-const tmp%9@ Bool)
 (declare-const tmp%10@ Bool)
 (assert
  fuel_defaults
 )
 (assert
  (has_type dm~2@ (TYPE%delmap_epr!EPRModel.DMapModel. K&. K& ID&. ID&))
 )
 (assert
  (has_type dm_~4@ (TYPE%delmap_epr!EPRModel.DMapModel. K&. K& ID&. ID&))
 )
 (assert
  (has_type lo~6@ K&)
 )
 (assert
  (has_type dst~8@ ID&)
 )
 (assert
  (has_type lows_2~10@ (TYPE%delmap_epr!EPRModel.SOMapModel. K&. K& ID&. ID&))
 )
 (assert
  (tr_bound%delmap_epr!Key. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. K&. K&)
 )
 (assert
  (tr_bound%delmap_epr!VerusClone. ID&. ID&)
 )
 (assert
  (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm~2@)
 )
 (assert
  (and
   (and
    (and
     (forall ((k~21$ Poly)) (!
       (=>
        (has_type k~21$ K&)
        (=>
         (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~21$)
         (forall ((id~41$ Poly)) (!
           (=>
            (has_type id~41$ ID&)
            (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~21$ id~41$) (= id~41$
              dst~8@
           )))
           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~21$ id~41$))
           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_121
           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_121
       ))))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~21$))
       :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_122
       :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_122
     ))
     (forall ((k~75$ Poly)) (!
       (=>
        (has_type k~75$ K&)
        (=>
         (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~75$))
         (forall ((id~96$ Poly)) (!
           (=>
            (has_type id~96$ ID&)
            (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~75$ id~96$) (delmap_epr!EPRModel.impl&%1.m.?
              K&. K& ID&. ID& dm~2@ k~75$ id~96$
           )))
           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~75$ id~96$))
           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~75$ id~96$))
           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_123
           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_123
       ))))
       :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~75$))
       :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_124
       :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_124
    )))
    (and
     (forall ((k~15$ Poly) (id~17$ Poly)) (!
       (=>
        (and
         (has_type k~15$ K&)
         (has_type id~17$ ID&)
        )
        (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~15$ id~17$) (and
          (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) k~15$ id~17$
          )
          (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~15$))
       )))
       :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~15$ id~17$))
       :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& dm~2@
         ) k~15$ id~17$
       ))
       :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_125
       :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_125
     ))
     (forall ((x~57$ Poly) (y~59$ Poly)) (!
       (=>
        (and
         (has_type x~57$ K&)
         (has_type y~59$ K&)
        )
        (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~57$ y~59$) (or
          (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) x~57$ y~59$
          )
          (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
            K&. K& ID&. ID& dm~2@
           ) x~57$ lo~6@
       ))))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~57$ y~59$))
       :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& dm~2@
         ) x~57$ y~59$
       ))
       :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_126
       :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_126
   ))))
   (and
    (forall ((k~17$ Poly) (id~19$ Poly)) (!
      (=>
       (and
        (has_type k~17$ K&)
        (has_type id~19$ ID&)
       )
       (= (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& dm_~4@
         ) k~17$ id~19$
        ) (ite
         (= lo~6@ k~17$)
         (= id~19$ dst~8@)
         (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~17$ id~19$)
      )))
      :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
         K&. K& ID&. ID& dm_~4@
        ) k~17$ id~19$
      ))
      :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& lows_2~10@ k~17$ id~19$))
      :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_127
      :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_127
    ))
    (forall ((x~74$ Poly) (y~76$ Poly)) (!
      (=>
       (and
        (has_type x~74$ K&)
        (has_type y~76$ K&)
       )
       (= (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
          K&. K& ID&. ID& dm_~4@
         ) x~74$ y~76$
        ) (and
         (delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~74$ y~76$)
         (not (and
           (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$))
           (not (delmap_epr!EPRModel.key_le.? K&. K& y~76$ lo~6@))
      )))))
      :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
         K&. K& ID&. ID& dm_~4@
        ) x~74$ y~76$
      ))
      :pattern ((delmap_epr!EPRModel.impl&%0.gap.? K&. K& ID&. ID& lows_2~10@ x~74$ y~76$))
      :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ x~74$) (delmap_epr!EPRModel.key_le.?
        K&. K& y~76$ lo~6@
      ))
      :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_128
      :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_128
 )))))
 (declare-const %%switch_label%%0 Bool)
 (declare-const %%switch_label%%1 Bool)
 (declare-const %%switch_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 ;; assertion failed
 (declare-const %%location_label%%4 Bool)
 ;; assertion failed
 (declare-const %%location_label%%5 Bool)
 ;; assertion failed
 (declare-const %%location_label%%6 Bool)
 ;; assertion failed
 (declare-const %%location_label%%7 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%8 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%9 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%10 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (ens%delmap_epr!EPRModel.key_le_properties. K&. K&)
     (=>
      (= tmp%1@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm~2@))
      (=>
       (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& tmp%1@)
       (=>
        (= tmp%2@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm~2@))
        (=>
         (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& tmp%2@)
         (=>
          (ens%delmap_epr!EPRModel.impl&%1.map_properties. K&. K& ID&. ID& dm~2@)
          (=>
           (= tmp%3@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm_~4@))
           (=>
            (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& tmp%3@)
            (=>
             (= tmp%4@ (delmap_epr!EPRModel.impl&%1.lows.? K&. K& ID&. ID& dm_~4@))
             (=>
              (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& tmp%4@)
              (=>
               (ens%delmap_epr!EPRModel.impl&%1.map_properties. K&. K& ID&. ID& dm_~4@)
               (=>
                (ens%delmap_epr!EPRModel.impl&%0.map_properties. K&. K& ID&. ID& lows_2~10@)
                (=>
                 (ens%delmap_epr!EPRModel.impl&%0.gap_properties. K&. K& ID&. ID& lows_2~10@)
                 (and
                  (=>
                   (has_type k~193@ K&)
                   (or
                    (and
                     (=>
                      (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~193@)
                      (=>
                       (= tmp%5@ (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~193@ dst~8@))
                       (and
                        (=>
                         %%location_label%%0
                         tmp%5@
                        )
                        (=>
                         tmp%5@
                         %%switch_label%%2
                     ))))
                     (=>
                      (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~193@))
                      (=>
                       (= tmp%6@ (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~193@))
                       (and
                        (=>
                         %%location_label%%1
                         tmp%6@
                        )
                        (=>
                         tmp%6@
                         %%switch_label%%2
                    )))))
                    (and
                     (not %%switch_label%%2)
                     (=>
                      %%location_label%%2
                      (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm_~4@ k~193@)
                  ))))
                  (=>
                   (forall ((k~193$ Poly)) (!
                     (=>
                      (has_type k~193$ K&)
                      (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm_~4@ k~193$)
                     )
                     :pattern ((delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm_~4@ k~193$))
                     :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_118
                     :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_118
                   ))
                   (or
                    (and
                     (=>
                      (= lo~6@ (delmap_epr!EPRModel.key_zero.? K&. K&))
                      (=>
                       (= tmp%7@ (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                          K&. K& ID&. ID& dm_~4@
                         ) (delmap_epr!EPRModel.key_zero.? K&. K&) dst~8@
                       ))
                       (and
                        (=>
                         %%location_label%%3
                         tmp%7@
                        )
                        (=>
                         tmp%7@
                         %%switch_label%%1
                     ))))
                     (=>
                      (not (= lo~6@ (delmap_epr!EPRModel.key_zero.? K&. K&)))
                      (=>
                       (= tmp%8@ (exists ((id~299$ Poly)) (!
                          (and
                           (has_type id~299$ ID&)
                           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                             K&. K& ID&. ID& dm_~4@
                            ) (delmap_epr!EPRModel.key_zero.? K&. K&) id~299$
                          ))
                          :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                             K&. K& ID&. ID& dm_~4@
                            ) (delmap_epr!EPRModel.key_zero.? K&. K&) id~299$
                          ))
                          :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_119
                          :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_119
                       )))
                       (and
                        (=>
                         %%location_label%%4
                         tmp%8@
                        )
                        (=>
                         tmp%8@
                         %%switch_label%%1
                    )))))
                    (and
                     (not %%switch_label%%1)
                     (and
                      (=>
                       (has_type k~324@ K&)
                       (=>
                        (has_type id~326@ ID&)
                        (=>
                         (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                           K&. K& ID&. ID& dm_~4@
                          ) k~324@ id~326@
                         )
                         (or
                          (and
                           (=>
                            (= k~324@ lo~6@)
                            (=>
                             (= tmp%9@ (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~324@))
                             (and
                              (=>
                               %%location_label%%5
                               tmp%9@
                              )
                              (=>
                               tmp%9@
                               %%switch_label%%0
                           ))))
                           (=>
                            (not (= k~324@ lo~6@))
                            (=>
                             (= tmp%10@ (delmap_epr!EPRProof.m_has_key.? K&. K& ID&. ID& dm~2@ k~324@))
                             (and
                              (=>
                               %%location_label%%6
                               tmp%10@
                              )
                              (=>
                               tmp%10@
                               %%switch_label%%0
                          )))))
                          (and
                           (not %%switch_label%%0)
                           (=>
                            %%location_label%%7
                            (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~324@ id~326@)
                      ))))))
                      (=>
                       (forall ((k~324$ Poly) (id~326$ Poly)) (!
                         (=>
                          (and
                           (has_type k~324$ K&)
                           (has_type id~326$ ID&)
                          )
                          (=>
                           (delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                             K&. K& ID&. ID& dm_~4@
                            ) k~324$ id~326$
                           )
                           (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~324$ id~326$)
                         ))
                         :pattern ((delmap_epr!EPRModel.impl&%0.m.? K&. K& ID&. ID& (delmap_epr!EPRModel.impl&%1.lows.?
                            K&. K& ID&. ID& dm_~4@
                           ) k~324$ id~326$
                         ))
                         :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~324$ id~326$))
                         :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_120
                         :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_120
                       ))
                       (and
                        (=>
                         %%location_label%%8
                         (forall ((k~48$ Poly)) (!
                           (=>
                            (has_type k~48$ K&)
                            (=>
                             (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~48$)
                             (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~48$ dst~8@)
                           ))
                           :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~48$))
                           :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~48$ dst~8@))
                           :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_115
                           :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_115
                        )))
                        (and
                         (=>
                          %%location_label%%9
                          (forall ((k~78$ Poly)) (!
                            (=>
                             (has_type k~78$ K&)
                             (=>
                              (not (delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~78$))
                              (forall ((id~99$ Poly)) (!
                                (=>
                                 (has_type id~99$ ID&)
                                 (= (delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~78$ id~99$) (delmap_epr!EPRModel.impl&%1.m.?
                                   K&. K& ID&. ID& dm~2@ k~78$ id~99$
                                )))
                                :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm_~4@ k~78$ id~99$))
                                :pattern ((delmap_epr!EPRModel.impl&%1.m.? K&. K& ID&. ID& dm~2@ k~78$ id~99$))
                                :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_116
                                :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_116
                            ))))
                            :pattern ((delmap_epr!EPRModel.key_le.? K&. K& lo~6@ k~78$))
                            :qid user_delmap_epr__EPRProof__set_unbounded_postcondition_117
                            :skolemid skolem_user_delmap_epr__EPRProof__set_unbounded_postcondition_117
                         )))
                         (=>
                          %%location_label%%10
                          (delmap_epr!EPRProof.dmap_invariant.? K&. K& ID&. ID& dm_~4@)
 )))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)
