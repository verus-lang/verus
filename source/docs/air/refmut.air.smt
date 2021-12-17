(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)

;; AIR prelude
(declare-sort %%Function%%)

(declare-sort FuelId)
(declare-sort Fuel)
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
))))
(declare-sort Poly)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun F (%%Function%%) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %F (Poly) %%Function%%)
(declare-sort Type)
(declare-const BOOL Type)
(declare-const FUN Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
)))
(assert
 (forall ((x %%Function%%)) (!
   (= x (%F (F x)))
   :pattern ((F x))
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x FUN)
    (= x (F (%F x)))
   )
   :pattern ((has_type x FUN))
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
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
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
)))
(declare-fun check_decrease_int.? (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int.? cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int.? cur prev otherwise))
)))
(declare-fun height.? (Poly) Int)
(assert
 (forall ((x Poly)) (!
   (<= 0 (height.? x))
   :pattern ((height.? x))
)))
(push)
 (assert
  true
 )
 (declare-datatypes () ((tuple%0. (tuple%0./tuple%0))))
 (declare-const TYPE%tuple%0. Type)
 (declare-fun Poly%tuple%0. (tuple%0.) Poly)
 (declare-fun %Poly%tuple%0. (Poly) tuple%0.)
 (assert
  (forall ((x@ tuple%0.)) (!
    (= x@ (%Poly%tuple%0. (Poly%tuple%0. x@)))
    :pattern ((Poly%tuple%0. x@))
 )))
 (assert
  (forall ((x@ Poly)) (!
    (=>
     (has_type x@ TYPE%tuple%0.)
     (= x@ (Poly%tuple%0. (%Poly%tuple%0. x@)))
    )
    :pattern ((has_type x@ TYPE%tuple%0.))
 )))
 (assert
  (forall ((x@ tuple%0.)) (!
    (has_type (Poly%tuple%0. x@) TYPE%tuple%0.)
    :pattern ((has_type (Poly%tuple%0. x@) TYPE%tuple%0.))
 )))
 (declare-fun ens%add1. (Int Int) Bool)
 (assert
  (forall ((pre%a@ Int) (a@ Int)) (!
    (= (ens%add1. pre%a@ a@) (and
      (uInv 64 a@)
      (= a@ (uClip 64 (+ pre%a@ 1)))
    ))
    :pattern ((ens%add1. pre%a@ a@))
 )))
 (push)
  (declare-const a@0 Int)
  (assert
   fuel_defaults
  )
  (assert
   (uInv 64 a@0)
  )
  (declare-const a@1 Int)
  ;; test.rs:8:13: 8:34 (#0)
  (declare-const %%location_label%%0 Bool)
  (assert
   (not (=>
     (= a@1 (uClip 64 (+ a@0 1)))
     (=>
      %%location_label%%0
      (= a@1 (uClip 64 (+ a@0 1)))
  ))))
  (set-option :rlimit 0)
  (check-sat)
  (set-option :rlimit 0)
 (pop)
(pop)
