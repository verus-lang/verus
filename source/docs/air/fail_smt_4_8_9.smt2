(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)

;; Prelude

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
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-sort Type)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(assert
 (has_type (B true) BOOL)
)
(assert
 (has_type (B false) BOOL)
)
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
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
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
(declare-fun uintxor (Int Int) Int)
(declare-fun uintand (Int Int) Int)
(declare-fun uintor (Int Int) Int)
(declare-fun uintshr (Int Int) Int)
(declare-fun uintshl (Int Int) Int)
(declare-fun uintnot (Int) Int)

;; MODULE ''
(push)

 ;; Fuel
 (assert
  true
 )

 ;; Datatypes
 (declare-sort seq.Seq<int.>.)
 (declare-datatypes () ((tuple%0. (tuple%0./tuple%0))))
 (declare-fun TYPE%seq.Seq. (Type) Type)
 (declare-const TYPE%tuple%0. Type)
 (declare-fun Poly%seq.Seq<int.>. (seq.Seq<int.>.) Poly)
 (declare-fun %Poly%seq.Seq<int.>. (Poly) seq.Seq<int.>.)
 (declare-fun Poly%tuple%0. (tuple%0.) Poly)
 (declare-fun %Poly%tuple%0. (Poly) tuple%0.)
 (assert
  (forall ((x@ seq.Seq<int.>.)) (!
    (= x@ (%Poly%seq.Seq<int.>. (Poly%seq.Seq<int.>. x@)))
    :pattern ((Poly%seq.Seq<int.>. x@))
 )))
 (assert
  (forall ((x@ Poly)) (!
    (=>
     (has_type x@ (TYPE%seq.Seq. INT))
     (= x@ (Poly%seq.Seq<int.>. (%Poly%seq.Seq<int.>. x@)))
    )
    :pattern ((has_type x@ (TYPE%seq.Seq. INT)))
 )))
 (assert
  (forall ((x@ seq.Seq<int.>.)) (!
    (has_type (Poly%seq.Seq<int.>. x@) (TYPE%seq.Seq. INT))
    :pattern ((has_type (Poly%seq.Seq<int.>. x@) (TYPE%seq.Seq. INT)))
 )))
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

 ;; Function-Decl crate::seq::seq_empty
 (declare-fun seq.seq_empty.? (Type) Poly)

 ;; Function-Decl crate::seq::Seq::len
 (declare-fun seq.Seq.len.? (Type Poly) Int)

 ;; Function-Decl crate::seq::Seq::index
 (declare-fun seq.Seq.index.? (Type Poly Poly) Poly)

 ;; Function-Decl crate::seq::Seq::push
 (declare-fun seq.Seq.push.? (Type Poly Poly) Poly)

 ;; Function-Axioms crate::seq::seq_empty
 (assert
  (forall ((A& Type)) (!
    (has_type (seq.seq_empty.? A&) (TYPE%seq.Seq. A&))
    :pattern ((seq.seq_empty.? A&))
 )))

 ;; Function-Axioms crate::seq::Seq::len
 (assert
  (forall ((A& Type) (self@ Poly)) (!
    (=>
     (has_type self@ (TYPE%seq.Seq. A&))
     (<= 0 (seq.Seq.len.? A& self@))
    )
    :pattern ((seq.Seq.len.? A& self@))
 )))

 ;; Function-Axioms crate::seq::Seq::index
 (assert
  (forall ((A& Type) (self@ Poly) (i@ Poly)) (!
    (=>
     (and
      (has_type self@ (TYPE%seq.Seq. A&))
      (has_type i@ INT)
     )
     (has_type (seq.Seq.index.? A& self@ i@) A&)
    )
    :pattern ((seq.Seq.index.? A& self@ i@))
 )))

 ;; Function-Axioms crate::seq::Seq::push
 (assert
  (forall ((A& Type) (self@ Poly) (a@ Poly)) (!
    (=>
     (and
      (has_type self@ (TYPE%seq.Seq. A&))
      (has_type a@ A&)
     )
     (has_type (seq.Seq.push.? A& self@ a@) (TYPE%seq.Seq. A&))
    )
    :pattern ((seq.Seq.push.? A& self@ a@))
 )))

 ;; Function-Axioms crate::seq::axiom_seq_empty
 (declare-fun ens%seq.axiom_seq_empty. (Type) Bool)
 (assert
  (forall ((A& Type)) (!
    (= (ens%seq.axiom_seq_empty. A&) (= (seq.Seq.len.? A& (seq.seq_empty.? A&)) 0))
    :pattern ((ens%seq.axiom_seq_empty. A&))
 )))
 (assert
  (forall ((A& Type)) (!
    (= (seq.Seq.len.? A& (seq.seq_empty.? A&)) 0)
    :pattern ((seq.Seq.len.? A& (seq.seq_empty.? A&)))
 )))

 ;; Function-Axioms crate::seq::axiom_seq_push_len
 (declare-fun ens%seq.axiom_seq_push_len. (Type Poly Poly) Bool)
 (assert
  (forall ((A& Type) (s@ Poly) (a@ Poly)) (!
    (= (ens%seq.axiom_seq_push_len. A& s@ a@) (= (seq.Seq.len.? A& (seq.Seq.push.? A& s@
        a@
       )
      ) (nClip (+ (seq.Seq.len.? A& s@) 1))
    ))
    :pattern ((ens%seq.axiom_seq_push_len. A& s@ a@))
 )))
 (assert
  (forall ((A& Type) (s$ Poly) (a$ Poly)) (!
    (=>
     (and
      (has_type s$ (TYPE%seq.Seq. A&))
      (has_type a$ A&)
     )
     (= (seq.Seq.len.? A& (seq.Seq.push.? A& s$ a$)) (nClip (+ (seq.Seq.len.? A& s$) 1)))
    )
    :pattern ((seq.Seq.len.? A& (seq.Seq.push.? A& s$ a$)))
 )))

 ;; Function-Axioms crate::seq::axiom_seq_push_index_same
 (declare-fun ens%seq.axiom_seq_push_index_same. (Type Poly Poly) Bool)
 (assert
  (forall ((A& Type) (s@ Poly) (a@ Poly)) (!
    (= (ens%seq.axiom_seq_push_index_same. A& s@ a@) (= (seq.Seq.index.? A& (seq.Seq.push.?
        A& s@ a@
       ) (I (seq.Seq.len.? A& s@))
      ) a@
    ))
    :pattern ((ens%seq.axiom_seq_push_index_same. A& s@ a@))
 )))
 (assert
  (forall ((A& Type) (s$ Poly) (a$ Poly)) (!
    (=>
     (and
      (has_type s$ (TYPE%seq.Seq. A&))
      (has_type a$ A&)
     )
     (= (seq.Seq.index.? A& (seq.Seq.push.? A& s$ a$) (I (seq.Seq.len.? A& s$))) a$)
    )
    :pattern ((seq.Seq.index.? A& (seq.Seq.push.? A& s$ a$) (I (seq.Seq.len.? A& s$))))
 )))

 ;; Function-Axioms crate::seq::axiom_seq_push_index_different
 (declare-fun req%seq.axiom_seq_push_index_different. (Type Poly Poly Int) Bool)
 (declare-const %%global_location_label%%0 Bool)
 (declare-const %%global_location_label%%1 Bool)
 (assert
  (forall ((A& Type) (s@ Poly) (a@ Poly) (i@ Int)) (!
    (= (req%seq.axiom_seq_push_index_different. A& s@ a@ i@) (and
      (=>
       %%global_location_label%%0
       (<= 0 i@)
      )
      (=>
       %%global_location_label%%1
       (< i@ (seq.Seq.len.? A& s@))
    )))
    :pattern ((req%seq.axiom_seq_push_index_different. A& s@ a@ i@))
 )))
 (declare-fun ens%seq.axiom_seq_push_index_different. (Type Poly Poly Int) Bool)
 (assert
  (forall ((A& Type) (s@ Poly) (a@ Poly) (i@ Int)) (!
    (= (ens%seq.axiom_seq_push_index_different. A& s@ a@ i@) (= (seq.Seq.index.? A& (seq.Seq.push.?
        A& s@ a@
       ) (I i@)
      ) (seq.Seq.index.? A& s@ (I i@))
    ))
    :pattern ((ens%seq.axiom_seq_push_index_different. A& s@ a@ i@))
 )))
 (assert
  (forall ((A& Type) (s$ Poly) (a$ Poly) (i$ Int)) (!
    (=>
     (and
      (has_type s$ (TYPE%seq.Seq. A&))
      (has_type a$ A&)
     )
     (=>
      (and
       (<= 0 i$)
       (< i$ (seq.Seq.len.? A& s$))
      )
      (= (seq.Seq.index.? A& (seq.Seq.push.? A& s$ a$) (I i$)) (seq.Seq.index.? A& s$ (I i$)))
    ))
    :pattern ((seq.Seq.index.? A& (seq.Seq.push.? A& s$ a$) (I i$)))
 )))

 ;; Function-Axioms crate::sl
 (declare-fun req%sl. (seq.Seq<int.>.) Bool)
 (declare-const %%global_location_label%%2 Bool)
 (assert
  (forall ((s@ seq.Seq<int.>.)) (!
    (= (req%sl. s@) (=>
      %%global_location_label%%2
      (= s@ (%Poly%seq.Seq<int.>. (seq.Seq.push.? INT (seq.seq_empty.? INT) (I 7))))
    ))
    :pattern ((req%sl. s@))
 )))
 (declare-fun ens%sl. (seq.Seq<int.>.) Bool)
 (assert
  (forall ((s@ seq.Seq<int.>.)) (!
    (= (ens%sl. s@) (= (%I (seq.Seq.index.? INT (Poly%seq.Seq<int.>. s@) (I 0))) 7))
    :pattern ((ens%sl. s@))
 )))

 ;; Function-Def crate::sl
 (push)
  (declare-const s@ seq.Seq<int.>.)
  (assert
   fuel_defaults
  )
  (assert
   (= s@ (%Poly%seq.Seq<int.>. (seq.Seq.push.? INT (seq.seq_empty.? INT) (I 7))))
  )
  ;; postcondition not satisfied
  (declare-const %%location_label%%0 Bool)
  (assert
   (not (=>
     %%location_label%%0
     (= (%I (seq.Seq.index.? INT (Poly%seq.Seq<int.>. s@) (I 0))) 7)
  )))
  (set-option :rlimit 0)
  (check-sat)
  (set-option :rlimit 0)
 (pop)
(pop)
