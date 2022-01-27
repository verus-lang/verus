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
 (declare-const fuel%M.sequence_is_sorted. FuelId)
 (declare-const fuel%M.tree_as_sequence. FuelId)
 (assert
  (distinct fuel%M.sequence_is_sorted. fuel%M.tree_as_sequence.)
 )

 ;; Datatypes
 (declare-sort seq.Seq<u64.>.)
 (declare-datatypes () ((M.Tree. (M.Tree./Nil) (M.Tree./Node (M.Tree./Node/?value Int)
     (M.Tree./Node/?left M.Tree.) (M.Tree./Node/?right M.Tree.)
    )
   ) (tuple%0. (tuple%0./tuple%0))
 ))
 (declare-fun M.Tree./Node/value (M.Tree.) Int)
 (declare-fun M.Tree./Node/left (M.Tree.) M.Tree.)
 (declare-fun M.Tree./Node/right (M.Tree.) M.Tree.)
 (declare-fun TYPE%seq.Seq. (Type) Type)
 (declare-const TYPE%M.Tree. Type)
 (declare-const TYPE%tuple%0. Type)
 (declare-fun Poly%seq.Seq<u64.>. (seq.Seq<u64.>.) Poly)
 (declare-fun %Poly%seq.Seq<u64.>. (Poly) seq.Seq<u64.>.)
 (declare-fun Poly%M.Tree. (M.Tree.) Poly)
 (declare-fun %Poly%M.Tree. (Poly) M.Tree.)
 (declare-fun Poly%tuple%0. (tuple%0.) Poly)
 (declare-fun %Poly%tuple%0. (Poly) tuple%0.)
 (assert
  (forall ((x@ seq.Seq<u64.>.)) (!
    (= x@ (%Poly%seq.Seq<u64.>. (Poly%seq.Seq<u64.>. x@)))
    :pattern ((Poly%seq.Seq<u64.>. x@))
 )))
 (assert
  (forall ((x@ Poly)) (!
    (=>
     (has_type x@ (TYPE%seq.Seq. (UINT 64)))
     (= x@ (Poly%seq.Seq<u64.>. (%Poly%seq.Seq<u64.>. x@)))
    )
    :pattern ((has_type x@ (TYPE%seq.Seq. (UINT 64))))
 )))
 (assert
  (forall ((x@ seq.Seq<u64.>.)) (!
    (has_type (Poly%seq.Seq<u64.>. x@) (TYPE%seq.Seq. (UINT 64)))
    :pattern ((has_type (Poly%seq.Seq<u64.>. x@) (TYPE%seq.Seq. (UINT 64))))
 )))
 (assert
  (forall ((x@ M.Tree.)) (!
    (= x@ (%Poly%M.Tree. (Poly%M.Tree. x@)))
    :pattern ((Poly%M.Tree. x@))
 )))
 (assert
  (forall ((x@ Poly)) (!
    (=>
     (has_type x@ TYPE%M.Tree.)
     (= x@ (Poly%M.Tree. (%Poly%M.Tree. x@)))
    )
    :pattern ((has_type x@ TYPE%M.Tree.))
 )))
 (assert
  (has_type (Poly%M.Tree. M.Tree./Nil) TYPE%M.Tree.)
 )
 (assert
  (forall ((value@ Int) (left@ M.Tree.) (right@ M.Tree.)) (!
    (=>
     (and
      (uInv 64 value@)
      (has_type (Poly%M.Tree. left@) TYPE%M.Tree.)
      (has_type (Poly%M.Tree. right@) TYPE%M.Tree.)
     )
     (has_type (Poly%M.Tree. (M.Tree./Node value@ left@ right@)) TYPE%M.Tree.)
    )
    :pattern ((has_type (Poly%M.Tree. (M.Tree./Node value@ left@ right@)) TYPE%M.Tree.))
 )))
 (assert
  (forall ((x@ M.Tree.)) (!
    (= (M.Tree./Node/value x@) (M.Tree./Node/?value x@))
    :pattern ((M.Tree./Node/value x@))
 )))
 (assert
  (forall ((x@ Poly)) (!
    (=>
     (has_type x@ TYPE%M.Tree.)
     (uInv 64 (M.Tree./Node/value (%Poly%M.Tree. x@)))
    )
    :pattern ((M.Tree./Node/value (%Poly%M.Tree. x@)) (has_type x@ TYPE%M.Tree.))
 )))
 (assert
  (forall ((x@ M.Tree.)) (!
    (= (M.Tree./Node/left x@) (M.Tree./Node/?left x@))
    :pattern ((M.Tree./Node/left x@))
 )))
 (assert
  (forall ((x@ Poly)) (!
    (=>
     (has_type x@ TYPE%M.Tree.)
     (has_type (Poly%M.Tree. (M.Tree./Node/left (%Poly%M.Tree. x@))) TYPE%M.Tree.)
    )
    :pattern ((M.Tree./Node/left (%Poly%M.Tree. x@)) (has_type x@ TYPE%M.Tree.))
 )))
 (assert
  (forall ((x@ M.Tree.)) (!
    (= (M.Tree./Node/right x@) (M.Tree./Node/?right x@))
    :pattern ((M.Tree./Node/right x@))
 )))
 (assert
  (forall ((x@ Poly)) (!
    (=>
     (has_type x@ TYPE%M.Tree.)
     (has_type (Poly%M.Tree. (M.Tree./Node/right (%Poly%M.Tree. x@))) TYPE%M.Tree.)
    )
    :pattern ((M.Tree./Node/right (%Poly%M.Tree. x@)) (has_type x@ TYPE%M.Tree.))
 )))
 (assert
  (forall ((x M.Tree.)) (!
    (< (height.? (Poly%M.Tree. (M.Tree./Node/left x))) (height.? (Poly%M.Tree. x)))
    :pattern ((height.? (Poly%M.Tree. (M.Tree./Node/left x))))
 )))
 (assert
  (forall ((x M.Tree.)) (!
    (< (height.? (Poly%M.Tree. (M.Tree./Node/right x))) (height.? (Poly%M.Tree. x)))
    :pattern ((height.? (Poly%M.Tree. (M.Tree./Node/right x))))
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

 ;; Function-Decl crate::seq::Seq::add
 (declare-fun seq.Seq.add.? (Type Poly Poly) Poly)

 ;; Function-Decl crate::M::sequence_is_sorted
 (declare-fun M.sequence_is_sorted.? (Poly) Bool)

 ;; Function-Decl crate::M::tree_as_sequence
 (declare-fun M.tree_as_sequence.? (Poly) seq.Seq<u64.>.)
 (declare-fun M.rec%tree_as_sequence.? (Poly Fuel) seq.Seq<u64.>.)

 ;; Function-Axioms crate::pervasive::assume
 (declare-fun ens%pervasive.assume. (Bool) Bool)
 (assert
  (forall ((b@ Bool)) (!
    (= (ens%pervasive.assume. b@) b@)
    :pattern ((ens%pervasive.assume. b@))
 )))

 ;; Function-Axioms crate::pervasive::assert
 (declare-fun req%pervasive.assert. (Bool) Bool)
 (assert
  (forall ((b@ Bool)) (!
    (= (req%pervasive.assert. b@) b@)
    :pattern ((req%pervasive.assert. b@))
 )))
 (declare-fun ens%pervasive.assert. (Bool) Bool)
 (assert
  (forall ((b@ Bool)) (!
    (= (ens%pervasive.assert. b@) b@)
    :pattern ((ens%pervasive.assert. b@))
 )))

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

 ;; Function-Axioms crate::seq::Seq::add
 (assert
  (forall ((A& Type) (self@ Poly) (rhs@ Poly)) (!
    (=>
     (and
      (has_type self@ (TYPE%seq.Seq. A&))
      (has_type rhs@ (TYPE%seq.Seq. A&))
     )
     (has_type (seq.Seq.add.? A& self@ rhs@) (TYPE%seq.Seq. A&))
    )
    :pattern ((seq.Seq.add.? A& self@ rhs@))
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
 (declare-fun ens%seq.axiom_seq_push_index_different. (Type Poly Poly Int) Bool)
 (assert
  (forall ((A& Type) (s@ Poly) (a@ Poly) (i@ Int)) (!
    (= (ens%seq.axiom_seq_push_index_different. A& s@ a@ i@) (=>
      (and
       (<= 0 i@)
       (< i@ (seq.Seq.len.? A& s@))
      )
      (= (seq.Seq.index.? A& (seq.Seq.push.? A& s@ a@) (I i@)) (seq.Seq.index.? A& s@ (I i@)))
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

 ;; Function-Axioms crate::seq::axiom_seq_add_len
 (declare-fun ens%seq.axiom_seq_add_len. (Type Poly Poly) Bool)
 (assert
  (forall ((A& Type) (s1@ Poly) (s2@ Poly)) (!
    (= (ens%seq.axiom_seq_add_len. A& s1@ s2@) (= (seq.Seq.len.? A& (seq.Seq.add.? A& s1@
        s2@
       )
      ) (nClip (+ (seq.Seq.len.? A& s1@) (seq.Seq.len.? A& s2@)))
    ))
    :pattern ((ens%seq.axiom_seq_add_len. A& s1@ s2@))
 )))
 (assert
  (forall ((A& Type) (s1$ Poly) (s2$ Poly)) (!
    (=>
     (and
      (has_type s1$ (TYPE%seq.Seq. A&))
      (has_type s2$ (TYPE%seq.Seq. A&))
     )
     (= (seq.Seq.len.? A& (seq.Seq.add.? A& s1$ s2$)) (nClip (+ (seq.Seq.len.? A& s1$) (seq.Seq.len.?
         A& s2$
    )))))
    :pattern ((seq.Seq.len.? A& (seq.Seq.add.? A& s1$ s2$)))
 )))

 ;; Function-Axioms crate::seq::axiom_seq_add_index1
 (declare-fun ens%seq.axiom_seq_add_index1. (Type Poly Poly Int) Bool)
 (assert
  (forall ((A& Type) (s1@ Poly) (s2@ Poly) (i@ Int)) (!
    (= (ens%seq.axiom_seq_add_index1. A& s1@ s2@ i@) (=>
      (and
       (<= 0 i@)
       (< i@ (seq.Seq.len.? A& s1@))
      )
      (= (seq.Seq.index.? A& (seq.Seq.add.? A& s1@ s2@) (I i@)) (seq.Seq.index.? A& s1@ (
         I i@
    )))))
    :pattern ((ens%seq.axiom_seq_add_index1. A& s1@ s2@ i@))
 )))
 (assert
  (forall ((A& Type) (s1$ Poly) (s2$ Poly) (i$ Int)) (!
    (=>
     (and
      (has_type s1$ (TYPE%seq.Seq. A&))
      (has_type s2$ (TYPE%seq.Seq. A&))
     )
     (=>
      (and
       (<= 0 i$)
       (< i$ (seq.Seq.len.? A& s1$))
      )
      (= (seq.Seq.index.? A& (seq.Seq.add.? A& s1$ s2$) (I i$)) (seq.Seq.index.? A& s1$ (
         I i$
    )))))
    :pattern ((seq.Seq.index.? A& (seq.Seq.add.? A& s1$ s2$) (I i$)))
 )))

 ;; Function-Axioms crate::seq::axiom_seq_add_index2
 (declare-fun ens%seq.axiom_seq_add_index2. (Type Poly Poly Int) Bool)
 (assert
  (forall ((A& Type) (s1@ Poly) (s2@ Poly) (i@ Int)) (!
    (= (ens%seq.axiom_seq_add_index2. A& s1@ s2@ i@) (=>
      (and
       (<= 0 (seq.Seq.len.? A& s1@))
       (< i@ (+ (seq.Seq.len.? A& s1@) (seq.Seq.len.? A& s2@)))
      )
      (= (seq.Seq.index.? A& (seq.Seq.add.? A& s1@ s2@) (I i@)) (seq.Seq.index.? A& s2@ (
         I (- i@ (seq.Seq.len.? A& s1@))
    )))))
    :pattern ((ens%seq.axiom_seq_add_index2. A& s1@ s2@ i@))
 )))
 (assert
  (forall ((A& Type) (s1$ Poly) (s2$ Poly) (i$ Int)) (!
    (=>
     (and
      (has_type s1$ (TYPE%seq.Seq. A&))
      (has_type s2$ (TYPE%seq.Seq. A&))
     )
     (=>
      (and
       (<= 0 (seq.Seq.len.? A& s1$))
       (< i$ (+ (seq.Seq.len.? A& s1$) (seq.Seq.len.? A& s2$)))
      )
      (= (seq.Seq.index.? A& (seq.Seq.add.? A& s1$ s2$) (I i$)) (seq.Seq.index.? A& s2$ (
         I (- i$ (seq.Seq.len.? A& s1$))
    )))))
    :pattern ((seq.Seq.index.? A& (seq.Seq.add.? A& s1$ s2$) (I i$)))
 )))

 ;; Function-Axioms crate::M::sequence_is_sorted
 (assert
  (fuel_bool_default fuel%M.sequence_is_sorted.)
 )
 (assert
  (=>
   (fuel_bool fuel%M.sequence_is_sorted.)
   (forall ((s@ Poly)) (!
     (= (M.sequence_is_sorted.? s@) (forall ((i$ Poly) (j$ Poly)) (!
        (=>
         (and
          (has_type i$ NAT)
          (has_type j$ NAT)
         )
         (=>
          (and
           (<= (%I i$) (%I j$))
           (< (%I j$) (seq.Seq.len.? (UINT 64) s@))
          )
          (<= (%I (seq.Seq.index.? (UINT 64) s@ i$)) (%I (seq.Seq.index.? (UINT 64) s@ j$)))
        ))
        :pattern ((seq.Seq.index.? (UINT 64) s@ j$) (seq.Seq.index.? (UINT 64) s@ i$))
     )))
     :pattern ((M.sequence_is_sorted.? s@))
 ))))

 ;; Function-Axioms crate::M::tree_as_sequence
 (assert
  (fuel_bool_default fuel%M.tree_as_sequence.)
 )
 (declare-const fuel_nat%M.tree_as_sequence. Fuel)
 (assert
  (forall ((tree@ Poly) (fuel%@ Fuel)) (!
    (= (M.rec%tree_as_sequence.? tree@ fuel%@) (M.rec%tree_as_sequence.? tree@ zero))
    :pattern ((M.rec%tree_as_sequence.? tree@ fuel%@))
 )))
 (assert
  (forall ((tree@ Poly) (fuel%@ Fuel)) (!
    (= (M.rec%tree_as_sequence.? tree@ (succ fuel%@)) (%Poly%seq.Seq<u64.>. (ite
       (is-M.Tree./Nil (%Poly%M.Tree. tree@))
       (seq.seq_empty.? (UINT 64))
       (let
        ((value$ (M.Tree./Node/value (%Poly%M.Tree. tree@))))
        (let
         ((left$ (M.Tree./Node/left (%Poly%M.Tree. tree@))))
         (let
          ((right$ (M.Tree./Node/right (%Poly%M.Tree. tree@))))
          (seq.Seq.add.? (UINT 64) (seq.Seq.add.? (UINT 64) (Poly%seq.Seq<u64.>. (M.rec%tree_as_sequence.?
              (Poly%M.Tree. left$) fuel%@
             )
            ) (seq.Seq.push.? (UINT 64) (seq.seq_empty.? (UINT 64)) (I value$))
           ) (Poly%seq.Seq<u64.>. (M.rec%tree_as_sequence.? (Poly%M.Tree. right$) fuel%@))
    )))))))
    :pattern ((M.rec%tree_as_sequence.? tree@ (succ fuel%@)))
 )))
 (assert
  (=>
   (fuel_bool fuel%M.tree_as_sequence.)
   (forall ((tree@ Poly)) (!
     (= (M.tree_as_sequence.? tree@) (M.rec%tree_as_sequence.? tree@ (succ fuel_nat%M.tree_as_sequence.)))
     :pattern ((M.tree_as_sequence.? tree@))
 ))))

 ;; Function-Axioms crate::unstable
 (declare-fun ens%unstable. (Int M.Tree. Int) Bool)
 (assert
  (forall ((min@ Int) (tree@ M.Tree.) (max@ Int)) (!
    (= (ens%unstable. min@ tree@ max@) (let
      ((s$ (M.tree_as_sequence.? (Poly%M.Tree. tree@))))
      (and
       (forall ((i$ Poly)) (!
         (=>
          (has_type i$ NAT)
          (=>
           (< (%I i$) (seq.Seq.len.? (UINT 64) (Poly%seq.Seq<u64.>. s$)))
           (and
            (<= min@ (%I (seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s$) i$)))
            (<= (%I (seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s$) i$)) max@)
         )))
         :pattern ((seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s$) i$))
       ))
       (M.sequence_is_sorted.? (Poly%seq.Seq<u64.>. (M.tree_as_sequence.? (Poly%M.Tree. tree@))))
    )))
    :pattern ((ens%unstable. min@ tree@ max@))
 )))

 ;; Function-Def crate::unstable
 (push)
  (declare-const min@ Int)
  (declare-const tree@ M.Tree.)
  (declare-const max@ Int)
  (declare-const tmp%1@ Bool)
  (declare-const tmp%2@ Bool)
  (declare-const tmp%3@ Bool)
  (declare-const s@ seq.Seq<u64.>.)
  (declare-const value@ Int)
  (declare-const left@ M.Tree.)
  (declare-const right@ M.Tree.)
  (declare-const decrease%init0@ Int)
  (assert
   fuel_defaults
  )
  (assert
   (uInv 64 min@)
  )
  (assert
   (has_type (Poly%M.Tree. tree@) TYPE%M.Tree.)
  )
  (assert
   (uInv 64 max@)
  )
  (declare-const %%switch_label%%0 Bool)
  ;; could not prove termination
  (declare-const %%location_label%%0 Bool)
  ;; could not prove termination
  (declare-const %%location_label%%1 Bool)
  ;; assertion failure
  (declare-const %%location_label%%2 Bool)
  ;; postcondition not satisfied
  (declare-const %%location_label%%3 Bool)
  (assert
   (not (=>
     (= decrease%init0@ (height.? (Poly%M.Tree. tree@)))
     (or
      (and
       (=>
        (is-M.Tree./Nil tree@)
        %%switch_label%%0
       )
       (=>
        (not (is-M.Tree./Nil tree@))
        (=>
         (= value@ (M.Tree./Node/value (%Poly%M.Tree. (Poly%M.Tree. tree@))))
         (=>
          (= left@ (M.Tree./Node/left (%Poly%M.Tree. (Poly%M.Tree. tree@))))
          (=>
           (= right@ (M.Tree./Node/right (%Poly%M.Tree. (Poly%M.Tree. tree@))))
           (=>
            (= s@ (M.tree_as_sequence.? (Poly%M.Tree. tree@)))
            (and
             (=>
              %%location_label%%0
              (check_decrease_int.? (height.? (Poly%M.Tree. (let
                  ((min!$ min@) (tree!$ left@) (max!$ value@))
                  tree!$
                ))
               ) decrease%init0@ false
             ))
             (=>
              (ens%unstable. min@ left@ value@)
              (and
               (=>
                %%location_label%%1
                (check_decrease_int.? (height.? (Poly%M.Tree. (let
                    ((min!$ value@) (tree!$ right@) (max!$ max@))
                    tree!$
                  ))
                 ) decrease%init0@ false
               ))
               (=>
                (ens%unstable. value@ right@ max@)
                (=>
                 (= tmp%1@ (<= min@ value@))
                 (=>
                  (ens%pervasive.assume. tmp%1@)
                  (=>
                   (= tmp%2@ (<= value@ max@))
                   (=>
                    (ens%pervasive.assume. tmp%2@)
                    (=>
                     (= tmp%3@ (forall ((i$ Poly)) (!
                        (=>
                         (has_type i$ NAT)
                         (=>
                          (< (%I i$) (seq.Seq.len.? (UINT 64) (Poly%seq.Seq<u64.>. s@)))
                          (and
                           (<= min@ (%I (seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s@) i$)))
                           (<= (%I (seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s@) i$)) max@)
                        )))
                        :pattern ((seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s@) i$))
                     )))
                     (and
                      (=>
                       %%location_label%%2
                       (req%pervasive.assert. tmp%3@)
                      )
                      (=>
                       (ens%pervasive.assert. tmp%3@)
                       (=>
                        (ens%pervasive.assume. false)
                        %%switch_label%%0
      ))))))))))))))))))
      (and
       (not %%switch_label%%0)
       (=>
        %%location_label%%3
        (let
         ((s$ (M.tree_as_sequence.? (Poly%M.Tree. tree@))))
         (and
          (forall ((i$ Poly)) (!
            (=>
             (has_type i$ NAT)
             (=>
              (< (%I i$) (seq.Seq.len.? (UINT 64) (Poly%seq.Seq<u64.>. s$)))
              (and
               (<= min@ (%I (seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s$) i$)))
               (<= (%I (seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s$) i$)) max@)
            )))
            :pattern ((seq.Seq.index.? (UINT 64) (Poly%seq.Seq<u64.>. s$) i$))
          ))
          (M.sequence_is_sorted.? (Poly%seq.Seq<u64.>. (M.tree_as_sequence.? (Poly%M.Tree. tree@))))
  ))))))))
  (set-option :rlimit 0)
  (check-sat)
  (set-option :rlimit 0)
 (pop)
(pop)
