#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)] use vstd::prelude::*;

verus! {
  mod lib {
    #[allow(unused_imports)] use super::*;

    pub proof fn mod_add_zero(a: int, b: int, c: int)
        // by (integer_ring)
        requires
            a % c == 0,
            b % c == 0,
        ensures
            (a + b) % c == 0,
    {
      admit();
    }
    
    pub open spec fn same_or_arbitrary<A>(a1: A, a2: A) -> A {
      if a1 == a2 {
        a1
      } else {
        arbitrary()
      }
    }
  }

  mod multiple_open {
    #[allow(unused_imports)] use super::*;

    pub struct Multiple {
      pub i: nat,
      pub modulo: nat,
    }
    
    impl Multiple {
      pub open spec fn aligned(&self) -> bool {
        &&& self.i % self.modulo == 0
      }
    
      pub open spec fn add(&self, v: nat) -> Self {
        Multiple { i: self.i + v, ..*self }
      }
    }
  }
  
  mod m1 {
    #[allow(unused_imports)] use super::*;

    use super::multiple_open::Multiple;
  
    proof fn lemma_increase_by_twice(
        p1: Multiple, v: nat, p2: Multiple)
      requires
        p1.modulo != 0, p1.aligned(),
        v % p1.modulo == 0,
        p1.modulo == p2.modulo,
        p2 == p1.add(v).add(v),
      ensures
        p2.aligned()
    {
      // assert((p1.i + v + v) % p2.modulo == 0) by (nonlinear_arith)
      //   requires
      //     p1.i % p2.modulo == 0,
      //     v % p2.modulo == 0,
      //     p2.modulo != 0,
      // { }
      assert((p1.i + v + v) % p2.modulo == 0) by {
        super::lib::mod_add_zero(
          p1.i as int, v as int, p2.modulo as int);
        super::lib::mod_add_zero(
          p1.i as int + v as int, v as int, p2.modulo as int);
      }
    }
  }
  
  
  mod multiple_broadcast_proof {
    #[allow(unused_imports)] use super::*;

    pub struct Multiple {
      pub i: nat,
      pub modulo: nat,
    }
    
    impl Multiple {
      pub closed spec fn aligned(&self) -> bool {
        &&& self.modulo != 0
        &&& self.i % self.modulo == 0
      }

      pub closed spec fn add(&self, v: Self) -> Self {
        Multiple {
            i: self.i + v.i,
            modulo: lib::same_or_arbitrary(self.modulo, v.modulo)
        }
      }

      pub closed spec fn mul(&self, v: Self) -> Self {
        Multiple {
            i: self.i * v.i,
            modulo: lib::same_or_arbitrary(self.modulo, v.modulo)
        }
      }
      
      pub broadcast proof fn lemma_add_aligned(p: Self, v: Self)
        requires
          p.aligned(), v.aligned(), p.modulo == v.modulo,
        ensures
          (#[trigger] p.add(v)).aligned(),
          p.add(v).modulo == lib::same_or_arbitrary(p.modulo, v.modulo),
      {
        super::lib::mod_add_zero(p.i as int, v.i as int, p.modulo as int);
      }

      pub broadcast proof fn lemma_mul_aligned(p: Self, v: Self)
        requires
          p.aligned(), v.aligned(), p.modulo == v.modulo,
        ensures
          (#[trigger] p.mul(v)).aligned(),
          p.mul(v).modulo == lib::same_or_arbitrary(p.modulo, v.modulo),
      {
        // TODO
        admit();
      }

      pub broadcast group group_properties {
        Multiple::lemma_add_aligned,
        Multiple::lemma_mul_aligned,
      }
    }
  }

  mod m2 {
    #[allow(unused_imports)] use super::*;
      
    use super::multiple_broadcast_proof::Multiple;
    
    broadcast use Multiple::lemma_add_aligned;

    proof fn increase_twice(
        p1: Multiple, v: Multiple, p2: Multiple)
      requires
        p1.aligned(), v.aligned(), p1.modulo == v.modulo,
        p2 == p1.add(v).add(v),
      ensures
        p2.aligned()
    {
    }

  }

  mod m3 {
    #[allow(unused_imports)] use super::*;
      
    use super::multiple_broadcast_proof::Multiple;
    

    proof fn increase_twice(
        p1: Multiple, v: Multiple, p2: Multiple)
      requires
        p1.aligned(), v.aligned(), p1.modulo == v.modulo,
        p2 == p1.add(v).add(v),
      ensures
        p2.aligned()
    {
    broadcast use Multiple::group_properties;
    }
    
    proof fn multiply_add(
        p1: Multiple, v: Multiple, p2: Multiple)
      requires
        p1.aligned(), v.aligned(), p1.modulo == v.modulo,
        p2 == p1.mul(v).add(v),
      ensures
        p2.aligned()
    {
    broadcast use Multiple::group_properties;
    }
    
    proof fn some_vstd_lemma()
    {
      let a = seq![1nat, 2, 3];
      assert(a[2] == 3);
    }
  }
  
} // verus!