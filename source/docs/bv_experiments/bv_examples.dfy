module bv {

  newtype uint8 = n: int | 0 <= n < 256

  newtype uint16 = n: int | 0 <= n < 65536

  newtype uint32 = n: int | 0 <= n < 4294967296

  newtype uint64 = n: int | 0 <= n < 18446744073709551616

  newtype int8 = n: int | -128 <= n < 128

  newtype int16 = n: int | -32768 <= n < 32768

  newtype int32 = n: int | -2147483648 <= n < 2147483648

  newtype int64 = n: int | -9223372036854775808 <= n < 9223372036854775808

  function {:opaque} U32(b:bv32) : uint32 { b as uint32 }
  function {:opaque} B32(u:uint32) : bv32 { u as bv32 }
  function {:opaque} U64(b:bv64) : uint64 { b as uint64 }
  function {:opaque} B64(u:uint64) : bv64 { u as bv64 }

  // 32 bits
  function {:opaque} bit_and32(b0:bv32, b1:bv32) : bv32 
    { b0 & b1 }

  function {:opaque} bit_or32(b0:bv32, b1:bv32) : bv32 
    { b0 | b1 }

  function {:opaque} bit_mod32(b0:bv32, b1:bv32) : bv32 
    requires b1 != 0;
    { b0 % b1 }

  function {:opaque} bit_xor32(b0:bv32, b1:bv32) : bv32 
    { b0 ^ b1 }

  function {:opaque} bit_lshift32(b0:bv32, b1:bv32) : bv32 
    requires b1 <= 32;
    { b0 << b1 }

  function {:opaque} bit_rshift32(b0:bv32, b1:bv32) : bv32 
    requires b1 <= 32;
    { b0 >> b1 }

  function {:opaque} bit_and_uint32(u0:uint32, u1:uint32) : uint32 
  {
    U32(bit_and32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_or_uint32(u0:uint32, u1:uint32) : uint32 
  {
    U32(bit_or32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_mod_uint32(u0:uint32, u1:uint32) : uint32 
    requires u1 != 0;
  {
    reveal B32();
    U32(bit_mod32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_xor_uint32(u0:uint32, u1:uint32) : uint32 
  {
    U32(bit_xor32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_lshift_uint32(u0:uint32, u1:uint32) : uint32 
    requires u1 <= 32;
  {
    bv32_inequality(u1);
    U32(bit_lshift32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_rshift_uint32(u0:uint32, u1:uint32) : uint32 
    requires u1 <= 32;
  {
    bv32_inequality(u1);
    U32(bit_rshift32(B32(u0), B32(u1)))
  }

  // 64 bits
  function {:opaque} bit_and64(b0:bv64, b1:bv64) : bv64 
    { b0 & b1 }

  function {:opaque} bit_or64(b0:bv64, b1:bv64) : bv64 
    { b0 | b1 }

  function {:opaque} bit_mod64(b0:bv64, b1:bv64) : bv64 
    requires b1 != 0;
    { b0 % b1 }

  function {:opaque} bit_xor64(b0:bv64, b1:bv64) : bv64 
    { b0 ^ b1 }

  function {:opaque} bit_lshift64(b0:bv64, b1:bv64) : bv64 
    requires b1 <= 64;
    { b0 << b1 }

  function {:opaque} bit_rshift64(b0:bv64, b1:bv64) : bv64 
    requires b1 <= 64;
    { b0 >> b1 }

  function {:opaque} bit_and_uint64(u0:uint64, u1:uint64) : uint64 
  {
    U64(bit_and64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_or_uint64(u0:uint64, u1:uint64) : uint64 
  {
    U64(bit_or64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_mod_uint64(u0:uint64, u1:uint64) : uint64 
    requires u1 != 0;
  {
    reveal B64();
    U64(bit_mod64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_xor_uint64(u0:uint64, u1:uint64) : uint64 
  {
    U64(bit_xor64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_lshift_uint64(u0:uint64, u1:uint64) : uint64 
    requires u1 <= 64;
  {
    bv64_inequality(u1);
    U64(bit_lshift64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_rshift_uint64(u0:uint64, u1:uint64) : uint64 
    requires u1 <= 64;
  {
    bv64_inequality(u1);
    U64(bit_rshift64(B64(u0), B64(u1)))
  }

  lemma {:axiom} bv_core_properties()
    ensures forall u:uint32 :: U32(B32(u)) == u;
    ensures forall b:bv32 :: B32(U32(b)) == b;
    ensures forall x:uint32, m:uint32 :: 
                   m != 0 && B32(m) != 0 ==> (x % m) == U32(bit_mod32(B32(x), B32(m)));
    ensures forall u:uint64 :: U64(B64(u)) == u;
    ensures forall b:bv64 :: B64(U64(b)) == b;
    ensures forall x:uint64, m:uint64 :: 
                   m != 0 && B64(m) != 0 ==> (x % m) == U64(bit_mod64(B64(x), B64(m)));
  
  // 32 bits
  lemma B32_injective(u0:uint32, u1:uint32)
    ensures u0 == u1 <==> B32(u0) == B32(u1);
  {
    bv_core_properties();
    assert u0 == u1 ==> B32(u0) == B32(u1);
    var b0 := B32(u0);
    var b1 := B32(u1);
    assert b0 == b1 ==> U32(b0) == U32(b1);
  }
  
  lemma U32_injective(b0:bv32, b1:bv32)
    ensures b0 == b1 <==> U32(b0) == U32(b1);
  {
    bv_core_properties();
    assert b0 == b1 ==> U32(b0) == U32(b1);
    var u0 := U32(b0);
    var u1 := U32(b1);
    assert u0 == u1 ==> B32(u0) == B32(u1);
  }

  lemma bv32_injectivity()
    ensures forall u0:uint32, u1:uint32 :: u0 == u1 <==> B32(u0) == B32(u1)
    ensures forall b0, b1 :: b0 == b1 <==> U32(b0) == U32(b1)
  {
    reveal B32(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    reveal U32(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    forall u0:uint32, u1:uint32 ensures u0 == u1 <==> B32(u0) == B32(u1) { B32_injective(u0, u1); }
    forall b0, b1 ensures b0 == b1 <==> U32(b0) == U32(b1) { U32_injective(b0, b1); }
  }

  lemma bv32_inequality(u:uint32)
    requires u <= 32;
    ensures  B32(u) <= 32;
  {
    reveal B32();
    reveal U32();
    bv_core_properties();
    bv32_injectivity();
  }

  // 64 bits
  lemma B64_injective(u0:uint64, u1:uint64)
    ensures u0 == u1 <==> B64(u0) == B64(u1);
  {
    bv_core_properties();
    assert u0 == u1 ==> B64(u0) == B64(u1);
    var b0 := B64(u0);
    var b1 := B64(u1);
    assert b0 == b1 ==> U64(b0) == U64(b1);
  }
  
  lemma U64_injective(b0:bv64, b1:bv64)
    ensures b0 == b1 <==> U64(b0) == U64(b1);
  {
    bv_core_properties();
    assert b0 == b1 ==> U64(b0) == U64(b1);
    var u0 := U64(b0);
    var u1 := U64(b1);
    assert u0 == u1 ==> B64(u0) == B64(u1);
  }

  lemma bv64_injectivity()
    ensures forall u0:uint64, u1:uint64 :: u0 == u1 <==> B64(u0) == B64(u1)
    ensures forall b0, b1 :: b0 == b1 <==> U64(b0) == U64(b1)
  {
    reveal B64(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    reveal U64(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    forall u0:uint64, u1:uint64 ensures u0 == u1 <==> B64(u0) == B64(u1) { B64_injective(u0, u1); }
    forall b0, b1 ensures b0 == b1 <==> U64(b0) == U64(b1) { U64_injective(b0, b1); }
  }

  lemma bv64_inequality(u:uint64)
    requires u <= 64;
    ensures  B64(u) <= 64;
  {
    reveal B64();
    reveal U64();
    bv_core_properties();
    bv64_injectivity();
  }


  // Example uses
  lemma bv_test(b:bv64)
    //ensures bit_and64(b, 0) == 0;
    //ensures bit_and64(b, 0xFFFFFFFFFFFFFFFF) == b
    ensures bit_xor64(b, 0) == b;
  {
    //reveal bit_and64();
    var all_ones:bv64 := 0xFFFFFFFFFFFFFFFF; 
    //assert bit_and64(b, all_ones) == b;
    reveal_bit_xor64();
  }
  
  lemma bv64_properties()
    ensures forall u0:uint64 :: bit_and_uint64(u0, 0) == 0
  {
    reveal bit_and_uint64();  // Without this, Dafny can't seem to translate the forall statement to the forall expression
    forall u0 ensures bit_and_uint64(u0, 0) == 0 { bv64_properties_specific(u0, 0); }
  }

  lemma bv64_properties_specific(u0:uint64, u1:uint64)
    ensures bit_and_uint64(u0, 0) == 0
    ensures bit_and_uint64(u0, u1) == bit_and_uint64(u1, u0)
    ensures bit_xor_uint64(u0, u0) == 0 
    ensures bit_xor_uint64(u0, u1) == bit_xor_uint64(u1, u0)
  {
    bv_core_properties(); reveal U64(); reveal B64();

    var all_ones:uint64 := 0xFFFFFFFFFFFFFFFF; 
    assert B64(0) == 0; // Help Z3 with constant conversion
    assert B64(all_ones) == 0xFFFFFFFFFFFFFFFF; // Help Z3 with constant conversion

    // AND
    assert bit_and_uint64(u0, 0)  == 0 by { reveal bit_and_uint64(); reveal bit_and64(); }
    assert bit_and_uint64(u0, all_ones)  == u0 by { reveal bit_and_uint64(); reveal bit_and64(); }
    assert bit_and_uint64(u0, u1) == bit_and_uint64(u1, u0) by { reveal bit_and_uint64(); reveal bit_and64(); }

    // OR
    assert bit_or_uint64(u0, 0)  == u0 by { reveal bit_or_uint64(); reveal bit_or64(); }
    assert bit_or_uint64(u0, all_ones)  == all_ones by { reveal bit_or_uint64(); reveal bit_or64(); }
    assert bit_or_uint64(u0, u1) == bit_or_uint64(u1, u0) by { reveal bit_or_uint64(); reveal bit_or64(); }

    // XOR
    assert bit_xor_uint64(u0, u0) == 0 by { reveal bit_xor_uint64(); reveal bit_xor64(); }
    assert bit_xor_uint64(u0, u1) == bit_xor_uint64(u1, u0) by { reveal bit_xor_uint64(); reveal bit_xor64(); }
    assert bit_xor_uint64(u0, 0)  == u0 by { reveal bit_xor_uint64(); reveal bit_xor64(); }
  }

  lemma mask_equiv_bv_wrapped(y:bv32)
    ensures bit_mod32(y, 512) == bit_and32(y, 511);
  {
    reveal bit_mod32();
    reveal bit_and32();
  }

  lemma mask_equiv_wrapped(x:uint32)
    ensures bit_mod_uint32(x, 512) == bit_and_uint32(x, 511);
  {
    assert B32(512) == 512 by { reveal B32(); }
    assert B32(511) == 511 by { reveal B32(); }
    calc {
      bit_mod_uint32(x, 512);
        { reveal bit_mod_uint32(); reveal B32(); }
      U32(bit_mod32(B32(x), B32(512)));
        { mask_equiv_bv_wrapped(B32(x)); assert bit_mod32(B32(x), 512) == bit_and32(B32(x), 511); }
      U32(bit_and32(B32(x), B32(511)));
        { reveal bit_and_uint32(); }
      bit_and_uint32(x, 511);
    }
  }

  lemma bit_mod_equiv(u0:uint32, u1:uint32)
    requires u1 != 0;
    ensures bit_mod_uint32(u0, u1) == u0 % u1;
  {
    reveal bit_mod_uint32();
    bv_core_properties();
    assert B32(u1) != 0 by { reveal B32(); }
    assert bit_mod32(B32(u0), B32(u1)) >= 0;
  }

  lemma mask_equiv_specific(x:uint32)
    ensures x % 512 == bit_and_uint32(x, 511);
  {
    calc {
      x % 512;
        { bit_mod_equiv(x, 512); }
      bit_mod_uint32(x, 512);
        { mask_equiv_wrapped(x); }
      bit_and_uint32(x, 511);
    }
  }

  lemma lemma_xor_bytes(x:uint32, y:uint32)
    requires 0 <= x < 256;
    requires 0 <= y < 256;
    ensures bit_and_uint32(x, y) < 256;
  {
    assume false;
  }

  // (declare-fun y () (_ BitVec 32))
  // (declare-fun x () (_ BitVec 32))
  // (assert (not (=> (and (bvslt x #x00000100) (bvslt y #x00000100))
  //          (bvslt (bvand x y) #x00000100))))

  lemma mask_with_ffff(x:uint32)
    ensures bit_and_uint32(x, 0xFFFF) < 0x10000;
  {
    assume false;
  }

// (declare-fun x () (_ BitVec 32))
// (assert (not (bvslt (bvand x #x0000ffff) #x00010000)))
// (check-sat)


  lemma lemma_and_with_32_64_specific_premium(x:uint32)
    // ensures bit_and_uint32(x, 32) > 0 ==> BEWordToBitSeq(x)[26] == 1;
    // ensures bit_and_uint32(x, 64) > 0 ==> BEWordToBitSeq(x)[25] == 1;
  {
    assume false;
  }

  lemma left_shift_is_muliplication(x:uint32)
    ensures bit_lshift_uint32(x, 8) == (x * 256) % 4294967296


}
