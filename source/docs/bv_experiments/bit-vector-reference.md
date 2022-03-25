# Proving Properties About Bit Manipulation

Verus offers two dedicated mechanisms for reasoning about bit manipulation
(e.g., to prove that `xor(w, w) == 0`).  Small, one-off proofs can by done
via `assert_bit_vector` (similar to a standard `assert`).  Larger proofs,
or proofs that will be needed in more than one place, can be done by writing
a lemma (i.e., a function in `#[proof]` mode) and adding the annotation 
`#[verifier(bit_vector)]`.  Both mechanisms export facts expressed over
integers (e.g., in terms of `u32`), but internally, they translate the proof
obligations into assertions about bit vectors and use a dedicated solver to
discharge those assertions.

## Details

### Details on `assert_bit_vector`
`assert_bit_vector` is used when a short and context-free bit-related fact is needed. 
Here are two example use cases:
```
fn test_passes(b: u32) {
  assert_bit_vector(b & 7 == b % 8);
  assert(b & 7 == b % 8);

  assert_bit_vector(b & 0xff < 0x100);
  assert(b & 0xff < 0x100);
}
```

Currently, assertions expressed via `assert_bit_vector` do not include any
ambient facts from the surrounding context (e.g., from `requires` clauses or
previous variable definitions).  For example, the following example will fail.

```
fn test_fails(x: u32, y: u32) {
  requires(x == y);
  assert_bit_vector(x & 3 == y & 3);  // Fails
}
```


### Details on `#[verifier(bit_vector)]`
This mechanism should be used when proving more complex facts about bit manipulation,
or when a proof will be used more than once.
To use this mechanism, the developer should write a
function in `proof` mode (i.e., annotated with `#[proof]`). 
The function **should not** have a body. 
Context can be provided via a `requires` clause. 
For example:     
```
  #[verifier(bit_vector)]
  #[proof]
  fn de_morgan_auto(){
      ensures([
          forall(|a: u32, b: u32| #[trigger] (!(a & b)) == !a | !b),
          forall(|a: u32, b: u32| #[trigger] (!(a | b)) == !a & !b),
      ]);
  }
```
For more examples, please refer to the bit-manipulation examples at the bottom.

## Limitations

### Supported Expressions 

The two bit-reasoning mechanisms support only a subset of the full set of expressions Verus offers.
Currently, they support:
- Integer types (as well as the `as` keyword between integers)
- Built-in operators
- `let` binding
- Quantifiers
- `if-then-else` 
For more details, see `exp_to_bv_expr` in `source/vir/src/sst_to_air.rs`.
Use of other expressions or non-integer types will cause Verus to panic.

Note that function calls are not supported. As a workaround, you may consider using a macro instead of a function.

### Signed integers are not supported
Currently, if a signed integer is used as an operand in bit-reasoning, the translation process panics.


### Bitwise Operators As Uninterpreted Functions
Outside of `#[verifier(bit_vector)]` and `assert_bit_vector`, bitwise operators
are translated into uninterpreted functions in Z3, meaning Z3 knows nothing
about them when used in other other contexts. 
As a consequence, basic properties such as commutativity and associativity of
bitwise-AND will not be applied automatically. To make use of these properties,
please refer to `source/rust_verify/example/bitvector_basic.rs`, which contains
basic properties for bitwise operators.



## Examples of Bit Manipulation Proofs
First, let's define macros to manipulate bits. `get_bit64!` reads a single bit from a `u64`, and `set_64!` sets a single bit for a `u64`. For this example, we are using a boolean value to represent one bit.
```
// a: bitvec, b: index
macro_rules! get_bit64{
    ($a:expr,$b:expr)=>{
        {
            (0x1u64 & ($a>>($b as u64))) == 1u64
        }
    }
}

// a: bitvec, b: index, c: bit(boolean value)
macro_rules! set_bit64{
    ($a:expr,$b:expr, $c:expr)=>{
        {
             if $c {$a | 1u64 << ($b as u64)}
             else {$a & (!(1u64 << ($b as u64)))}
        }
    }
}
```
With the macros above, we can prove that `set_bit64!` has the desired behavior. 
```
#[verifier(bit_vector)]
#[proof]
fn set_bit64_proof(bv_new: u64, bv_old: u64, index: u32, bit: bool){
    requires([
        bv_new == set_bit64!(bv_old, index, bit),
        index < 64 ,
    ]);
    ensures([
        get_bit64!(bv_new, index) == bit,
        forall(|loc2:u32| (loc2 < 64 && loc2 != index) >>= (get_bit64!(bv_new, loc2) == get_bit64!(bv_old, loc2))),
    ]);
}
```

We can also set two bits at once.  The second function below executes the operation, while the first funciton proves that that execution has the desired effect.
```
#[verifier(bit_vector)]
#[proof]
fn set_two_bit_proof(bv:u32, target:u32, mask:u32, result:u32, low_loc:u32, high:bool, low:bool) {
    requires([
        low_loc < 31,
        target == {if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc,
        mask == !(3u32 << low_loc),
        result == (bv & mask) | target, 
    ]);
    ensures([
        get_bit!(result, low_loc) == low,
        get_bit!(result, low_loc+1) == high,
        forall(|loc2:u32| (loc2 < 32 && loc2 != low_loc && loc2 != (low_loc+1)) >>= (get_bit!(result, loc2) == get_bit!(bv, loc2))),
    ]);    
}

#[exec]
fn set_two_bit_exec(bv:u32, low_loc:u32, high:bool, low:bool) -> u32 {
    requires(low_loc < 31);
    ensures(|ret:u32| [ 
        get_bit!(ret, low_loc) == low,
        get_bit!(ret, low_loc+1) == high,
        forall(|loc2:u32| (loc2 < 32 && loc2 != low_loc && loc2 != (low_loc+1)) >>= (get_bit!(ret, loc2) == get_bit!(bv, loc2))),
    ]);
    let target:u32 = {if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc;
    let mask:u32 = !(3u32 << low_loc);
    let result:u32 = (bv & mask) | target;
    set_two_bit_proof(bv, target, mask, result, low_loc, high, low);
    result
}
```


