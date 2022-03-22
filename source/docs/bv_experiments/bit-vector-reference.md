# `#[verifier(bit_vector)]` and `assert_bit_vector`
There are two ways to use bit-vector reasoning. The first one is using bit-vector function mode with annotation `#[verifier(bit_vector)]`, and the second one is using single line assertion, `assert_bit_vector`. These will try to prove assertions using bit-vector theory(in a separate Z3 query), and produce its corresponding integer property as an axiom. When making the corresponding property, bitwise operators are translated into uninterpreted functions in Z3.   


### `assert_bit_vector`
`assert_bit_vector` is used when a short and context-free bit-vector fact is needed. 
Currently, `assert_bit_vector` does not recognize any context(variable definition, `requires` in the function scope, etc).  
Example use cases:  
```
fn test1(b: u32) {
  assert_bit_vector(b & 7 == b % 8);
  assert(b & 7 == b % 8);

  assert_bit_vector(b & 0xff < 0x100);
  assert(b & 0xff < 0x100);
}
```



### `#[verifier(bit_vector)]`
To use this annotation, the function must be specified as `proof` mode. Also, this function should not have a body. Contexts can be provided by `requires`. 
Example:     
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

### Supported expressions inside `assert_bit_vector` and `#[verifier(bit_vector)]`
The supported functionalities for bit-vector can be found in `exp_to_bv_expr` in `sst_to_air.rs`. Integer types(as well as `as` keyword between integers), builtin operators, `let` binding, quantifier binding, and `if and else` are supported.  
 Function call is not supported, and macro might be used instead of functions in some cases. Any types other than integer types can make the translation process panic.


### Signed bit-vector is not supported
In the current setting, if a signed integer is used as an operand in bit-vector reasoning, the translation process panics.




## Bitwise operators as uninterpreted functions
Outside of `#[verifier(bit_vector)]` and `assert_bit_vector`, bitwise operators are translated into uninterpreted functions in Z3. Therefore, it is even impossible to prove trivial facts about bit-vectors without `#[verifier(bit_vector)]` or `assert_bit_vector`.

### Basic properties are missing
As a consequence, basic properties such as `&`'s commutativity and associativity are not triggered automatically. To trigger these, please refer to `rust_verify/example/bitvector_basic.rs`, which contains basic properties for bit-wise operators.



## Examples on bit manipulation
First, let's define macros to manipulation bits. `get_bit64!` reads a single bit from a `u64`, and `set_64!` sets a single bit for a `u64`. For this example, we are using boolean to represent one bit.
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
With macros above, we can prove that `set_bit64!` does what is has to do.
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

We can also set two bits at once. First function proves that the second function behaves as desired. 

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


