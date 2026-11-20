# Generated-harness coverage report

Generator: `generate.py`  •  std_specs: `../../source/vstd/std_specs`

**Emitted 56 Kani harnesses** into `src/generated.rs`.

## Per-file textual `assume_specification` sites

| file | sites | harnesses emitted |
|---|---|---|
| num.rs | 52 | 56 |
| cmp.rs | 30 | 0 |
| ops.rs | 13 | 0 |
| bits.rs | 30 | 0 |
| result.rs | 28 | 0 |
| option.rs | 24 | 0 |

Total textual sites across the six files: 177.
num.rs sites are macro templates instantiated over 6 integer pairs.

## Skips (grouped by reason)

### trait-method item carries no inline postcondition (contract on extension trait)  — 108

- `num.rs:35`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:80`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:82`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:84`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:86`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:88`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:90`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:92`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:94`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:299`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:344`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:346`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:348`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:350`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:352`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:354`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:356`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:358`  [types: u128,u16,u32,u64,u8,usize]

### references macro-local spec module ($mod_*) — postcondition delegates to a vstd wrapping/spec fn (R3)  — 72

- `num.rs:98`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:105`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:112`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:119`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:126`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:133`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:362`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:369`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:376`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:383`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:390`  [types: u128,u16,u32,u64,u8,usize]
- `num.rs:397`  [types: u128,u16,u32,u64,u8,usize]

### multi-clause ensures (R1)  — 47

- `cmp.rs:266`
- `cmp.rs:271`
- `cmp.rs:309`
- `cmp.rs:326`
- `cmp.rs:396`
- `cmp.rs:402`
- `cmp.rs:407`
- `cmp.rs:412`
- `cmp.rs:417`
- `cmp.rs:422`
- `cmp.rs:427`
- `cmp.rs:433`
- `cmp.rs:439`
- `cmp.rs:444`
- `cmp.rs:449`
- `cmp.rs:454`
- `cmp.rs:459`
- `cmp.rs:464`
- `ops.rs:754`
- `ops.rs:759`
- `ops.rs:764`
- `ops.rs:769`
- `ops.rs:774`
- `ops.rs:779`
- `ops.rs:784`
- `ops.rs:789`
- `ops.rs:794`
- `ops.rs:799`
- `option.rs:143`
- `option.rs:201`
- `option.rs:209`
- `option.rs:227`
- `option.rs:237`
- `option.rs:249`
- `option.rs:373`
- `option.rs:382`
- `option.rs:391`
- `option.rs:405`
- `option.rs:412`
- `result.rs:155`
- `result.rs:263`
- `result.rs:279`
- `result.rs:290`
- `result.rs:303`
- `result.rs:340`
- `result.rs:352`
- `result.rs:378`

### R6 tractability: division/remainder is only CBMC-tractable at 8-bit within the CI budget  — 20

- `num.rs:225`  [types: u16,u32,u64,usize]
- `num.rs:238`  [types: u16,u32,u64,usize]
- `num.rs:287`  [types: u16,u32,u64,usize]
- `num.rs:476`  [types: u16,u32,u64,usize]
- `num.rs:500`  [types: u16,u32,u64,usize]

### i128 widening insufficient: needs 130 bits (sum of 128-bit) (R5)  — 19

- `num.rs:140`  [types: u128]
- `num.rs:152`  [types: u128]
- `num.rs:164`  [types: u128]
- `num.rs:188`  [types: u128]
- `num.rs:210`  [types: u128]
- `num.rs:217`  [types: u128]
- `num.rs:225`  [types: u128]
- `num.rs:238`  [types: u128]
- `num.rs:251`  [types: u128]
- `num.rs:263`  [types: u128]
- `num.rs:287`  [types: u128]
- `num.rs:404`  [types: u128]
- `num.rs:416`  [types: u128]
- `num.rs:428`  [types: u128]
- `num.rs:440`  [types: u128]
- `num.rs:464`  [types: u128]
- `num.rs:476`  [types: u128]
- `num.rs:488`  [types: u128]
- `num.rs:500`  [types: u128]

### no inline postcondition (contract on extension trait / separate spec fn) (R1)  — 16

- `cmp.rs:355`
- `cmp.rs:357`
- `cmp.rs:497`
- `cmp.rs:505`
- `cmp.rs:526`
- `cmp.rs:534`
- `cmp.rs:542`
- `cmp.rs:550`
- `cmp.rs:558`
- `cmp.rs:576`
- `ops.rs:360`
- `ops.rs:384`
- `ops.rs:408`
- `option.rs:308`
- `option.rs:330`
- `option.rs:351`

### references non-translatable symbol: checked_div  — 10

- `num.rs:210`  [types: u16,u32,u64,u8,usize]
- `num.rs:217`  [types: u16,u32,u64,u8,usize]

### unexpected char '.' in expr  — 8

- `option.rs:219`
- `option.rs:264`
- `option.rs:273`
- `option.rs:285`
- `result.rs:316`
- `result.rs:328`
- `result.rs:404`
- `result.rs:427`

### i128 widening insufficient: needs 130 bits (product of 64-bit) (R5)  — 6

- `num.rs:176`  [types: u64,usize]
- `num.rs:275`  [types: u64,usize]
- `num.rs:452`  [types: u64,usize]

### references non-translatable symbol: nat_count_ones  — 6

- `bits.rs:1048`
- `bits.rs:1057`
- `bits.rs:1066`
- `bits.rs:1075`
- `bits.rs:1084`
- `bits.rs:1093`

### cannot parse primary at ('OP', '>')  — 6

- `result.rs:177`
- `result.rs:196`
- `result.rs:206`
- `result.rs:214`
- `result.rs:231`
- `result.rs:252`

### expected '{' got ('ID', 'if')  — 5

- `num.rs:188`  [types: u16,u32,u64,u8,usize]

### references non-translatable symbol: rust_div  — 5

- `num.rs:464`  [types: u16,u32,u64,u8,usize]

### references non-translatable symbol: rust_rem  — 5

- `num.rs:488`  [types: u16,u32,u64,u8,usize]

### unexpected char '=' in expr  — 5

- `result.rs:366`
- `result.rs:392`
- `result.rs:418`
- `result.rs:482`
- `result.rs:496`

### R6 tractability: multiplication is only CBMC-tractable up to 16-bit within the CI budget  — 3

- `num.rs:176`  [types: u32]
- `num.rs:275`  [types: u32]
- `num.rs:452`  [types: u32]

### i128 widening insufficient: needs 258 bits (product of 128-bit) (R5)  — 3

- `num.rs:176`  [types: u128]
- `num.rs:275`  [types: u128]
- `num.rs:452`  [types: u128]

### unexpected char ':' in expr  — 3

- `cmp.rs:278`
- `cmp.rs:292`
- `result.rs:439`

### references non-translatable symbol: u8_trailing_zeros  — 1

- `bits.rs:55`

### references non-translatable symbol: u8_trailing_ones  — 1

- `bits.rs:61`

### references non-translatable symbol: u8_leading_zeros  — 1

- `bits.rs:67`

### references non-translatable symbol: u8_leading_ones  — 1

- `bits.rs:73`

### references non-translatable symbol: u8_reverse_bits  — 1

- `bits.rs:189`

### references non-translatable symbol: u16_trailing_zeros  — 1

- `bits.rs:245`

### references non-translatable symbol: u16_trailing_ones  — 1

- `bits.rs:251`

### references non-translatable symbol: u16_leading_zeros  — 1

- `bits.rs:257`

### references non-translatable symbol: u16_leading_ones  — 1

- `bits.rs:263`

### references non-translatable symbol: u16_reverse_bits  — 1

- `bits.rs:385`

### references non-translatable symbol: u32_trailing_zeros  — 1

- `bits.rs:441`

### references non-translatable symbol: u32_trailing_ones  — 1

- `bits.rs:447`

### references non-translatable symbol: u32_leading_zeros  — 1

- `bits.rs:453`

### references non-translatable symbol: u32_leading_ones  — 1

- `bits.rs:459`

### references non-translatable symbol: u32_reverse_bits  — 1

- `bits.rs:581`

### references non-translatable symbol: u64_trailing_zeros  — 1

- `bits.rs:638`

### references non-translatable symbol: u64_trailing_ones  — 1

- `bits.rs:644`

### references non-translatable symbol: u64_leading_zeros  — 1

- `bits.rs:650`

### references non-translatable symbol: u64_leading_ones  — 1

- `bits.rs:656`

### references non-translatable symbol: u64_reverse_bits  — 1

- `bits.rs:779`

### references non-translatable symbol: u128_trailing_zeros  — 1

- `bits.rs:823`

### references non-translatable symbol: u128_leading_zeros  — 1

- `bits.rs:829`

### references non-translatable symbol: usize_trailing_zeros  — 1

- `bits.rs:930`

### references non-translatable symbol: usize_leading_zeros  — 1

- `bits.rs:936`

### references non-translatable symbol: is_ok  — 1

- `result.rs:135`

### references non-translatable symbol: is_err  — 1

- `result.rs:148`

### references non-translatable symbol: ok  — 1

- `result.rs:457`

### references non-translatable symbol: err  — 1

- `result.rs:473`

### references non-translatable symbol: is_some  — 1

- `option.rs:123`

### references non-translatable symbol: is_none  — 1

- `option.rs:136`

### references non-translatable symbol: spec_unwrap  — 1

- `option.rs:160`

### references non-translatable symbol: spec_unwrap_or  — 1

- `option.rs:177`

### references non-translatable symbol: spec_expect  — 1

- `option.rs:193`

### references non-translatable symbol: spec_ok_or  — 1

- `option.rs:367`

## Emitted harnesses

- `gen_i16_checked_add`
- `gen_i16_checked_add_unsigned`
- `gen_i16_checked_mul`
- `gen_i16_checked_sub`
- `gen_i16_checked_sub_unsigned`
- `gen_i32_checked_add`
- `gen_i32_checked_add_unsigned`
- `gen_i32_checked_sub`
- `gen_i32_checked_sub_unsigned`
- `gen_i64_checked_add`
- `gen_i64_checked_add_unsigned`
- `gen_i64_checked_sub`
- `gen_i64_checked_sub_unsigned`
- `gen_i8_checked_add`
- `gen_i8_checked_add_unsigned`
- `gen_i8_checked_div_euclid`
- `gen_i8_checked_mul`
- `gen_i8_checked_rem_euclid`
- `gen_i8_checked_sub`
- `gen_i8_checked_sub_unsigned`
- `gen_isize_checked_add`
- `gen_isize_checked_add_unsigned`
- `gen_isize_checked_sub`
- `gen_isize_checked_sub_unsigned`
- `gen_u16_checked_add`
- `gen_u16_checked_add_signed`
- `gen_u16_checked_mul`
- `gen_u16_checked_sub`
- `gen_u16_saturating_add`
- `gen_u16_saturating_mul`
- `gen_u16_saturating_sub`
- `gen_u32_checked_add`
- `gen_u32_checked_add_signed`
- `gen_u32_checked_sub`
- `gen_u32_saturating_add`
- `gen_u32_saturating_sub`
- `gen_u64_checked_add`
- `gen_u64_checked_add_signed`
- `gen_u64_checked_sub`
- `gen_u64_saturating_add`
- `gen_u64_saturating_sub`
- `gen_u8_checked_add`
- `gen_u8_checked_add_signed`
- `gen_u8_checked_mul`
- `gen_u8_checked_rem`
- `gen_u8_checked_rem_euclid`
- `gen_u8_checked_sub`
- `gen_u8_is_multiple_of`
- `gen_u8_saturating_add`
- `gen_u8_saturating_mul`
- `gen_u8_saturating_sub`
- `gen_usize_checked_add`
- `gen_usize_checked_add_signed`
- `gen_usize_checked_sub`
- `gen_usize_saturating_add`
- `gen_usize_saturating_sub`
