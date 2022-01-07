from z3 import *

full_bits = 256
base = (2 ** full_bits)

def bvadd():
    x = BitVec("x", full_bits)
    y = BitVec("y", full_bits)
    z = Concat(y, x) 
    # print(z.sort())
    x_ext = ZeroExt(full_bits, x)
    y_ext = ZeroExt(full_bits, y)
    return z == x_ext + y_ext * (2 ** full_bits)

def and_preserves_bound():
    x = BitVec("x", full_bits)
    y = BitVec("y", full_bits)
    return Implies(
            And(x < 256, y < 256),
            x & y < 256);

def or_preserves_bound():
    x = BitVec("x", full_bits)
    y = BitVec("y", full_bits)
    return Implies(
            And(x < 256, y < 256),
            x | y < 256);

def mask_with_ffff():
    x = BitVec("x", full_bits)
    return x & 0xFFFF < 0x10000;

def left_shift_is_muliplication():
    x = BitVec("x", full_bits)
    shift = 128
    return x << shift == (x * (2 ** shift));# % base;

def left_shift_is_mul_if_no_overflow():
    x = BitVec("x", full_bits)
    shift = BitVec("shift", full_bits)
    return Implies(
             BVMulNoOverflow(x, 2 ** shift, False),
             x << shift == x * (2 ** shift));

def logical_right_shift_is_division():
    x = BitVec("x", full_bits)
    shift = 128
    # logical right shift
    return LShR(x, shift) == (UDiv(x, (2 ** shift)));


def and7_is_mod8():
    x = BitVec("x", 5)
    return (x & 7) == x % 8


def left_shift_2_is_mul_4():
    x = BitVec("x", 32)
    return x << 2 == (x * 4)

def xor_clear():
    x = BitVec("x", 32)
    return x ^ x == 0

def concat_and_split():
    x1 = BitVec("x", 32)
    y1 = BitVec("y", 32)
    z = Concat(y1,x1)
    x2 = Extract(31,0,z)
    y2 = Extract(63,32,z)
    return And(x1 == x2, y1 == y2)

def make_bound_with_msb():
    x = BitVec("x", 32)
    y = Extract(31, 31, x)
    return Implies(y==0 , ULT(x , (2**31)))


def concat_property():
    x = BitVec("x", 16)
    y = BitVec("y", 16)
    zero = BitVecVal(0, 16)
    x_extended = Concat(zero, x)
    y_extended = Concat(zero, y)
    z = Concat(y,x)
    return z == (y_extended * 0x10000 + x_extended)    

# def make_bound_with_highest_set_bit():
#     x = BitVec("x", 32)




# query = bvadd()
# query = and_preserves_bound()
# query = or_preserves_bound()
# query = mask_with_ffff()
# query = left_shift_is_muliplication()
# query = left_shift_is_mul_if_no_overflow()
# query = logical_right_shift_is_division()
# query = and7_is_mod8()
# query = left_shift_2_is_mul_4()
# query = xor_clear()
# query = concat_and_split()
# query = make_bound_with_msb()
query = concat_property()

s = Solver()
s.push()
s.add(Not(query))
print(s.sexpr(), end="")
print("(check-sat)")
print(s.check())
# print(s.model())