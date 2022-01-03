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
    x = BitVec("x", 32)
    return (x & 7) == x % 8


def left_shift_2_is_mul_4():
    x = BitVec("x", 32)
    return x << 2 == (x * 4)

def xor_clear():
    x = BitVec("x", 32)
    return x ^ x == 0

# def index_highest_one(x):
#     y = extract(31, 30, x);
    

# def make_bound_with_highest_one():
#     x = BitVec("x", full_bits)


# query = bvadd()
# query = and_preserves_bound()
# query = or_preserves_bound()
# query = mask_with_ffff()
# query = left_shift_is_muliplication()
# query = left_shift_is_mul_if_no_overflow()
# query = logical_right_shift_is_division()
# query = and7_is_mod8()
# query = left_shift_2_is_mul_4()
query = xor_clear()

s = Solver()
s.push()
s.add(Not(query))
print(s.sexpr(), end="")
print("(check-sat)")
print(s.check())