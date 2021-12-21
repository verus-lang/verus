from z3 import *

full_bits = 256
base = (2 ** full_bits)

# def bvadd():
#     x = BitVec("x", full_bits)
#     y = BitVec("y", full_bits)
#     z = Concat(y, x) 
#     # print(z.sort())
#     x_ext = ZeroExt(full_bits, x)
#     y_ext = ZeroExt(full_bits, y)
#     return z == x_ext + y_ext * (2 ** full_bits)

def xor_bytes():
    x = BitVec("x", full_bits)
    y = BitVec("y", full_bits)
    return Implies(
            And(x < 256, y < 256),
            x & y < 256);

def mask_with_ffff():
    x = BitVec("x", full_bits)
    return x & 0xFFFF < 0x10000;

def left_shift_is_muliplication():
    x = BitVec("x", full_bits)
    shift = 128
    return x << shift == (x * (2 ** shift)) % base;

def logical_right_shift_is_division():
    x = BitVec("x", full_bits)
    shift = 128
    # logical right shift
    return LShR(x, shift) == (UDiv(x, (2 ** shift))) % base;


query = logical_right_shift_is_division()
prove(query)

s = Solver()
s.push()
s.add(Not(query))
print(s.sexpr(), end="")
print("(check-sat)")