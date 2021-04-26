extern crate builtin;
use builtin::*;

fn main() {}

#[spec]
fn add1_int(i: int) -> int {
    i + 1
}

#[spec]
fn add1_nat(i: nat) -> nat {
    i + 1
}

fn test1(i: int, n: nat, u: u8) {
    // assert(n >= 0); // TODO
    // assert(u >= 0); // TODO
    assert(n + n >= 0);
    assert(((u + u) as int) < 256);
    assert(imply(0 <= u && u < 100, ((u + u) as int) < 250));
    assert(add1_int(u) == u as int + 1);
    // assert(add1_int(u) == (u + 1) as int); // FAILS
    assert(imply(0 <= u, add1_nat(u) == u as nat + 1));
    // assert(imply((u as int) < 256, u < 256)); // FAILS, because 256 is a u8 in u < 256
}

/*
fn typing(u: u64, i: int, n: nat) -> int {
    let u2 = i as u64;
    let i2 = u as int;
    let i3: int = u; // implicit coercion ok
    //let i4: int = u + 1; // implicit coercion disallowed
    //let u3: u64 = i; // implicit coercion disallowed
    let i5: int = n; // implicit coercion ok
    //let n2: nat = i; // implicit coercion disallowed
    let n3: nat = 10;
    let i6: int = -10;
    let u3: u8 = 300;
    assert(u3 > 100); // should fail
    let x = 2 + 2;
    x
}
*/
