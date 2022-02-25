#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{invariants::*};
use crate::pervasive::{atomic::*};
use crate::pervasive::{modes::*};

#[verifier(atomic)]
#[verifier(external_body)]
fn atomic_op() {
  opens_invariants_none();
}

#[verifier(external_body)]
fn non_atomic_op() {
  opens_invariants_none();
}

pub fn do_nothing(#[proof] i: Invariant<u8>) {
  open_invariant!(&i => inner => {
    atomic_op();
    //atomic_op();
  });
}

pub fn main() {
    let (at, Proof(mut perm)) = PAtomicU64::new(5);

    assert(perm.value == 5);

    let l = at.load(&perm);
    assert(l == 5);

    at.store(&mut perm, 6);
    assert(perm.value == 6);

    let l = at.swap(&mut perm, 9);
    assert(l == 6);
    assert(perm.value == 9);

    let l = at.fetch_add_wrapping(&mut perm, 0xffff_ffff_ffff_ffff);
    assert(l == 9);
    assert(perm.value == 8);

    let l = at.fetch_sub_wrapping(&mut perm, 0xffff_ffff_ffff_ffff);
    assert(l == 8);
    assert(perm.value == 9);

    let l = at.fetch_or(&mut perm, 2);
    assert(l == 9);
    assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
    assert(perm.value == 11);

    let l = at.fetch_and(&mut perm, 6);
    assert(l == 11);
    assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
    assert(perm.value == 2);

    let l = at.fetch_xor(&mut perm, 3);
    assert(l == 2);
    assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
    assert(perm.value == 1);

    let l = at.fetch_max(&mut perm, 5);
    assert(l == 1);
    assert(perm.value == 5);

    let l = at.fetch_max(&mut perm, 4);
    assert(l == 5);
    assert(perm.value == 5);

    let l = at.fetch_min(&mut perm, 4);
    assert(l == 5);
    assert(perm.value == 4);

    let l = at.fetch_min(&mut perm, 7);
    assert(l == 4);
    assert(perm.value == 4);

    let l = at.into_inner(perm);
    assert(l == 4);
}
