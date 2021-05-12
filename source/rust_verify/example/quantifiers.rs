#![feature(stmt_expr_attributes)]
extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

#[spec]
fn f1(i: int, j: int) -> bool {
    i <= j
}

#[spec]
fn f2(i: int, j: int) -> bool {
    i >= j
}

#[spec]
fn g1(i: int) -> int {
    i + 1
}

#[spec]
fn g2(i: int) -> int {
    i + 2
}

#[spec]
fn g3(i: int) -> int {
    i + 3
}

// TODO: this should be the definition of assert
fn assert_ensure(#[spec] b: bool) {
    requires(b);
    ensures(b);
}

// Automatically chosen triggers
fn test_auto() {
    // :pattern ((f1. i@ j@))
    assert(forall(|i: int, j: int| imply(i == j, f1(i, j))));

    // :pattern ((f1. i@ j@))
    assert(forall(|i: int, j: int| imply(i == j, f1(i, j) && f1(i, j))));

    // :pattern ((f1. j@ i@))
    // :pattern ((f1. i@ j@))
    assert(forall(|i: int, j: int| imply(i == j, f1(i, j) || f1(j, i))));

    // :pattern ((f1. i@ j@))
    // note: f1(i, j) is preferred over splitting i, j among g1(i), g2(j)
    assert(forall(|i: int, j: int| imply(f1(i, j), g1(i) <= g2(j))));

    // :pattern ((g1. i@))
    // note: g1(i) is preferred over the more deeply nested g3(i)
    assert(forall(|i: int| g1(i) >= i || g2(g3(i)) >= i));

    // :pattern ((f1. i@ j@))
    // note: f1(i, j) is preferred over the larger f2(j, g1(i))
    assert(forall(|i: int, j: int| imply(i == j, f1(i, j) || f2(j, g1(i)))));

    // :pattern ((f1. j@ (g1. i@)))
    // note: f1(i, j) is excluded due to a potential matching loop
    assert(forall(|i: int, j: int| imply(i == j, f1(i, j) || f1(j, g1(i)))));

    // matching loop, no trigger
    // assert(forall(|i: int, j: int| imply(i == j, f1(i, j) || f1(j, i + 1))));

    // :pattern ((f2. j@ i@))
    // :pattern ((f1. i@ j@))
    assert(forall(|i: int, j: int| imply(f2(j, i), f1(i, j))));

    // :pattern ((g1. j@) (g1. i@))
    assert(forall(|i: int, j: int| g1(i) >= i && g1(j) >= j));

    // :pattern ((g1. i@) (g2. j@))
    assert_ensure(g1(3) == g2(2));
    assert(exists(|i: int, j: int| g1(i) == g2(j)));
}

// Manually chosen triggers
fn test_manual() {
    //
    // For single triggers, use #[trigger]
    //

    // :pattern ((f1. i@ j@))
    assert(forall(|i: int, j: int| imply(f2(j, i), #[trigger] f1(i, j))));

    // :pattern ((g1. i@) (g2. j@))
    assert(forall(|i: int, j: int| imply(f1(i, j), f1(#[trigger] g1(i), #[trigger] g2(j)))));

    //
    // For multiple triggers, use #[trigger(...)], where the triggers are numbered 1, 2, ...
    //

    // :pattern ((g1. i@) (g2. j@))
    // :pattern ((f1. i@ j@))
    assert(forall(|i: int, j: int|
        imply(
            #[trigger(1)] f1(i, j),
            f1(#[trigger(2)] g1(i), #[trigger(2)] g2(j))
        )));

    // :pattern ((g1. i@) (g2. j@))
    // :pattern ((f1. i@ j@) (g1. i@))
    assert(forall(|i: int, j: int|
        imply(
            #[trigger(1)] f1(i, j),
            f1(#[trigger(1, 2)] g1(i), #[trigger(2)] g2(j))
        )));
}

#[spec]
fn tr(i: int) -> bool {
    true
}

fn test_nat() {
    assert(forall(|i: nat| i >= 0 && tr(i)));
    assert(tr(300));
    assert(exists(|i: nat| i >= 0 && tr(i)));
    assert(exists(|i: u16| i >= 300 && tr(i)));
}
