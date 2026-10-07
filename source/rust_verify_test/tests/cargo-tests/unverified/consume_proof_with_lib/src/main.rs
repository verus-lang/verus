use proof_with_lib::{negate, Counter};

// Standard rust tools see only the unverified stubs, which keep the exec
// signature and the real body.
fn main() {
    let b = negate(true, 1);
    let n = Counter(0).bump();
    println!("\n\nnegate(true, 1) = {b}, bump() = {n}\n\n");
}
