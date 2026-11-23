use basic_verified_lib::*;

fn main() {
    let u: u16 = 21;
    let dbl = double(u);
    println!("\n\nThe result is definitely going to be 42:\t{}\n\n", dbl);

    assert!(!proof_with_lib::negate(true, 1));
    assert_eq!(proof_with_lib::Counter(0).bump(), 7);
}
