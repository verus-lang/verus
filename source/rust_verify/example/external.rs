use builtin::*;
mod pervasive;

#[verifier(external_body)]
fn test(n: u64, #[spec] s: int) {
    requires(n > 10 && s >= n);
    println!("hello {}", n);
}

fn main() {
    test(15, 200);
}
