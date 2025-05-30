use builtin::*;
use builtin_macros::*;

verus! {

#[verifier::external_body]
fn test(n: u64, s: Ghost<int>)
    requires
        n > 10 && s@ >= n,
{
    println!("hello {}", n);
}

fn main() {
    test(15, Ghost(200));
}

} // verus!
