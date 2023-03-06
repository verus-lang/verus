use builtin::*;
use builtin_macros::*;
#[cfg(not(vstd_todo))]
mod pervasive;

verus! {

#[verifier(external_body)]
fn test(n: u64, s: Ghost<int>)
    requires
        n > 10 && s@ >= n,
{
    println!("hello {}", n);
}

fn main() {
    test(15, ghost(200));
}

} // verus!
