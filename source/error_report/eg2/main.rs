use vstd::prelude::*;
mod b;
mod c;
mod folder1;
mod folder2;

//use folder1::{d,e};
// mod hi::d;
// use hi::d;

verus!{
    fn hi() {
        assert(folder1::e::divides(2, 4));
    }
    
    #[verifier(external_body)]
    fn main() {
        hi();
        if (b::b() && c::c() && folder1::e::e() && folder2::f::f())
        {
            println!("This program correctly uses dependencies.");
        }
    }
}

