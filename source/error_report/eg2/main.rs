use vstd::prelude::*;

mod b;
mod c;
mod hi;
// mod hi::d;
// use hi::d;

verus!{
    fn hi() {
        assert(hi::d::divides(2, 4));
    }
    
    #[verifier(external_body)]
    fn main() {
        hi();
        println!("hi");
    }
    

}

