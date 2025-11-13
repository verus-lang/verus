use vstd::prelude::*;

verus! {
    struct a<b: Copy> {
        c: b,
        d: usize,
        e: usize
    }
    
    impl<b: Copy> a<b> {
        #[verifier::type_invariant]
        spec fn f(self) -> bool;
        
        fn g(self) -> bool {
            proof {
                use_type_invariant(&self)
            }
            self.d != self.e
        }
    }
    
    fn main();
}
