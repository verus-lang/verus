#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] struct_with_invariants_assoc_type_prefix verus_code! {
        use core::marker::PhantomData;
        use vstd::atomic_ghost::AtomicPtr;
        use vstd::prelude::*;

        pub trait HasTarget {
            type Target;
        }

        struct_with_invariants!{
            pub struct S<A: HasTarget>  {
                a: AtomicPtr<<A as HasTarget>::Target,_,(),_>,
                _phantom: PhantomData<*const A::Target>,
            }

            closed spec fn wf(self) -> bool {
                invariant on a with (_phantom) is (v:*mut <A as HasTarget>::Target,g:()) {
                    true
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_with_invariants_const_usage verus_code! {
        use vstd::prelude::*;
        use vstd::atomic_ghost::AtomicUsize;

        const ONE: usize = 1;

        struct_with_invariants!{
            pub struct S {
                x: AtomicUsize<_,(),_>,
            }

            closed spec fn wf(self) -> bool {
                invariant on x is (v:usize,g:()) {
                    v == ONE
                }
            }
        }
    } => Ok(())
}
