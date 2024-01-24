use crate::prelude::*;
use core::ops::Range;

verus!{

#[verifier(external_type_specification)]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRange<Idx>(Range<Idx>);

pub trait StepSpec where Self: Sized {
    // REVIEW: it would be nice to be able to use SpecOrd::spec_lt (not yet supported)
    spec fn spec_is_lt(self, other: Self) -> bool;
    spec fn spec_steps_between(self, end: Self) -> Option<usize>;
    spec fn spec_forward_checked(self, count: usize) -> Option<Self>;
    spec fn spec_backward_checked(self, count: usize) -> Option<Self>;
}

pub spec fn spec_range_next<A>(a: Range<A>) -> (Range<A>, Option<A>);

#[verifier::external_fn_specification]
pub fn ex_range_next<A: core::iter::Step>(range: &mut Range<A>) -> (r: Option<A>)
    ensures (*range, r) == spec_range_next(*old(range))
{
    range.next()
}

} // verus!

macro_rules! step_specs {
    ($t: ty, $axiom: ident) => {
        verus! {
        impl StepSpec for $t {
            open spec fn spec_is_lt(self, other: Self) -> bool {
                self < other
            }
            open spec fn spec_steps_between(self, end: Self) -> Option<usize> {
                let n = end - self;
                if usize::MIN <= n <= usize::MAX {
                    Some(n as usize)
                } else {
                    None
                }
            }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> {
                if self + count <= $t::MAX {
                    Some((self + count) as $t)
                } else {
                    None
                }
            }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> {
                if self - count >= $t::MIN {
                    Some((self - count) as $t)
                } else {
                    None
                }
            }
        }
        // TODO: we might be able to make this generic over A: StepSpec
        // once we settle on a way to connect std traits like Step with spec traits like StepSpec.
        #[verifier::external_body]
        #[verifier::broadcast_forall]
        pub proof fn $axiom(range: Range<$t>)
            ensures
                range.start.spec_is_lt(range.end) ==>
                    // TODO (not important): use new "matches ==>" syntax here
                    (if let Some(n) = range.start.spec_forward_checked(1) {
                        spec_range_next(range) == (Range { start: n, ..range }, Some(range.start))
                    } else {
                        true
                    }),
                !range.start.spec_is_lt(range.end) ==>
                    #[trigger] spec_range_next(range) == (range, None::<$t>),
        {
        }
        } // verus!
    }
}

step_specs!(u8, axiom_spec_range_next_u8);
step_specs!(u16, axiom_spec_range_next_u16);
step_specs!(u32, axiom_spec_range_next_u32);
step_specs!(u64, axiom_spec_range_next_u64);
step_specs!(u128, axiom_spec_range_next_u128);
step_specs!(usize, axiom_spec_range_next_usize);
step_specs!(i8, axiom_spec_range_next_i8);
step_specs!(i16, axiom_spec_range_next_i16);
step_specs!(i32, axiom_spec_range_next_i32);
step_specs!(i64, axiom_spec_range_next_i64);
step_specs!(i128, axiom_spec_range_next_i128);
step_specs!(isize, axiom_spec_range_next_isize);
