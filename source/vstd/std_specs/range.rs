use super::super::prelude::*;
use super::super::view::View;
use core::ops::Range;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRange<Idx>(Range<Idx>);

pub trait StepSpec where Self: Sized {
    // REVIEW: it would be nice to be able to use SpecOrd::spec_lt (not yet supported)
    spec fn spec_is_lt(self, other: Self) -> bool;

    spec fn spec_steps_between(self, end: Self) -> Option<usize>;

    spec fn spec_steps_between_int(self, end: Self) -> int;

    spec fn spec_forward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_forward_checked_int(self, count: int) -> Option<Self>;

    spec fn spec_backward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_backward_checked_int(self, count: int) -> Option<Self>;
}

pub spec fn spec_range_next<A>(a: Range<A>) -> (Range<A>, Option<A>);

#[verifier::external_fn_specification]
pub fn ex_range_next<A: core::iter::Step>(range: &mut Range<A>) -> (r: Option<A>)
    ensures
        (*range, r) == spec_range_next(*old(range)),
{
    range.next()
}

pub struct RangeGhostIterator<A> {
    pub start: A,
    pub cur: A,
    pub end: A,
}

impl<A: StepSpec> super::super::pervasive::ForLoopGhostIteratorNew for Range<A> {
    type GhostIter = RangeGhostIterator<A>;

    open spec fn ghost_iter(&self) -> RangeGhostIterator<A> {
        RangeGhostIterator { start: self.start, cur: self.start, end: self.end }
    }
}

impl<
    A: StepSpec + core::iter::Step,
> super::super::pervasive::ForLoopGhostIterator for RangeGhostIterator<A> {
    type ExecIter = Range<A>;

    type Item = A;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Range<A>) -> bool {
        &&& self.cur == exec_iter.start
        &&& self.end == exec_iter.end
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        &&& self.start.spec_is_lt(self.cur) || self.start == self.cur
        &&& self.cur.spec_is_lt(self.end) || self.cur
            == self.end
        // TODO (not important): use new "matches ==>" syntax here
        &&& if let Some(init) = init {
            &&& init.start == init.cur
            &&& init.start == self.start
            &&& init.end == self.end
        } else {
            true
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        !self.cur.spec_is_lt(self.end)
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.cur.spec_steps_between_int(self.end))
    }

    open spec fn ghost_peek_next(&self) -> Option<A> {
        Some(self.cur)
    }

    open spec fn ghost_advance(&self, _exec_iter: &Range<A>) -> RangeGhostIterator<A> {
        RangeGhostIterator { cur: self.cur.spec_forward_checked(1).unwrap(), ..*self }
    }
}

impl<A: StepSpec + core::iter::Step> View for RangeGhostIterator<A> {
    type V = Seq<A>;

    // generate seq![start, start + 1, start + 2, ..., cur - 1]
    open spec fn view(&self) -> Seq<A> {
        Seq::new(
            self.start.spec_steps_between_int(self.cur) as nat,
            |i: int| self.start.spec_forward_checked_int(i).unwrap(),
        )
    }
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
            open spec fn spec_steps_between_int(self, end: Self) -> int {
                end - self
            }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> {
                self.spec_forward_checked_int(count as int)
            }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> {
                if self + count <= $t::MAX {
                    Some((self + count) as $t)
                } else {
                    None
                }
            }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> {
                self.spec_backward_checked_int(count as int)
            }
            open spec fn spec_backward_checked_int(self, count: int) -> Option<Self> {
                if self - count >= $t::MIN {
                    Some((self - count) as $t)
                } else {
                    None
                }
            }
        }
        // TODO: we might be able to make this generic over A: StepSpec
        // once we settle on a way to connect std traits like Step with spec traits like StepSpec.
        pub broadcast proof fn $axiom(range: Range<$t>)
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
            admit();
        }
        } // verus!
    };
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

verus! {

pub broadcast group group_range_axioms {
    axiom_spec_range_next_u8,
    axiom_spec_range_next_u16,
    axiom_spec_range_next_u32,
    axiom_spec_range_next_u64,
    axiom_spec_range_next_u128,
    axiom_spec_range_next_usize,
    axiom_spec_range_next_i8,
    axiom_spec_range_next_i16,
    axiom_spec_range_next_i32,
    axiom_spec_range_next_i64,
    axiom_spec_range_next_i128,
    axiom_spec_range_next_isize,
}

} // verus!
