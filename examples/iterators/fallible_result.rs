#![feature(try_trait_v2_residual)]

use core::ops::{ControlFlow, FromResidual, Try};
use vstd::prelude::*;
use vstd::std_specs::control_flow::{try_laws, TrySpec};
use vstd::std_specs::iter::{try_fold_post, try_fold_prefix, IteratorSpec};

verus! {

proof fn lemma_try_fold_overwrite<A, R: Try<Output = A>, F: FnMut(A, A) -> R>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: A,
    f: F,
    result: R,
    consumed: int,
    remaining_produces: Seq<bool>,
)
    requires
        try_laws::<R>(),
        items.len() > 0,
        try_fold_post(items, produces, init, f, result, consumed, remaining_produces),
        forall|acc: A, x: A, value: R| #[trigger]
            f.ensures((acc, x), value) ==> value.branch_model() == ControlFlow::Continue(x),
    ensures
        consumed == items.len(),
        result.branch_model() == ControlFlow::Continue(items.last()),
{
    match result.branch_model() {
        ControlFlow::Break(residual) => {
            let (bs, results, failed) = choose|bs: Seq<A>, results: Seq<R>, failed: R|
                try_fold_prefix(items, produces, init, f, bs, results) && results.len() == consumed
                    - 1 && f.ensures((bs.last(), items[results.len() as int]), failed)
                    && failed.branch_model() == ControlFlow::Break(residual);
        },
        ControlFlow::Continue(output) => {
            let (bs, results) = choose|bs: Seq<A>, results: Seq<R>|
                try_fold_prefix(items, produces, init, f, bs, results) && results.len()
                    == items.len() && output == bs.last();
            let j = items.len() - 1;
            assert(f.ensures((bs[j], items[j]), results[j]));
            assert(results[j].branch_model() == ControlFlow::Continue(bs[j + 1]));
        },
    }
}

proof fn lemma_try_fold_always_break<A, B, R: Try<Output = B>, F: FnMut(B, A) -> R>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: B,
    f: F,
    residual_for: spec_fn(A) -> R::Residual,
    result: R,
    consumed: int,
    remaining_produces: Seq<bool>,
)
    requires
        try_laws::<R>(),
        items.len() > 0,
        try_fold_post(items, produces, init, f, result, consumed, remaining_produces),
        forall|acc: B, x: A, value: R| #[trigger]
            f.ensures((acc, x), value) ==> value.branch_model() == ControlFlow::Break(
                residual_for(x),
            ),
    ensures
        consumed == 1,
        result.branch_model() == ControlFlow::Break(residual_for(items[0])),
{
    match result.branch_model() {
        ControlFlow::Continue(output) => {
            let (bs, results) = choose|bs: Seq<B>, results: Seq<R>|
                try_fold_prefix(items, produces, init, f, bs, results) && results.len()
                    == items.len() && output == bs.last();
            assert(f.ensures((bs[0], items[0]), results[0]));
            assert(results[0].branch_model() == ControlFlow::Continue(bs[1]));
        },
        ControlFlow::Break(residual) => {
            let (bs, results, failed) = choose|bs: Seq<B>, results: Seq<R>, failed: R|
                try_fold_prefix(items, produces, init, f, bs, results) && results.len() == consumed
                    - 1 && f.ensures((bs.last(), items[results.len() as int]), failed)
                    && failed.branch_model() == ControlFlow::Break(residual);
            if results.len() > 0 {
                assert(f.ensures((bs[0], items[0]), results[0]));
                assert(results[0].branch_model() == ControlFlow::Continue(bs[1]));
            }
        },
    }
}

pub struct Stop {
    pub code: u32,
}

// Metadata survives when an adapter returns a callback result directly.
// Reconstructing the same classification resets the metadata.
pub struct Tagged<B> {
    pub value: Option<B>,
    pub code: u32,
    pub callback_result: bool,
}

impl<B> vstd::std_specs::control_flow::TrySpecImpl for Tagged<B> {
    open spec fn branch_model_is_valid() -> bool {
        true
    }

    open spec fn branch_model(self) -> ControlFlow<Stop, B> {
        match self.value {
            Some(b) => ControlFlow::Continue(b),
            None => ControlFlow::Break(Stop { code: self.code }),
        }
    }
}

impl<B> Try for Tagged<B> {
    type Output = B;

    type Residual = Stop;

    fn from_output(output: B) -> (result: Self)
        ensures
            result.value == Some(output) && result.code == 0 && !result.callback_result,
    {
        Self { value: Some(output), code: 0, callback_result: false }
    }

    fn branch(self) -> ControlFlow<Stop, B> {
        match self.value {
            Some(b) => ControlFlow::Continue(b),
            None => ControlFlow::Break(Stop { code: self.code }),
        }
    }
}

impl<B> FromResidual<Stop> for Tagged<B> {
    fn from_residual(residual: Stop) -> (result: Self)
        ensures
            result.value == None && result.code == residual.code && !result.callback_result,
    {
        Self { value: None, code: residual.code, callback_result: false }
    }
}

proof fn tagged_laws<B>()
    ensures
        try_laws::<Tagged<B>>(),
{
}

fn tagged_fold() {
    proof {
        tagged_laws::<u32>();
    }
    let mut it = vec![1u32, 2, 3].into_iter().take(2);
    let ghost input = it.remaining();
    let ghost produces = it.produces();
    let f = |acc: u32, x: u32| -> (ret: Tagged<u32>)
        ensures
            ret.value == Some(x) && ret.callback_result,
        { Tagged { value: Some(x), code: 0, callback_result: true } };
    let ret = it.try_fold(0, f);
    proof {
        lemma_try_fold_overwrite(
            input,
            produces,
            0u32,
            f,
            ret,
            input.len() - it.remaining().len(),
            it.produces(),
        );
    }
    assert(ret.branch_model() == ControlFlow::Continue(2));
    assert(it.remaining().len() == 0);
    // The contract intentionally makes no claim that callback_result is false.

    let mut it = vec![1u32, 2, 3].into_iter().skip(1);
    let ghost input = it.remaining().reverse();
    let ghost produces = it.produces().reverse();
    let f = |acc: u32, x: u32| -> (ret: Tagged<u32>)
        ensures
            ret.value == None && ret.code == x,
        { Tagged { value: None, code: x, callback_result: true } };
    let ret = it.try_rfold(0, f);
    proof {
        lemma_try_fold_always_break(
            input,
            produces,
            0u32,
            f,
            |x: u32| Stop { code: x },
            ret,
            input.len() - it.remaining().len(),
            it.produces().reverse(),
        );
    }
    assert(ret.branch_model() == ControlFlow::Break(Stop { code: 3 }));
    assert(it.remaining() =~= seq![2u32]);
}

} // verus!
// This marker implementation only supplies a Rust associated type. It has no
// executable operations or logical axioms.
impl<B> core::ops::Residual<B> for Stop {
    type TryType = Tagged<B>;
}

fn main() {}
