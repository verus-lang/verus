use super::prelude::*;

verus! {

// == Logical atomicity library without syntactic support ==

pub trait ReadOperation: Sized {
    type Resource  /* = () */
    ;

    // tracked resource(s) passed to callback
    type ExecResult  /* = () */
    ;

    // executable result returned from operation
    spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool;

    // Optionally support peeking, which provides initial validation
    // before the operation is linearized.
    open spec fn peek_requires(self, r: Self::Resource) -> bool {
        true
    }

    open spec fn peek_ensures(self, r: Self::Resource) -> bool {
        true
    }
}

pub trait MutOperation: Sized {
    type Resource  /* = () */
    ;

    // tracked resource(s) passed to callback
    type ExecResult  /* = () */
    ;

    // executable result returned from operation
    type NewState  /* = () */
    ;

    // type of new value for the resource
    spec fn requires(
        self,
        pre: Self::Resource,
        new_state: Self::NewState,
        e: Self::ExecResult,
    ) -> bool;

    spec fn ensures(
        self,
        pre: Self::Resource,
        post: Self::Resource,
        new_state: Self::NewState,
    ) -> bool;

    // Optionally support peeking, which provides initial validation
    // before the operation is linearized.
    open spec fn peek_requires(self, r: Self::Resource) -> bool {
        true
    }

    open spec fn peek_ensures(self, r: Self::Resource) -> bool {
        true
    }
}

pub trait ReadLinearizer<Op: ReadOperation>: Sized {
    type Completion  /* = () */
    ;

    open spec fn namespaces(self) -> Set<int> {
        Set::empty()
    }

    open spec fn pre(self, op: Op) -> bool {
        true
    }

    open spec fn post(self, op: Op, r: Op::ExecResult, c: Self::Completion) -> bool {
        true
    }

    proof fn apply(
        tracked self,
        op: Op,
        tracked r: &Op::Resource,
        e: &Op::ExecResult,
    ) -> (tracked out: Self::Completion)
        requires
            self.pre(op),
            op.requires(*r, *e),
        ensures
            self.post(op, *e, out),
        opens_invariants self.namespaces()
    ;

    proof fn peek(tracked &self, op: Op, tracked r: &Op::Resource)
        requires
            self.pre(op),
            op.peek_requires(*r),
        ensures
            op.peek_ensures(*r),
        opens_invariants self.namespaces()
    ;
}

pub trait MutLinearizer<Op: MutOperation>: Sized {
    type Completion  /* = () */
    ;

    open spec fn namespaces(self) -> Set<int> {
        Set::empty()
    }

    open spec fn pre(self, op: Op) -> bool {
        true
    }

    open spec fn post(self, op: Op, r: Op::ExecResult, c: Self::Completion) -> bool {
        true
    }

    proof fn apply(
        tracked self,
        op: Op,
        tracked r: &mut Op::Resource,
        new_state: Op::NewState,
        e: &Op::ExecResult,
    ) -> (tracked out: Self::Completion)
        requires
            self.pre(op),
            op.requires(*old(r), new_state, *e),
        ensures
            op.ensures(*old(r), *r, new_state),
            self.post(op, *e, out),
        opens_invariants self.namespaces()
    ;

    proof fn peek(tracked &self, op: Op, tracked r: &Op::Resource)
        requires
            self.pre(op),
            op.peek_requires(*r),
        ensures
            op.peek_ensures(*r),
        opens_invariants self.namespaces()
    ;
}

// == Supporting types and functions for logically atomic functions ==

#[cfg_attr(verus_keep_ghost, verifier::proof)]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(Input))]
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(Output))]
pub struct AtomicUpdate<Input, Output> {
    _pd: std::marker::PhantomData<(Input, Output)>,
}

impl<Input, Output> AtomicUpdate<Input, Output> {
    pub uninterp spec fn req(&self, input: Input) -> bool;
    pub uninterp spec fn ens(&self, input: Input, output: Output) -> bool;

    pub uninterp spec fn has_fired(&self) -> bool;
    
    // TODO: this is a prototype, it will be replace by sound machinery
    #[verifier::external_body]
    pub proof fn assume_get_input() -> tracked Input {
        proof_from_false()
    }

    // TODO: this is a prototype, it will be replace by sound machinery
    #[verifier::external_body]
    pub proof fn assume_new() -> tracked AtomicUpdate<Input, Output> {
        proof_from_false()
    }
}


} // verus!
