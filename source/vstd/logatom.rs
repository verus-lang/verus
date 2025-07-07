use super::prelude::*;

verus! {

pub trait ReadOperation: Sized {
    // tracked resource(s) passed to callback
    type Resource;

    // executable result returned from operation
    type ExecResult;

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
    // tracked resource(s) passed to callback
    type Resource;

    // executable result returned from operation
    type ExecResult;

    // type of new value for the resource
    type NewState;

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
    type Completion;

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
    type Completion;

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

} // verus!
