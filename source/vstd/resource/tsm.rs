//! Verified resource foundation for proof-producing tokenized state machines.
//!
//! A fragment is valid exactly when it can be completed to the embedding of an
//! invariant-satisfying machine state. The outer unit is distinct from a machine
//! fragment, so it remains valid even for a machine with an unsatisfiable invariant.
//! All ownership operations use the existing PCM resource interface.
use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::pcm::{PCM, Resource};
use super::relations::*;
use super::Loc;

verus! {

broadcast use super::super::iset::group_iset_lemmas;

/// Additive fragments for the `count` sharding strategy.
pub struct CountRA {
    pub count: nat,
}

impl ResourceAlgebra for CountRA {
    open spec fn valid(self) -> bool {
        true
    }

    open spec fn op(a: Self, b: Self) -> Self {
        Self { count: a.count + b.count }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

impl PCM for CountRA {
    open spec fn unit() -> Self {
        Self { count: 0 }
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

/// Both unit laws of a PCM.
pub proof fn pcm_units<P: PCM>(a: P)
    ensures
        P::op(P::unit(), a) == a,
        P::op(a, P::unit()) == a,
{
    a.op_unit();
    P::commutative(P::unit(), a);
}

/// Value observer of a checked field token.
///
/// Generated tokens implement this trait instead of declaring an inherent `value`,
/// as the trusted macro does with `ValueToken`. An inherent spec fn whose result type
/// has a typing invariant (e.g. `nat`, or a datatype with `nat` fields) gets its own
/// result-typing axiom, triggered on every call, in every client context that mentions
/// the token. A trait method implementation adds no axiom: calls share the trait
/// declaration's single generic one. In the verified allocator that per-token axiom
/// doubled the cost of unrelated client proofs (`span_queue_delete`, `page_queue_remove`).
pub trait TokenValue<V> {
    spec fn value(&self) -> V;
}

/// Count observer of a checked field token; see [`TokenValue`].
pub trait TokenCount {
    spec fn count(&self) -> nat;
}

/// A machine's mathematical state and separable fragment representation.
///
/// `Fragment::valid` is not used by this construction: only the total monoid laws
/// are needed. Validity is supplied by completion to `embed(state)` instead.
pub trait Machine: Sized {
    type Fragment: PCM;
    type State;

    spec fn invariant(state: Self::State) -> bool;

    spec fn embed(state: Self::State) -> Self::Fragment;
}

/// Completion to a full state witnesses validity of a machine fragment.
pub open spec fn completes<M: Machine>(fragment: M::Fragment) -> bool {
    exists|frame: M::Fragment, state: M::State|
        M::invariant(state) && M::Fragment::op(fragment, frame) == M::embed(state)
}

/// A machine fragment as a resource: valid if it completes to an invariant state.
pub enum Inved<M: Machine> {
    Unit,
    Value(M::Fragment),
}

impl<M: Machine> ResourceAlgebra for Inved<M> {
    open spec fn valid(self) -> bool {
        match self {
            Self::Unit => true,
            Self::Value(fragment) => completes::<M>(fragment),
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        // repeated `is` checks seem to be faster than matching on tuples.
        if a is Unit {
            b
        } else if b is Unit {
            a
        } else {
            Self::Value(M::Fragment::op(a->Value_0, b->Value_0))
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        if a is Value && b is Value && c is Value {
            M::Fragment::associative(a->Value_0, b->Value_0, c->Value_0);
        }
    }

    proof fn commutative(a: Self, b: Self) {
        if a is Value && b is Value {
            M::Fragment::commutative(a->Value_0, b->Value_0);
        }
    }

    proof fn valid_op(a: Self, b: Self) {
        if a is Value && b is Value {
            let x = a->Value_0;
            let y = b->Value_0;
            let (frame, state) = choose|frame: M::Fragment, state: M::State|
                M::invariant(state)
                    && M::Fragment::op(M::Fragment::op(x, y), frame) == M::embed(state);
            M::Fragment::associative(x, y, frame);
            assert(completes::<M>(x)) by {
                assert(M::invariant(state)
                    && M::Fragment::op(x, M::Fragment::op(y, frame)) == M::embed(state));
            }
        }
    }
}

impl<M: Machine> PCM for Inved<M> {
    open spec fn unit() -> Self {
        Self::Unit
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

/// The deterministic frame obligation produced by a machine transition.
///
/// The frame obligations (here and in `tsm_storage`) are opaque, so that their
/// quantifiers stay out of the generated proofs. The token operations use them
/// through the `*_sound` lemmas. The nondeterministic ones (and `update_point`,
/// `exchange_point`) are established through `update_point_intro`,
/// `exchange_point_intro*` and `frame_{update,exchange}_by_points`; the deterministic
/// `frame_update`, `frame_exchange` and `frame_guard` have no introduction lemma: a
/// proof of one (the raw fallback operations, the guard frames, `frame_exchange_with_extra`)
/// reveals it.
#[verifier::opaque]
pub open spec fn frame_update<M: Machine>(old: M::Fragment, new: M::Fragment) -> bool {
    forall|frame: M::Fragment, state: M::State|
        M::invariant(state) && M::Fragment::op(old, frame) == M::embed(state)
            ==> exists|next: M::State|
                M::invariant(next) && M::Fragment::op(new, frame) == M::embed(next)
}

/// Nondeterministic transitions may choose their output using the full state.
#[verifier::opaque]
pub open spec fn frame_update_nondeterministic<M: Machine>(
    old: M::Fragment,
    outputs: ISet<M::Fragment>,
) -> bool {
    forall|frame: M::Fragment, state: M::State|
        M::invariant(state) && M::Fragment::op(old, frame) == M::embed(state)
            ==> exists|new: M::Fragment, next: M::State|
                outputs.contains(new) && M::invariant(next)
                    && M::Fragment::op(new, frame) == M::embed(next)
}

/// `fragment` with frame `z` completes to the invariant state `state` (a named
/// trigger for the frames of generated operations' preconditions).
pub open spec fn completes_with<M: Machine>(
    fragment: M::Fragment,
    z: M::Fragment,
    state: M::State,
) -> bool {
    M::invariant(state) && M::Fragment::op(fragment, z) == M::embed(state)
}

/// One frame of a generated update: for the complete state around
/// `op(op(owned, h), z)`, some output `new` completes to an invariant state with
/// the same borrowed fragment `h` and frame `z`.
#[verifier::opaque]
pub open spec fn update_point<M: Machine>(
    owned: M::Fragment,
    h: M::Fragment,
    z: M::Fragment,
    pre: M::State,
    outputs: ISet<M::Fragment>,
) -> bool {
    exists|new: M::Fragment, post: M::State|
        #![trigger outputs.contains(new), M::embed(post)]
        outputs.contains(new) && M::invariant(post) && M::Fragment::op(
            M::Fragment::op(new, h),
            z,
        ) == M::embed(post)
}

/// Introduces [`update_point`] for the witnesses `new` and `post`.
pub proof fn update_point_intro<M: Machine>(
    owned: M::Fragment,
    h: M::Fragment,
    z: M::Fragment,
    pre: M::State,
    outputs: ISet<M::Fragment>,
    new: M::Fragment,
    post: M::State,
)
    requires
        outputs.contains(new),
        M::invariant(post),
        M::Fragment::op(M::Fragment::op(new, h), z) == M::embed(post),
    ensures
        update_point::<M>(owned, h, z, pre, outputs),
{
    reveal(update_point);
}

/// The frame obligation of a generated update, from its proof for each frame:
/// the outputs are lifted by the borrowed fragment `h`.
pub proof fn frame_update_by_points<M: Machine>(
    owned: M::Fragment,
    h: M::Fragment,
    outputs: ISet<M::Fragment>,
)
    requires
        forall|z: M::Fragment, pre: M::State|
            M::invariant(pre) && M::Fragment::op(M::Fragment::op(owned, h), z) == M::embed(pre)
                ==> #[trigger] update_point::<M>(owned, h, z, pre, outputs),
    ensures
        frame_update_nondeterministic::<M>(
            M::Fragment::op(owned, h),
            outputs.map(|new: M::Fragment| M::Fragment::op(new, h)),
        ),
{
    reveal(update_point);
    reveal(frame_update_nondeterministic);
    let lifted = outputs.map(|new: M::Fragment| M::Fragment::op(new, h));
    assert forall|z: M::Fragment, pre: M::State|
        M::invariant(pre) && M::Fragment::op(M::Fragment::op(owned, h), z) == M::embed(
            pre,
        ) implies exists|new: M::Fragment, next: M::State|
        lifted.contains(new) && M::invariant(next) && M::Fragment::op(new, z) == M::embed(
            next,
        ) by {
        assert(update_point::<M>(owned, h, z, pre, outputs));
        let (new, post) = choose|new: M::Fragment, post: M::State|
            #![trigger outputs.contains(new), M::embed(post)]
            outputs.contains(new) && M::invariant(post) && M::Fragment::op(
                M::Fragment::op(new, h),
                z,
            ) == M::embed(post);
        assert(lifted.contains(M::Fragment::op(new, h)));
    }
}

/// Complete-state frame obligations imply PCM frame-preserving updates.
pub proof fn frame_update_sound<M: Machine>(old: M::Fragment, new: M::Fragment)
    requires
        frame_update::<M>(old, new),
    ensures
        frame_preserving_update(Inved::<M>::Value(old), Inved::<M>::Value(new)),
{
    reveal(frame_update);
    assert forall|outer: Inved<M>|
        #[trigger] Inved::<M>::op(Inved::Value(old), outer).valid()
            implies Inved::<M>::op(Inved::Value(new), outer).valid() by {
        let external = match outer {
            Inved::Unit => M::Fragment::unit(),
            Inved::Value(f) => f,
        };
        M::Fragment::op_unit(old);
        M::Fragment::op_unit(new);
        let (completion, state) = choose|completion: M::Fragment, state: M::State|
            M::invariant(state)
                && M::Fragment::op(M::Fragment::op(old, external), completion)
                    == M::embed(state);
        M::Fragment::associative(old, external, completion);
        let frame = M::Fragment::op(external, completion);
        let next = choose|next: M::State|
            M::invariant(next) && M::Fragment::op(new, frame) == M::embed(next);
        M::Fragment::associative(new, external, completion);
        assert(completes::<M>(M::Fragment::op(new, external)));
    }
}

/// A checked nondeterministic frame update of machine fragments is a frame-preserving
/// update of the resources holding them.
pub proof fn frame_update_nondeterministic_sound<M: Machine>(
    old: M::Fragment,
    outputs: ISet<M::Fragment>,
)
    requires
        frame_update_nondeterministic::<M>(old, outputs),
    ensures
        frame_preserving_update_nondeterministic(
            Inved::<M>::Value(old),
            ISet::new(|value: Inved<M>| value is Value && outputs.contains(value->Value_0)),
        ),
{
    reveal(frame_update_nondeterministic);
    let wrapped = ISet::new(
        |value: Inved<M>| value is Value && outputs.contains(value->Value_0),
    );
    assert forall|outer: Inved<M>|
        #[trigger] Inved::<M>::op(Inved::Value(old), outer).valid()
            implies exists|value: Inved<M>| #[trigger] wrapped.contains(value)
                && Inved::<M>::op(value, outer).valid() by {
        let external = match outer {
            Inved::Unit => M::Fragment::unit(),
            Inved::Value(f) => f,
        };
        M::Fragment::op_unit(old);
        let (completion, state) = choose|completion: M::Fragment, state: M::State|
            M::invariant(state)
                && M::Fragment::op(M::Fragment::op(old, external), completion)
                    == M::embed(state);
        M::Fragment::associative(old, external, completion);
        let frame = M::Fragment::op(external, completion);
        let (new, next) = choose|new: M::Fragment, next: M::State|
            outputs.contains(new) && M::invariant(next)
                && M::Fragment::op(new, frame) == M::embed(next);
        M::Fragment::associative(new, external, completion);
        M::Fragment::op_unit(new);
        assert(completes::<M>(M::Fragment::op(new, external)));
        assert(wrapped.contains(Inved::Value(new))
            && Inved::<M>::op(Inved::Value(new), outer).valid());
    }
}

/// Lift the output predicate through an explicitly borrowed fragment.
pub proof fn frame_update_nondeterministic_shared_sound<M: Machine>(
    old: M::Fragment,
    shared: M::Fragment,
    outputs: ISet<M::Fragment>,
)
    requires
        frame_update_nondeterministic::<M>(
            M::Fragment::op(old, shared),
            outputs.map(|new: M::Fragment| M::Fragment::op(new, shared)),
        ),
    ensures
        frame_preserving_update_nondeterministic(
            Inved::<M>::op(Inved::Value(old), Inved::Value(shared)),
            set_op(
                ISet::new(|value: Inved<M>| value is Value && outputs.contains(value->Value_0)),
                Inved::<M>::Value(shared),
            ),
        ),
{
    let lifted = outputs.map(|new: M::Fragment| M::Fragment::op(new, shared));
    frame_update_nondeterministic_sound::<M>(M::Fragment::op(old, shared), lifted);
    let wrapped = ISet::new(
        |value: Inved<M>| value is Value && outputs.contains(value->Value_0),
    );
    let wrapped_lifted = ISet::new(
        |value: Inved<M>| value is Value && lifted.contains(value->Value_0),
    );
    let combined = set_op(wrapped, Inved::<M>::Value(shared));
    assert(wrapped_lifted =~= combined) by {
        assert forall|value: Inved<M>|
            #[trigger] wrapped_lifted.contains(value) <==> combined.contains(value) by {
            if wrapped_lifted.contains(value) {
                let new = choose|new: M::Fragment|
                    outputs.contains(new) && value->Value_0 == M::Fragment::op(new, shared);
                assert(wrapped.contains(Inved::Value(new)));
                assert(value == Inved::<M>::op(Inved::Value(new), Inved::Value(shared)));
                assert(combined.contains(value));
            }
            if combined.contains(value) {
                let source = choose|source: Inved<M>|
                    wrapped.contains(source)
                        && value == Inved::<M>::op(source, Inved::Value(shared));
                assert(lifted.contains(value->Value_0));
                assert(wrapped_lifted.contains(value));
            }
        };
    }
}

/// Ownership of a machine fragment at a protocol location.
#[verifier::accept_recursive_types(M)]
pub tracked struct Token<M: Machine> {
    resource: Resource<Inved<M>>,
}

impl<M: Machine> Token<M> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.resource.value() is Value
    }

    pub closed spec fn fragment(self) -> M::Fragment {
        self.resource.value()->Value_0
    }

    pub closed spec fn loc(self) -> Loc {
        self.resource.loc()
    }

    pub proof fn alloc(fragment: M::Fragment) -> (tracked out: Self)
        requires
            completes::<M>(fragment),
        ensures
            out.fragment() == fragment,
    {
        let tracked resource = Resource::alloc(Inved::Value(fragment));
        Self { resource }
    }

    pub proof fn alloc_state(state: M::State) -> (tracked out: Self)
        requires
            M::invariant(state),
        ensures
            out.fragment() == M::embed(state),
    {
        M::Fragment::op_unit(M::embed(state));
        Self::alloc(M::embed(state))
    }

    pub proof fn validate(tracked &self)
        ensures
            completes::<M>(self.fragment()),
    {
        use_type_invariant(self);
        self.resource.validate();
    }

    /// A common completion for read-only references, which may refer to the
    /// same token. Its completion frames are separate witnesses; this does
    /// not validate the separating composition of the input fragments.
    pub proof fn compatible_with(tracked &self, tracked other: &Self)
        -> (out: (M::State, M::Fragment, M::Fragment))
        requires
            self.loc() == other.loc(),
        ensures
            M::invariant(out.0),
            M::Fragment::op(self.fragment(), out.1) == M::embed(out.0),
            M::Fragment::op(other.fragment(), out.2) == M::embed(out.0),
    {
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked upper = self.resource.join_shared(&other.resource);
        upper.validate();
        let left = choose|left: Inved<M>|
            Inved::<M>::op(self.resource.value(), left) == upper.value();
        let right = choose|right: Inved<M>|
            Inved::<M>::op(other.resource.value(), right) == upper.value();
        assert(upper.value() is Value);
        let (frame, state) = choose|frame: M::Fragment, state: M::State|
            M::invariant(state)
                && M::Fragment::op(upper.value()->Value_0, frame) == M::embed(state);
        let left_remainder = if left is Unit { M::Fragment::unit() } else { left->Value_0 };
        let right_remainder = if right is Unit { M::Fragment::unit() } else { right->Value_0 };
        if left is Unit {
            self.fragment().op_unit();
        }
        if right is Unit {
            other.fragment().op_unit();
        }
        assert(M::Fragment::op(self.fragment(), left_remainder) == upper.value()->Value_0);
        assert(M::Fragment::op(other.fragment(), right_remainder) == upper.value()->Value_0);
        M::Fragment::associative(self.fragment(), left_remainder, frame);
        M::Fragment::associative(other.fragment(), right_remainder, frame);
        (
            state,
            M::Fragment::op(left_remainder, frame),
            M::Fragment::op(right_remainder, frame),
        )
    }

    /// Proves `fact` from every completion compatible with both tokens.
    pub proof fn facts_2(tracked &self, tracked other: &Self, fact: bool)
        requires
            self.loc() == other.loc(),
            forall|left_frame: M::Fragment, right_frame: M::Fragment, state: M::State|
                M::invariant(state)
                    && M::Fragment::op(self.fragment(), left_frame) == M::embed(state)
                    && M::Fragment::op(other.fragment(), right_frame) == M::embed(state)
                    ==> fact,
        ensures
            fact,
    {
        let (state, left_frame, right_frame) = self.compatible_with(other);
    }

    /// Three read-only references share a completion, including when some or
    /// all references alias. Each input has its own independent remainder.
    pub proof fn compatible_3(tracked &self, tracked second: &Self, tracked third: &Self)
        -> (out: (M::State, M::Fragment, M::Fragment, M::Fragment))
        requires
            self.loc() == second.loc(),
            self.loc() == third.loc(),
        ensures
            M::invariant(out.0),
            M::Fragment::op(self.fragment(), out.1) == M::embed(out.0),
            M::Fragment::op(second.fragment(), out.2) == M::embed(out.0),
            M::Fragment::op(third.fragment(), out.3) == M::embed(out.0),
    {
        use_type_invariant(self);
        use_type_invariant(second);
        use_type_invariant(third);
        let tracked first_two = self.resource.join_shared(&second.resource);
        let tracked upper = first_two.join_shared(&third.resource);
        upper.validate();
        let first_remainder = choose|remainder: Inved<M>|
            Inved::<M>::op(self.resource.value(), remainder) == first_two.value();
        let second_remainder = choose|remainder: Inved<M>|
            Inved::<M>::op(second.resource.value(), remainder) == first_two.value();
        let common_remainder = choose|remainder: Inved<M>|
            Inved::<M>::op(first_two.value(), remainder) == upper.value();
        let third_remainder = choose|remainder: Inved<M>|
            Inved::<M>::op(third.resource.value(), remainder) == upper.value();
        Inved::<M>::associative(self.resource.value(), first_remainder, common_remainder);
        Inved::<M>::associative(second.resource.value(), second_remainder, common_remainder);
        let first_remainder = Inved::<M>::op(first_remainder, common_remainder);
        let second_remainder = Inved::<M>::op(second_remainder, common_remainder);
        assert(upper.value() is Value);
        let (frame, state) = choose|frame: M::Fragment, state: M::State|
            M::invariant(state)
                && M::Fragment::op(upper.value()->Value_0, frame) == M::embed(state);
        let first_remainder = if first_remainder is Unit {
            M::Fragment::unit()
        } else {
            first_remainder->Value_0
        };
        let second_remainder = if second_remainder is Unit {
            M::Fragment::unit()
        } else {
            second_remainder->Value_0
        };
        let third_remainder = if third_remainder is Unit {
            M::Fragment::unit()
        } else {
            third_remainder->Value_0
        };
        self.fragment().op_unit();
        second.fragment().op_unit();
        third.fragment().op_unit();
        assert(M::Fragment::op(self.fragment(), first_remainder) == upper.value()->Value_0);
        assert(M::Fragment::op(second.fragment(), second_remainder) == upper.value()->Value_0);
        assert(M::Fragment::op(third.fragment(), third_remainder) == upper.value()->Value_0);
        M::Fragment::associative(self.fragment(), first_remainder, frame);
        M::Fragment::associative(second.fragment(), second_remainder, frame);
        M::Fragment::associative(third.fragment(), third_remainder, frame);
        (
            state,
            M::Fragment::op(first_remainder, frame),
            M::Fragment::op(second_remainder, frame),
            M::Fragment::op(third_remainder, frame),
        )
    }

    /// Proves `fact` from every completion compatible with all three tokens.
    pub proof fn facts_3(tracked &self, tracked second: &Self, tracked third: &Self, fact: bool)
        requires
            self.loc() == second.loc(),
            self.loc() == third.loc(),
            forall|first_frame: M::Fragment, second_frame: M::Fragment,
                third_frame: M::Fragment, state: M::State|
                M::invariant(state)
                    && M::Fragment::op(self.fragment(), first_frame) == M::embed(state)
                    && M::Fragment::op(second.fragment(), second_frame) == M::embed(state)
                    && M::Fragment::op(third.fragment(), third_frame) == M::embed(state)
                    ==> fact,
        ensures
            fact,
    {
        let (state, first_frame, second_frame, third_frame) = self.compatible_3(second, third);
    }

    pub proof fn join(tracked self, tracked other: Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            out.fragment() == M::Fragment::op(self.fragment(), other.fragment()),
    {
        use_type_invariant(&self);
        use_type_invariant(&other);
        let tracked resource = self.resource.join(other.resource);
        Self { resource }
    }

    pub proof fn split(tracked self, left: M::Fragment, right: M::Fragment)
        -> (tracked out: (Self, Self))
        requires
            self.fragment() == M::Fragment::op(left, right),
        ensures
            out.0.loc() == self.loc(),
            out.1.loc() == self.loc(),
            out.0.fragment() == left,
            out.1.fragment() == right,
    {
        use_type_invariant(&self);
        let tracked (left, right) = self.resource.split(Inved::Value(left), Inved::Value(right));
        (Self { resource: left }, Self { resource: right })
    }

    pub proof fn update(tracked self, new: M::Fragment) -> (tracked out: Self)
        requires
            frame_update::<M>(self.fragment(), new),
        ensures
            out.loc() == self.loc(),
            out.fragment() == new,
    {
        use_type_invariant(&self);
        frame_update_sound::<M>(self.fragment(), new);
        let tracked resource = self.resource.update(Inved::Value(new));
        Self { resource }
    }

    pub proof fn update_nondeterministic(tracked self, outputs: ISet<M::Fragment>)
        -> (tracked out: Self)
        requires
            frame_update_nondeterministic::<M>(self.fragment(), outputs),
        ensures
            out.loc() == self.loc(),
            outputs.contains(out.fragment()),
    {
        use_type_invariant(&self);
        frame_update_nondeterministic_sound::<M>(self.fragment(), outputs);
        let wrapped = ISet::new(
            |value: Inved<M>| value is Value && outputs.contains(value->Value_0),
        );
        let tracked resource = self.resource.update_nondeterministic(wrapped);
        Self { resource }
    }

    /// Choose an owned output while keeping a borrowed fragment unchanged.
    pub proof fn update_nondeterministic_with_shared(
        tracked self,
        tracked other: &Self,
        outputs: ISet<M::Fragment>,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_update_nondeterministic::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                outputs.map(|new: M::Fragment| M::Fragment::op(new, other.fragment())),
            ),
        ensures
            out.loc() == self.loc(),
            outputs.contains(out.fragment()),
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        frame_update_nondeterministic_shared_sound::<M>(
            self.fragment(),
            other.fragment(),
            outputs,
        );
        let wrapped = ISet::new(
            |value: Inved<M>| value is Value && outputs.contains(value->Value_0),
        );
        let tracked resource = self.resource.update_nondeterministic_with_shared(
            &other.resource,
            wrapped,
        );
        Self { resource }
    }

    /// A borrowed fragment may support an update while its ownership stays put.
    pub proof fn update_with_shared(
        tracked self,
        tracked other: &Self,
        new: M::Fragment,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_update::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                M::Fragment::op(new, other.fragment()),
            ),
        ensures
            out.loc() == self.loc(),
            out.fragment() == new,
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        frame_update_sound::<M>(
            M::Fragment::op(self.fragment(), other.fragment()),
            M::Fragment::op(new, other.fragment()),
        );
        let tracked resource = self.resource.update_with_shared(
            &other.resource,
            Inved::Value(new),
        );
        Self { resource }
    }

    /// Observe the separating composition with a borrowed token.
    pub proof fn validate_2(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            *final(self) == *old(self),
            completes::<M>(M::Fragment::op(final(self).fragment(), other.fragment())),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.resource.validate_2(&other.resource);
    }

    /// Obtain the empty machine fragment at an existing location. This is
    /// distinct from the outer PCM unit, whose validity needs no machine state.
    pub proof fn empty(tracked &self) -> (tracked out: Self)
        ensures
            out.loc() == self.loc(),
            out.fragment() == M::Fragment::unit(),
    {
        use_type_invariant(self);
        let empty = Inved::<M>::Value(M::Fragment::unit());
        let value = self.resource.value();
        M::Fragment::commutative(M::Fragment::unit(), self.fragment());
        M::Fragment::op_unit(self.fragment());
        assert(Inved::<M>::op(empty, value) == value);
        assert(frame_preserving_update(value, Inved::<M>::op(empty, value)));
        let tracked resource = self.resource.duplicate_previous(empty);
        Self { resource }
    }

    /// Persistent fragments duplicate when their composition is idempotent.
    pub proof fn duplicate(tracked &self) -> (tracked out: Self)
        requires
            M::Fragment::op(self.fragment(), self.fragment()) == self.fragment(),
        ensures
            out.loc() == self.loc(),
            out.fragment() == self.fragment(),
    {
        use_type_invariant(self);
        let value = self.resource.value();
        assert(Inved::<M>::op(value, value) == value);
        assert(frame_preserving_update(value, Inved::<M>::op(value, value)));
        let tracked resource = self.resource.duplicate_previous(value);
        Self { resource }
    }

    /// Recover a pure fact entailed by every completion of this token.
    pub proof fn facts(tracked &self, fact: bool)
        requires
            forall|frame: M::Fragment, state: M::State|
                M::invariant(state)
                    && M::Fragment::op(self.fragment(), frame) == M::embed(state) ==> fact,
        ensures
            fact,
    {
        self.validate();
    }
}

/// A lifetime-bound read of an actual resource. It owns no machine fragment.
#[verifier::accept_recursive_types(M)]
pub tracked struct Observation<'a, M: Machine> {
    resource: &'a Resource<Inved<M>>,
}

/// Opaque: the generated proofs use it through the lemmas below (and introduce it
/// in the generic-token observations).
#[verifier::opaque]
pub open spec fn fragment_included<M: Machine>(source: M::Fragment, upper: M::Fragment) -> bool {
    exists|frame: M::Fragment| M::Fragment::op(source, frame) == upper
}

/// Every fragment is included in itself, with the monoid unit as its remainder.
pub proof fn fragment_included_reflexive<M: Machine>(source: M::Fragment)
    ensures
        fragment_included::<M>(source, source),
{
    reveal(fragment_included);
    M::Fragment::op_unit(source);
    assert(M::Fragment::op(source, M::Fragment::unit()) == source);
}

/// The unit is included in every fragment.
pub proof fn fragment_included_unit<M: Machine>(upper: M::Fragment)
    ensures
        fragment_included::<M>(M::Fragment::unit(), upper),
{
    reveal(fragment_included);
    M::Fragment::commutative(M::Fragment::unit(), upper);
    M::Fragment::op_unit(upper);
    assert(M::Fragment::op(M::Fragment::unit(), upper) == upper);
}

/// Inclusion composes by combining the two remainders.
pub proof fn fragment_included_transitive<M: Machine>(
    source: M::Fragment,
    middle: M::Fragment,
    upper: M::Fragment,
)
    requires
        fragment_included::<M>(source, middle),
        fragment_included::<M>(middle, upper),
    ensures
        fragment_included::<M>(source, upper),
{
    reveal(fragment_included);
    let left = choose|left: M::Fragment| M::Fragment::op(source, left) == middle;
    let right = choose|right: M::Fragment| M::Fragment::op(middle, right) == upper;
    M::Fragment::associative(source, left, right);
    assert(M::Fragment::op(source, M::Fragment::op(left, right)) == upper);
}

/// Complete a smaller fragment using an inclusion remainder and a full-state frame.
/// Each operand is included in a composition.
pub proof fn fragment_included_op_left<M: Machine>(a: M::Fragment, b: M::Fragment)
    ensures
        fragment_included::<M>(a, M::Fragment::op(a, b)),
{
    reveal(fragment_included);
    assert(M::Fragment::op(a, b) == M::Fragment::op(a, b));
}

pub proof fn fragment_included_op_right<M: Machine>(a: M::Fragment, b: M::Fragment)
    ensures
        fragment_included::<M>(b, M::Fragment::op(a, b)),
{
    reveal(fragment_included);
    M::Fragment::commutative(a, b);
    assert(M::Fragment::op(b, a) == M::Fragment::op(a, b));
}

/// A remainder of `source` in `upper` (if `source` is included in `upper`).
pub open spec fn fragment_frame<M: Machine>(source: M::Fragment, upper: M::Fragment) -> M::Fragment {
    choose|frame: M::Fragment| M::Fragment::op(source, frame) == upper
}

/// `fragment_frame` is a remainder of an included fragment.
pub proof fn fragment_included_frame<M: Machine>(source: M::Fragment, upper: M::Fragment)
    requires
        fragment_included::<M>(source, upper),
    ensures
        M::Fragment::op(source, fragment_frame::<M>(source, upper)) == upper,
{
    reveal(fragment_included);
}

pub proof fn fragment_included_completion<M: Machine>(
    source: M::Fragment,
    upper: M::Fragment,
    frame: M::Fragment,
    state: M::State,
) -> (out: M::Fragment)
    requires
        fragment_included::<M>(source, upper),
        M::Fragment::op(upper, frame) == M::embed(state),
    ensures
        M::Fragment::op(source, out) == M::embed(state),
{
    reveal(fragment_included);
    let remainder = choose|remainder: M::Fragment| M::Fragment::op(source, remainder) == upper;
    M::Fragment::associative(source, remainder, frame);
    M::Fragment::op(remainder, frame)
}

impl<'a, M: Machine> Observation<'a, M> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.resource.value() is Value
    }

    pub closed spec fn loc(self) -> Loc {
        self.resource.loc()
    }

    pub closed spec fn fragment(self) -> M::Fragment {
        self.resource.value()->Value_0
    }

    /// Join potentially overlapping observations. The result includes each
    /// input separately; it does not promise their separating composition.
    pub proof fn join(tracked &self, tracked other: &Self) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
        ensures
            out.loc() == self.loc(),
            fragment_included::<M>(self.fragment(), out.fragment()),
            fragment_included::<M>(other.fragment(), out.fragment()),
    {
        reveal(fragment_included);
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked upper = self.resource.join_shared(other.resource);
        let left = choose|frame: Inved<M>|
            Inved::<M>::op(self.resource.value(), frame) == upper.value();
        let right = choose|frame: Inved<M>|
            Inved::<M>::op(other.resource.value(), frame) == upper.value();
        assert(upper.value() is Value);
        let left = if left is Unit {
            M::Fragment::unit()
        } else {
            left->Value_0
        };
        let right = if right is Unit {
            M::Fragment::unit()
        } else {
            right->Value_0
        };
        self.fragment().op_unit();
        other.fragment().op_unit();
        assert(M::Fragment::op(self.fragment(), left) == upper.value()->Value_0);
        assert(M::Fragment::op(other.fragment(), right) == upper.value()->Value_0);
        Observation { resource: upper }
    }

    pub proof fn validate(tracked &self)
        ensures
            completes::<M>(self.fragment()),
    {
        use_type_invariant(self);
        self.resource.validate();
    }
}

impl<M: Machine> Token<M> {
    pub proof fn observe<'a>(tracked &'a self) -> (tracked out: Observation<'a, M>)
        ensures
            out.loc() == self.loc(),
            out.fragment() == self.fragment(),
    {
        use_type_invariant(self);
        Observation { resource: &self.resource }
    }

    /// Validate the separating composition with an actual borrowed observation.
    pub proof fn validate_with_observation(tracked &mut self, tracked other: &Observation<M>)
        requires
            old(self).loc() == other.loc(),
        ensures
            *final(self) == *old(self),
            completes::<M>(M::Fragment::op(final(self).fragment(), other.fragment())),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.resource.validate_2(other.resource);
    }

    /// Update actual owned rights while preserving a real borrowed observation.
    pub proof fn update_with_observation(
        tracked self,
        tracked other: &Observation<M>,
        new: M::Fragment,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_update::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                M::Fragment::op(new, other.fragment()),
            ),
        ensures
            out.loc() == self.loc(),
            out.fragment() == new,
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        frame_update_sound::<M>(
            M::Fragment::op(self.fragment(), other.fragment()),
            M::Fragment::op(new, other.fragment()),
        );
        let tracked resource = self.resource.update_with_shared(other.resource, Inved::Value(new));
        Self { resource }
    }

    pub proof fn update_nondeterministic_with_observation(
        tracked self,
        tracked other: &Observation<M>,
        outputs: ISet<M::Fragment>,
    ) -> (tracked out: Self)
        requires
            self.loc() == other.loc(),
            frame_update_nondeterministic::<M>(
                M::Fragment::op(self.fragment(), other.fragment()),
                outputs.map(|new: M::Fragment| M::Fragment::op(new, other.fragment())),
            ),
        ensures
            out.loc() == self.loc(),
            outputs.contains(out.fragment()),
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        frame_update_nondeterministic_shared_sound::<M>(self.fragment(), other.fragment(), outputs);
        let wrapped = ISet::new(
            |value: Inved<M>| value is Value && outputs.contains(value->Value_0),
        );
        let tracked resource = self.resource.update_nondeterministic_with_shared(
            other.resource,
            wrapped,
        );
        Self { resource }
    }
}

impl<'a, M: Machine> Observation<'a, M> {
    /// Restrict a real borrowed observation to a included fragment. No owned
    /// rights are created; the original lifetime and location are retained.
    pub proof fn weaken(tracked &self, target: M::Fragment) -> (tracked out: Self)
        requires fragment_included::<M>(target, self.fragment()),
        ensures out.loc() == self.loc(), out.fragment() == target,
    {
        reveal(fragment_included);
        use_type_invariant(self);
        let frame = choose|frame: M::Fragment| M::Fragment::op(target, frame) == self.fragment();
        assert(Inved::<M>::op(Inved::Value(target), Inved::Value(frame)) == self.resource.value());
        let tracked resource = self.resource.weaken(Inved::Value(target));
        Observation {resource}
    }
}

} // verus!
