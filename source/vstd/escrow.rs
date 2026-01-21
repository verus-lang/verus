
use crate::prelude::*;
use crate::pcm::*;
use crate::simple_pptr::*;
use crate::tokens::*;
use std::marker::PhantomData;

verus! {

/// Token PCM
enum TokenCarrier {
    Tok,
    Empty,
    Invalid,
}

impl PCM for TokenCarrier {
    closed spec fn valid(self) -> bool {
        match self {
            TokenCarrier::Invalid => false,
            TokenCarrier::Empty | TokenCarrier::Tok => true,
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        match self {
            TokenCarrier::Invalid => TokenCarrier::Invalid,
            TokenCarrier::Empty => other,
            TokenCarrier::Tok => match other {
                TokenCarrier::Invalid | TokenCarrier::Tok => TokenCarrier::Invalid,
                TokenCarrier::Empty => self,
            },
        }
    }

    closed spec fn unit() -> Self {
        TokenCarrier::Empty
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

pub struct Token {
    t: Resource<TokenCarrier>
}

impl Token {
    #[verifier::type_invariant]
    closed spec fn inv(&self) -> bool {
        self.resource().value() matches TokenCarrier::Tok
    }

    closed spec fn resource(&self) -> Resource<TokenCarrier> {
        self.t
    }

    pub proof fn new() -> (tracked result: Self)
    {
        let tracked carrier = TokenCarrier::Tok;
        let tracked t = Resource::alloc(carrier);
        Self { t }
    }
}

/// Escrow, in the style of https://plv.mpi-sws.org/igps/igps-full.pdf

pub trait Guard : Sized {
    spec fn id(&self) -> int;

    proof fn excl(tracked self, tracked other: Self) -> (tracked out: Self)
        ensures
            self.id() == other.id() ==> false,
            out == self
        ;
}

impl Guard for Token {
    closed spec fn id(&self) -> int {
        self.resource().loc()
    }

    proof fn excl(tracked self, tracked other: Self) -> (tracked out: Self) {
        if (self.id() == other.id()) {
            use_type_invariant(&self);
            use_type_invariant(&other);

            let tracked joined = self.t.join(other.t);
            joined.validate();
            assert(false);
            proof_from_false()
        } else {
            self
        }
    }
}

/// VerusSync tokens
pub struct UniqueSimpleTokenGuard<T: UniqueSimpleToken> {
    pub t: T
}

impl<T: UniqueSimpleToken> Guard for UniqueSimpleTokenGuard<T> {
    closed spec fn id(&self) -> int {
        self.t.instance_id().0
    }

    proof fn excl(tracked self, tracked other: Self) -> (tracked out: Self) {
        if (self.id() == other.id()) {
            let tracked mut s = self;
            s.t.unique(&other.t);
            assert(false);
            proof_from_false()
        } else {
            self
        }
    }
}

pub struct UniqueValueTokenGuard<V, T: UniqueValueToken<V>> {
    pub t: T,
    _v: PhantomData<V>
}

impl<V, T: UniqueValueToken<V>> Guard for UniqueValueTokenGuard<V, T> {
    closed spec fn id(&self) -> int {
        self.t.instance_id().0
    }

    proof fn excl(tracked self, tracked other: Self) -> (tracked out: Self) {
        if (self.id() == other.id()) {
            let tracked mut s = self;
            s.t.unique(&other.t);
            assert(false);
            proof_from_false()
        } else {
            self
        }
    }
}

pub trait Escrow<T, G: Guard> : Sized {
    // payload type will always be PointsTo for now. this avoids complication in footnote 7 in iGPS paper

    spec fn guard(&self) -> G;

    spec fn payload(&self) -> PointsTo<T>;

    proof fn intro(tracked payload: PointsTo<T>, guard_data: G) -> (tracked out: Self)
        ensures
            out.guard() == guard_data,
            out.payload() == payload
        ;

    proof fn elim(tracked &self, tracked guard: G) -> (tracked out: PointsTo<T>)
        requires
            self.guard() == guard
        ensures
            self.payload() == out
        ;

    proof fn persistent(tracked &self) -> (tracked out: Self)
        ensures
            self.guard() == out.guard(),
            self.payload() == out.payload()
        ;
}

}