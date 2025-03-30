use core::marker::PhantomData;
// use crate::vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way;
use crate::vstd::arithmetic::power::*;
use crate::vstd::arithmetic::power2::*;
use crate::vstd::arithmetic::mul::*;
use crate::vstd::calc_macro::*;
use crate::vstd::prelude::*;
use crate::vstd::group_vstd_default;
use crate::vstd::primitive_int::PrimitiveInt;

verus! {

broadcast use group_vstd_default;

pub trait Base {
    spec fn base() -> nat;

    proof fn base_min()
        ensures
            Self::base() > 1,
    ;
}

pub trait BasePow2: Base {
    spec fn bits() -> nat;

    proof fn bits_to_base()
        ensures
            Self::bits() > 1,
            Self::base() == pow2(Self::bits()),
    ;
}

pub trait CompatibleSmallerBaseFor<BIG: BasePow2>: BasePow2 {
    proof fn compatible()
        ensures
            BIG::bits() > Self::bits() && BIG::bits() % Self::bits() == 0,
    ;
}

pub enum Endian {
    Little, 
    Big,
}

pub uninterp spec fn endianness() -> Endian;

pub enum EndianNat<B: Base> {
    LittleEndianNat(LittleEndianNat<B>),
    BigEndianNat(BigEndianNat<B>),
}

// TODO: fix the return type once we've implemented BigEndianNat. 
// TODO: something relating PrimitiveInt to Integer, so that if it's a primitive int, then casting is fine
// TODO: currently I just pass the endianness in. But we might want to make that global in some sense
pub open spec fn to_big_ne<BIG, B>(n: Seq<B>, endianness: Endian) -> LittleEndianNat<BIG>
    where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG> + PrimitiveInt + Integer,
{
    match endianness {
        Endian::Little => LittleEndianNat::<B>::to_big::<BIG>(LittleEndianNat::<B>::new(Seq::new(n.len(), |i: int| n[i] as int))),
        Endian::Big => LittleEndianNat::<B>::to_big::<BIG>(LittleEndianNat::<B>::new(Seq::new(n.len(), |i: int| n[i] as int))), //TODO: replace with BigEndianNat functions
    }
}

pub proof fn lemma_to_big_ne_little<BIG, B>(n: Seq<B>)
    where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG> + PrimitiveInt + Integer,
    ensures 
        to_big_ne::<BIG, B>(n, Endian::Little) == LittleEndianNat::<B>::to_big::<BIG>(LittleEndianNat::<B>::new(Seq::new(n.len(), |i: int| n[i] as int))),
{}

// Not needed at the moment
// pub open spec fn from_big_ne<BIG, B>(n: Seq<BIG>, endianness: Endian) -> LittleEndianNat<B>
//     where
//         BIG: BasePow2 + Integer,
//         B: CompatibleSmallerBaseFor<BIG> + PrimitiveInt + Integer,
// {
//     match endianness {
//         Endian::Little => LittleEndianNat::<B>::from_big::<BIG>(LittleEndianNat::<BIG>::new(Seq::new(n.len(), |i: int| n[i] as int))),
//         Endian::Big => LittleEndianNat::<B>::from_big::<BIG>(LittleEndianNat::<BIG>::new(Seq::new(n.len(), |i: int| n[i] as int))), //TODO: replace with BigEndianNat functions
//     }
// }

/// Little endian interpretation of a sequence of numbers with a given base.
/// The first element of a sequence is the least significant position; the last
// element is the most significant position.
#[verifier::ext_equal]
pub struct LittleEndianNat<B: Base> {
    pub digits: Seq<int>,
    pub phantom: core::marker::PhantomData<B>,
}

/// Big endian interpretation of a sequence of numbers with a given base.
/// The last element of a sequence is the least significant position; the first
// element is the most significant position.
#[verifier::ext_equal]
pub struct BigEndianNat<B: Base> {
    pub digits: Seq<int>,
    pub phantom: core::marker::PhantomData<B>,
}

impl<B: Base> LittleEndianNat<B> {
    pub open spec fn in_bounds(s: Seq<int>) -> bool {
        forall|i| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < B::base()
    }

    pub open spec fn new(digits: Seq<int>) -> Self
        recommends
            Self::in_bounds(digits),
    {
        LittleEndianNat { digits, phantom: PhantomData }
    }

    pub open spec fn wf(self) -> bool {
        Self::in_bounds(self.digits)
    }

    pub open spec fn len(self) -> nat {
        self.digits.len()
    }

    pub open spec fn index(self, i: int) -> int {
        self.digits[i]
    }

    pub open spec fn first(self) -> nat {
        self.digits.first() as nat
    }

    pub proof fn first_nat(self)
        requires
            self.wf(),
            self.len() > 0,
        ensures
            self.first() as int == self.digits.first(),
    {
    }

    pub open spec fn append(self, other: Self) -> Self {
        LittleEndianNat::new(self.digits + other.digits)
    }

    pub open spec fn last(self) -> nat {
        self.digits.last() as nat
    }

    pub proof fn last_nat(self)
        requires
            self.wf(),
            self.len() > 0,
        ensures
            self.last() as int == self.digits.last(),
    {
    }

    pub proof fn index_nat(self, i: int)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            self.index(i) as int == self.digits.index(i),
    {}

    pub open spec fn skip(self, n: nat) -> Self {
        LittleEndianNat { digits: self.digits.skip(n as int), phantom: self.phantom }
    }

    pub open spec fn take(self, n: nat) -> Self {
        LittleEndianNat { digits: self.digits.take(n as int), phantom: self.phantom }
    }

    pub open spec fn drop_first(self) -> Self {
        LittleEndianNat { digits: self.digits.drop_first(), phantom: self.phantom }
    }

    pub open spec fn drop_last(self) -> Self {
        LittleEndianNat { digits: self.digits.drop_last(), phantom: self.phantom }
    }

    #[verifier::opaque]
    pub open spec fn to_nat_right(self) -> nat
        decreases self.len(),
    {
        if self.len() == 0 {
            0
        } else {
            self.drop_first().to_nat_right() * B::base() + self.first()
        }
    }

    #[verifier::opaque]
    pub open spec fn to_nat_left(self) -> nat
        decreases self.len(),
    {
        if self.len() == 0 {
            0
        } else {
            (self.drop_last().to_nat_left() + self.last() * pow(
                B::base() as int,
                (self.len() - 1) as nat,
            )) as nat
        }
    }

    pub proof fn to_nat_right_upper_bound(self)
        requires
            self.wf(),
            self.len() > 0,
        ensures
            self.to_nat_right() < pow(B::base() as int, self.len())
        decreases self.len(),
    {
        reveal(LittleEndianNat::to_nat_right);
        if self.len() == 1 {
            broadcast use lemma_pow1;
            assert(self.to_nat_right() == self.drop_first().to_nat_right() * B::base() + self.first());
        } else {
            self.drop_first().to_nat_right_upper_bound();

            calc!{
                (<)
                self.to_nat_right(); 
                (==) {}
                self.drop_first().to_nat_right() * B::base() + self.first(); 
                (<) {}
                self.drop_first().to_nat_right() * B::base() + B::base(); 
                (<=) {
                    broadcast use 
                        lemma_mul_inequality,
                        lemma_mul_is_distributive_sub_other_way;
                    // assert(self.drop_first().to_nat_right() < pow(B::base() as int, (self.len() - 1) as nat));
                    // assert(self.drop_first().to_nat_right() <= (pow(B::base() as int, (self.len() - 1) as nat) - 1) as nat);
                    // assert(self.drop_first().to_nat_right() * B::base() <= (pow(B::base() as int, (self.len() - 1) as nat) - 1) * B::base() as nat);
                    assert((pow(B::base() as int, (self.len() - 1) as nat) - 1) * B::base() as nat == (pow(B::base() as int, (self.len() - 1) as nat) * B::base() - B::base()) as nat);
                }
                (pow(B::base() as int, (self.len() - 1) as nat) * B::base() - B::base() + B::base()) as nat;
                (==) {
                    broadcast use lemma_pow1;
                }
                (pow(B::base() as int, (self.len() - 1) as nat) * pow(B::base() as int, 1)) as nat;
                (==) {
                    broadcast use lemma_pow_sub_add_cancel;
                }
                pow(B::base() as int, self.len()) as nat;
            }
        }
    }

    // TODO: How many of the triggering issues that arose with the broadcast pow properties are due to having mul_recursive and pow not opaque?
    pub proof fn nat_left_eq_nat_right(self)
        requires
            self.wf(),
        ensures
            self.to_nat_left() == self.to_nat_right(),
        decreases self.len(),
    {
        reveal(LittleEndianNat::to_nat_left);
        reveal(LittleEndianNat::to_nat_right);
        if self.len() == 0 {
        } else {
            if self.drop_last().len() == 0 {
                // This proof is similar to Dafny's in that it uses the same number of steps and hints
                // However, the first hint below isn't needed for Dafny, since Dafny
                // provides 2 fuel by default, while Verus provides 1.
                // The Dafny proof requires a reveal(pow) instead, 
                // because they hide pow, which we should probably do as well.
                calc! {
                    (==)
                    self.to_nat_left(); {
                        assert(self.drop_last().to_nat_left() == 0);
                    }
                    (self.last() * pow(B::base() as int, (self.len() - 1) as nat)) as nat; {}
                    self.last(); {}
                    self.first(); {
                        assert(self.drop_first().to_nat_right() == 0);
                        assert(0 * B::base() == 0);
                    }
                    self.to_nat_right();
                };
            } else {
                // Dafny proof steps:  8
                // Verus proof steps: 11
                // Dafny proof hints:  5 (4 are one line)
                // Verus proof hints:  9 (5 are one line)
                calc! {
                    (==)
                    self.to_nat_left() as int; {}
                    ((self.drop_last().to_nat_left() + self.last() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    )) as nat) as int; {
                        assert(self.last() >= 0);
                        assert(self.len() > 1);
                        lemma_pow_positive(B::base() as int, (self.len() - 1) as nat);
                        assert(pow(B::base() as int, (self.len() - 1) as nat) >= 0);
                    }
                    self.drop_last().to_nat_left() + self.last() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {
                        self.drop_last().nat_left_eq_nat_right();
                    }
                    self.drop_last().to_nat_right() + self.last() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {}
                    self.drop_last().drop_first().to_nat_right() * B::base()
                        + self.drop_last().first() + self.last() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {
                        self.drop_last().drop_first().nat_left_eq_nat_right();
                    }
                    self.drop_last().drop_first().to_nat_left() * B::base()
                        + self.drop_last().first() + self.last() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {
                        assert(self.drop_last().drop_first() == self.drop_first().drop_last());
                        //broadcast use group_mul_properties;
                    }
                    self.drop_first().drop_last().to_nat_left() * B::base() + self.first()
                        + self.last() * pow(B::base() as int, (self.len() - 1) as nat); {
                        assert(self.last() * pow(B::base() as int, (self.len() - 2) as nat)
                            * B::base() == self.last() * (pow(
                            B::base() as int,
                            (self.len() - 2) as nat,
                        ) * B::base())) by {
                            broadcast use crate::vstd::arithmetic::mul::lemma_mul_is_associative;

                        }
                        assert(pow(B::base() as int, (self.len() - 1) as nat) == pow(
                            B::base() as int,
                            (self.len() - 2) as nat,
                        ) * B::base()) by {
                            assert(B::base() == pow(B::base() as int, 1)) by {
                                lemma_pow1(B::base() as int);
                            }
                            lemma_pow_adds(B::base() as int, (self.len() - 2) as nat, 1);
                        }
                    }
                    self.drop_first().drop_last().to_nat_left() * B::base() + (self.last() * pow(
                        B::base() as int,
                        (self.len() - 2) as nat,
                    )) * B::base() + self.first(); {
                        lemma_mul_is_distributive_add_other_way(
                            B::base() as int,
                            self.drop_first().drop_last().to_nat_left() as int,
                            self.last() * pow(B::base() as int, (self.len() - 2) as nat),
                        );
                    }
                    (self.drop_first().drop_last().to_nat_left() + self.last() * pow(
                        B::base() as int,
                        (self.len() - 2) as nat,
                    )) * B::base() + self.first(); {
                        assert((self.drop_first().drop_last().to_nat_left() + self.last() * pow(
                            B::base() as int,
                            (self.len() - 2) as nat,
                        )) == self.drop_first().to_nat_left()) by {
                            lemma_pow_positive(B::base() as int, (self.len() - 2) as nat);
                        };
                    }
                    (self.drop_first().to_nat_left() * B::base() + self.first()) as int; {
                        self.drop_first().nat_left_eq_nat_right();
                    }
                    self.to_nat_right() as int;
                }
            }
        }
    }

    /// Converts a nat to a sequence
    pub uninterp spec fn from_nat(n: nat) -> Self;

    /// Converts a nat to a sequence of a specified length
    pub uninterp spec fn from_nat_with_len(n: nat, len: nat) -> Self
        recommends pow(B::base() as int, len) > n;

    proof fn from_nat_with_len_ensures(n: nat, len: nat)
        requires 
            pow(B::base() as int, len) > n,
        ensures 
            Self::from_nat_with_len(n, len).len() == len,
            Self::from_nat_with_len(n, len).to_nat_right() == n,
    {
        assume(false);
    }

    proof fn lemma_from_nat_injective(n: nat)
        ensures
            Self::from_nat(n).to_nat_right() == n,
    {
        assume(false);
    }

    // /////////////////////////////////////////////////// //
    //         Conversion Routines                         //
    // /////////////////////////////////////////////////// //

    /// SMALL::base() to the power of exp() is BIG::base()
    // CHANGED: made the spec open instead of closed
    pub open spec fn exp<BIG>() -> nat 
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>
    {
        BIG::bits() / B::bits()
    }

    proof fn exp_ensures<BIG>()
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>
        ensures
            pow(B::base() as int, Self::exp()) == BIG::base(),
            Self::exp() > 0,
    {
        broadcast use crate::vstd::arithmetic::div_mod::group_div_basics;

        assert(forall|x| x != 0 ==> #[trigger] (0int / x) == 0);
        broadcast use crate::vstd::arithmetic::power::lemma_pow_multiplies;

        B::bits_to_base();

        calc! {
            (==)
            BIG::bits(); {
                crate::vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    BIG::bits() as int,
                    B::bits() as int,
                );
            }
            B::bits() * (BIG::bits() / B::bits()) + (BIG::bits() % B::bits()); {
                B::compatible();
            }
            B::bits() * (BIG::bits() / B::bits()); {}
            B::bits() * Self::exp();
        }
        calc! {
            (==)
            pow(B::base() as int, Self::exp()); {
                crate::vstd::arithmetic::power::lemma_pow_multiplies(2, B::bits(), Self::exp());
                crate::vstd::arithmetic::power2::lemma_pow2(B::bits());
            }
            pow(2, B::bits() * Self::exp()) as int; {}
            pow(2, BIG::bits()) as int; {
                crate::vstd::arithmetic::power2::lemma_pow2(BIG::bits());
            }
            pow2(BIG::bits()) as int; {
                BIG::bits_to_base();
            }
            BIG::base() as int;
        }

        B::compatible();
        assert((BIG::bits() / B::bits()) != 0);
        BIG::bits_to_base();

    }    

    pub open spec fn from_big<BIG>(n: LittleEndianNat<BIG>) -> Self
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>
        decreases n.len(),
    {
        if n.len() == 0 {
            LittleEndianNat::new(Seq::empty())
        } else {
            LittleEndianNat::from_nat_with_len(n.first(), Self::exp()).append(Self::from_big(n.drop_first()))
        }
    }

    #[verifier::opaque]
    pub open spec fn to_big<BIG>(n: LittleEndianNat<B>) -> LittleEndianNat<BIG>
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        recommends n.len() % Self::exp() == 0,
        decreases n.len(),
        when n.len() % Self::exp() == 0
        via Self::to_big_decreases
    {
        if n.len() == 0 {
            LittleEndianNat::new(Seq::empty())
        } else {
            LittleEndianNat::new(seq![n.take(Self::exp()).to_nat_right() as int]).append(Self::to_big(n.skip(Self::exp())))
        }
    }

    #[via_fn]
    proof fn to_big_decreases<BIG>(n: LittleEndianNat<B>) 
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
    {
        Self::exp_ensures();
        if n.len() != 0 {
            assert(0 <= Self::exp());
            assert(Self::exp() < n.len()) by {
                broadcast use crate::vstd::arithmetic::div_mod::lemma_mod_is_zero;
            }
            assert(n.skip(Self::exp()).len() < n.len());
        }
    }

    /// Converting from a BIG base to a SMALL base does not change the fundamental value
    pub proof fn to_small_ensures<BIG>(n: LittleEndianNat<BIG>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        ensures
            Self::from_big(n).len() == n.len() * Self::exp(),
            Self::from_big(n).to_nat_right() == n.to_nat_right(),
    {
        assume(false);
    }

    /// Converting from a SMALL base to a BIG base does not change the fundamental value
    pub proof fn to_big_ensures<BIG>(n: LittleEndianNat<B>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        requires
            n.len() % Self::exp() == 0,
        ensures
            Self::to_big(n).len() == n.len() / Self::exp(),
            Self::to_big(n).to_nat_right() == n.to_nat_right(),
    {
        assume(false);
    }

    // to_small is injective
    pub proof fn to_small_injective<BIG>(x: LittleEndianNat<BIG>, y: LittleEndianNat<BIG>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        requires
            Self::from_big(x) == Self::from_big(y),
            x.len() == y.len(),
        ensures
            x == y,
    {
        assume(false);
    }

    // to_big is injective
    pub proof fn to_big_injective<BIG>(x: LittleEndianNat<B>, y: LittleEndianNat<B>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        requires
            x.len() % Self::exp() == 0,
            y.len() % Self::exp() == 0,
            Self::to_big(x) == Self::to_big(y),
            x.len() == y.len(),
        ensures
            x == y,
    {
        assume(false);
    }

    pub proof fn to_big_cycle<BIG>(x: LittleEndianNat<B>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        requires
            x.len() % Self::exp() == 0,
        ensures
            Self::from_big(Self::to_big(x)) == x,
    {
        assume(false);
    }

    pub proof fn from_big_cycle<BIG>(x: LittleEndianNat<BIG>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        ensures
            Self::to_big(Self::from_big(x)) == x,
    {
        assume(false);
    }

    // TODO: Generalize this to: Self::to_big(x).index(i) == x.skip(i * Self.exp()).take(Self::exp()).to_nat_right() as int,
    pub proof fn to_big_initial<BIG>(x: LittleEndianNat<B>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        requires
            x.len() % Self::exp() == 0,
            x.len() > 0,
        ensures
            Self::to_big(x).index(0) == x.take(Self::exp()).to_nat_right() as int,
    {
        reveal(LittleEndianNat::to_big);
        assert(x.skip(Self::exp()).len() % Self::exp() == 0) by {
            assert(Self::exp() <= x.len()) by {
                Self::exp_ensures();
                crate::vstd::arithmetic::div_mod::lemma_mod_is_zero(x.len(), Self::exp());
            };
            assert(x.skip(Self::exp()).len() == x.len() - Self::exp());
            broadcast use crate::vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish;
        }
        assert(Self::to_big(x) == LittleEndianNat::new(seq![x.take(Self::exp()).to_nat_right() as int]).append(Self::to_big(x.skip(Self::exp()))));
    }

}

impl Base for u8 {
    open spec fn base() -> nat {
        u8::MAX as nat + 1
    }

    proof fn base_min() {
    }
}

impl Base for u64 {
    open spec fn base() -> nat {
        u64::MAX as nat + 1
    }

    proof fn base_min() {
    }
}

impl Base for usize {
    open spec fn base() -> nat {
        usize::MAX as nat + 1
    }

    proof fn base_min() {
    }
}

impl BasePow2 for u8 {
    open spec fn bits() -> nat {
        8
    }

    proof fn bits_to_base() {
        crate::vstd::arithmetic::power2::lemma2_to64();
    }
}

impl BasePow2 for u64 {
    open spec fn bits() -> nat {
        64
    }

    proof fn bits_to_base() {
        crate::vstd::arithmetic::power2::lemma2_to64();
    }
}

impl BasePow2 for usize {
    open spec fn bits() -> nat {
        usize::BITS as nat
    }

    proof fn bits_to_base() {
        crate::vstd::arithmetic::power2::lemma2_to64();
    }
}

impl CompatibleSmallerBaseFor<u64> for u8 {
    proof fn compatible() {
    }
}

impl CompatibleSmallerBaseFor<usize> for u8 {
    proof fn compatible() {
    }
}

proof fn test(x: LittleEndianNat<u64>, y: LittleEndianNat<u8>) 
    requires y.len() % 8 == 0,
{
    let x8 = LittleEndianNat::<u8>::from_big(x);
    let x8_64 = LittleEndianNat::<u8>::to_big::<u64>(x8);
    assert(x == x8_64) by {
        LittleEndianNat::<u8>::from_big_cycle(x);
    };

    let y_64 = LittleEndianNat::<u8>::to_big::<u64>(y);
    if y.len() > 0 {
        assert(y_64.index(0) == y.take(8).to_nat_right() as int) by {
            LittleEndianNat::<u8>::to_big_initial::<u64>(y);
        };
    }
}

pub proof fn lemma_to_nat_right_bitwise_and(x: LittleEndianNat<u8>, y: LittleEndianNat<u8>)
    requires
        x.to_nat_right() as usize & y.to_nat_right() as usize == 0,
        x.len() == y.len() <= size_of::<usize>(),
        x.wf(),
        y.wf(),
    ensures
        forall |i| 0 <= i < x.len() ==> #[trigger] x.index(i) as u8 & y.index(i) as u8 == 0,
    decreases x.len(),
{
    if x.len() == 0 {}
    else if x.len() == 1 {
        reveal(LittleEndianNat::to_nat_right);
        assert(x.drop_first().to_nat_right() == 0);
        assert(y.drop_first().to_nat_right() == 0);
    } else {
        reveal(LittleEndianNat::to_nat_right);
        // assert(((x.drop_first().to_nat_right() * u8::base() + x.first()) as usize) & ((y.drop_first().to_nat_right() * u8::base() + y.first()) as usize) == 0);
        // assert(u8::base() == 256);
        let x_rest = x.drop_first().to_nat_right() as usize;
        let y_rest = y.drop_first().to_nat_right() as usize;
        let x_first = x.first() as u8;
        let y_first = y.first() as u8;

        // assert(x.first() < 256);
        // assert(x.first() == x.first() as u8);

        // assert(x.to_nat_right() < x.len() * 256 <= usize::MAX) by {x.to_nat_right_upper_bound()};
        // assert(y.to_nat_right() < y.len() * 256 <= usize::MAX) by {y.to_nat_right_upper_bound()};

        // To compute pow(256, x.drop_first().len()), which is the upper bound on x.drop_first().to_nat_right(), 
        // at most we need to unfold pow size_of::<usize>() times, since x.drop_first().len() < size_of::<usize>().
        // Since size_of::<usize>() <= 8, we reveal with fuel 8.
        reveal_with_fuel(pow, 8);
        assert(x.drop_first().to_nat_right() < (usize::MAX + 1)/256) by {x.drop_first().to_nat_right_upper_bound()};
        assert(y.drop_first().to_nat_right() < (usize::MAX + 1)/256) by {y.drop_first().to_nat_right_upper_bound()};
        // assert(x.drop_first().to_nat_right() * 256 == x.drop_first().to_nat_right() * 256 as usize);
        // assert(y.drop_first().to_nat_right() * 256 == y.drop_first().to_nat_right() * 256 as usize);

        // assert((x_rest * 256 + x_first) as usize & (y_rest * 256 + y_first) as usize == 0);
        assert((x_rest * 256 + x_first) as usize & (y_rest * 256 + y_first) as usize == 0 ==> x_first & y_first == 0) by (bit_vector);
        assert((x_rest * 256 + x_first) as usize & (y_rest * 256 + y_first) as usize == 0 ==> (x_rest * 256) as usize & (y_rest * 256) as usize == 0) by (bit_vector);
        assume((x_rest * 256) as usize & (y_rest * 256) as usize == 0 ==> x_rest & y_rest == 0) 
        // by (bit_vector)
        //     requires 
        //         (x_rest < 0x10000000000000000int/256 && y_rest < 0x10000000000000000int/256)
        //         || 
        //         (x_rest < 0x100000000int/256 && y_rest < 0x100000000int/256),
            ;
            // TODO: how to consider both cases with bit_vector?

        lemma_to_nat_right_bitwise_and(x.drop_first(), y.drop_first());
        // assert(forall |i| 0 <= i < x.drop_first().len() ==> #[trigger] x.drop_first().index(i) as u8 & y.drop_first().index(i) as u8 == 0);
        // assert(x.first() as u8 & y.first() as u8 == 0);
        assert(forall |i: int| 1 <= i < x.len() ==> x.drop_first().index(i-1) == x.index(i));
        assert(forall |i: int| 1 <= i < y.len() ==> y.drop_first().index(i-1) == y.index(i));
    }
}

} // verus!

