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

/***** Traits *****/

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

/***** Endian *****/

pub enum Endian {
    Little, 
    Big,
}

pub uninterp spec fn endianness() -> Endian;

/***** EndianNat *****/

/// Provides either little endian or big endian interpretation of a sequence of numbers with a given base.
/// With little endian, the first element of a sequence is the least significant position; the last
// element is the most significant position.
/// With big endian, the last element of a sequence is the least significant position; the first
// element is the most significant position.

#[verifier::ext_equal]
pub struct EndianNat<B: Base> {
    pub endian: Endian,
    pub digits: Seq<int>,
    pub phantom: core::marker::PhantomData<B>,
}

impl<B: Base> EndianNat<B> {
    pub open spec fn in_bounds(s: Seq<int>) -> bool {
        forall|i| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < B::base()
    }

    pub open spec fn new(endian: Endian, digits: Seq<int>) -> Self
        recommends
            Self::in_bounds(digits),
    {
        EndianNat { endian, digits, phantom: PhantomData }
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

    pub proof fn index_nat(self, i: int)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            self.index(i) as int == self.digits.index(i),
    {}

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

    pub open spec fn append(self, other: Self) -> Self 
        recommends 
            self.endian == other.endian,
    {
        EndianNat::new(self.endian, self.digits + other.digits)
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

    pub open spec fn least(self) -> nat {
        match self.endian {
            Endian::Little => self.first(),
            Endian::Big => self.last(),
        }
    }

    pub open spec fn most(self) -> nat {
        match self.endian {
            Endian::Little => self.last(),
            Endian::Big => self.first(),
        }
    }

    pub open spec fn skip(self, n: nat) -> Self {
        EndianNat { endian: self.endian, digits: self.digits.skip(n as int), phantom: self.phantom }
    }

    pub open spec fn take(self, n: nat) -> Self {
        EndianNat { endian: self.endian, digits: self.digits.take(n as int), phantom: self.phantom }
    }

    pub open spec fn drop_first(self) -> Self {
        EndianNat { endian: self.endian, digits: self.digits.drop_first(), phantom: self.phantom }
    }

    pub open spec fn drop_last(self) -> Self {
        EndianNat { endian: self.endian, digits: self.digits.drop_last(), phantom: self.phantom }
    }

    pub open spec fn drop_least(self) -> Self {
        match self.endian {
            Endian::Little => self.drop_first(),
            Endian::Big => self.drop_last(),
        }
    }

    pub open spec fn drop_most(self) -> Self {
        match self.endian {
            Endian::Little => self.drop_last(),
            Endian::Big => self.drop_first(),
        }
    }

    #[verifier::opaque]
    pub open spec fn to_nat_right(self) -> nat
        decreases self.len(),
    {
        if self.len() == 0 {
            0
        } else {
            match self.endian {
                Endian::Little => self.drop_first().to_nat_right() * B::base() + self.first(),
                Endian::Big => {
                    (self.drop_first().to_nat_right() + self.first() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    )) as nat
                }
            }
        }
    }

    #[verifier::opaque]
    pub open spec fn to_nat_left(self) -> nat
        decreases self.len(),
    {
        if self.len() == 0 {
            0
        } else {
            match self.endian {
                Endian::Little => {
                    (self.drop_last().to_nat_left() + self.last() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    )) as nat
                }
                Endian::Big => self.drop_last().to_nat_left() * B::base() + self.last()
            }
        }
    }

    // Provides default version of to_nat() which hides details of the endianness
    #[verifier::opaque]
    pub open spec fn to_nat(self) -> nat
        decreases self.len()
    {
        if self.len() == 0 {
            0
        } else { 
            self.drop_least().to_nat() * B::base() + self.least()
        }
    }

    pub proof fn to_nat_upper_bound(self)
        requires
            self.wf(),
        ensures
            self.to_nat() < pow(B::base() as int, self.len())
        decreases self.len(),
    {
        reveal(EndianNat::to_nat);
        reveal(pow);
        if self.len() == 0 {
        } else {
            self.drop_least().to_nat_upper_bound();

            calc!{
                (<)
                self.to_nat(); 
                (==) {}
                self.drop_least().to_nat() * B::base() + self.least(); 
                (<) {}
                self.drop_least().to_nat() * B::base() + B::base(); 
                (<=) {
                    broadcast use 
                        lemma_mul_inequality,
                        lemma_mul_is_distributive_sub_other_way;
                    // assert(self.drop_least().to_nat() < pow(B::base() as int, (self.len() - 1) as nat));
                    // assert(self.drop_least().to_nat() <= (pow(B::base() as int, (self.len() - 1) as nat) - 1) as nat);
                    // assert(self.drop_least().to_nat() * B::base() <= (pow(B::base() as int, (self.len() - 1) as nat) - 1) * B::base() as nat);
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

    pub proof fn nat_left_nat_right_to_nat_eq(self)
        requires 
            self.wf(),
        ensures
            self.to_nat() == self.to_nat_right() == self.to_nat_left(),
    {
        self.to_nat_eq();
        match self.endian {
            Endian::Little => self.nat_left_eq_nat_right_little(),
            Endian::Big => self.nat_left_eq_nat_right_big(),
        }
    }

    pub proof fn to_nat_eq(self)
        requires
            self.wf(),
        ensures
            self.endian == Endian::Little ==> self.to_nat() == self.to_nat_right(),
            self.endian == Endian::Big ==> self.to_nat() == self.to_nat_left(),
        decreases self.len(),
    {
        reveal(EndianNat::to_nat_right);
        reveal(EndianNat::to_nat_left);
        reveal(EndianNat::to_nat);

        if self.len() == 0 {
        } else {
            self.drop_least().to_nat_eq();
        }
    }

    // TODO: How many of the triggering issues that arose with the broadcast pow properties are due to having mul_recursive and pow not opaque?
    #[verifier::spinoff_prover]
    pub proof fn nat_left_eq_nat_right_little(self)
        requires
            self.wf(),
            self.endian == Endian::Little,
        ensures
            self.to_nat_left() == self.to_nat_right(),
        decreases self.len(),
    {
        reveal(EndianNat::to_nat_left);
        reveal(EndianNat::to_nat_right);
        reveal(pow);
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
                        self.drop_last().nat_left_eq_nat_right_little();
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
                        self.drop_last().drop_first().nat_left_eq_nat_right_little();
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
                        self.drop_first().nat_left_eq_nat_right_little();
                    }
                    self.to_nat_right() as int;
                }
            }
        }
    }

    // TODO: How many of the triggering issues that arose with the broadcast pow properties are due to having mul_recursive and pow not opaque?
    pub proof fn nat_left_eq_nat_right_big(self)
        requires
            self.wf(),
            self.endian == Endian::Big,
        ensures
            self.to_nat_left() == self.to_nat_right(),
        decreases self.len(),
    {
        reveal(EndianNat::to_nat_left);
        reveal(EndianNat::to_nat_right);
        reveal(pow);
        if self.len() == 0 {
        } else {
            if self.drop_first().len() == 0 {
                // This proof is similar to Dafny's in that it uses the same number of steps and hints
                // However, the first hint below isn't needed for Dafny, since Dafny
                // provides 2 fuel by default, while Verus provides 1.
                // The Dafny proof requires a reveal(pow) instead, 
                // because they hide pow, which we should probably do as well.
                calc! {
                    (==)
                    self.to_nat_right(); {
                        assert(self.drop_first().to_nat_right() == 0);
                    }
                    (self.first() * pow(B::base() as int, (self.len() - 1) as nat)) as nat; {}
                    self.first(); {}
                    self.last(); {
                        assert(self.drop_last().to_nat_left() == 0);
                        assert(0 * B::base() == 0);
                    }
                    self.to_nat_left();
                };
            } else {
                // Dafny proof steps:  8
                // Verus proof steps: 11
                // Dafny proof hints:  5 (4 are one line)
                // Verus proof hints:  9 (5 are one line)
                calc! {
                    (==)
                    self.to_nat_right() as int; {}
                    ((self.drop_first().to_nat_right() + self.first() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    )) as nat) as int; {
                        assert(self.first() >= 0);
                        assert(self.len() > 1);
                        lemma_pow_positive(B::base() as int, (self.len() - 1) as nat);
                        assert(pow(B::base() as int, (self.len() - 1) as nat) >= 0);
                    }
                    self.drop_first().to_nat_right() + self.first() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {
                        self.drop_first().nat_left_eq_nat_right_big();
                    }
                    self.drop_first().to_nat_left() + self.first() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {}
                    self.drop_first().drop_last().to_nat_left() * B::base()
                        + self.drop_first().last() + self.first() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {
                        self.drop_first().drop_last().nat_left_eq_nat_right_big();
                    }
                    self.drop_first().drop_last().to_nat_right() * B::base()
                        + self.drop_first().last() + self.first() * pow(
                        B::base() as int,
                        (self.len() - 1) as nat,
                    ); {
                        assert(self.drop_first().drop_last() == self.drop_last().drop_first());
                        //broadcast use group_mul_properties;
                    }
                    self.drop_last().drop_first().to_nat_right() * B::base() + self.last()
                        + self.first() * pow(B::base() as int, (self.len() - 1) as nat); {
                        assert(self.first() * pow(B::base() as int, (self.len() - 2) as nat)
                            * B::base() == self.first() * (pow(
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
                    self.drop_last().drop_first().to_nat_right() * B::base() + (self.first() * pow(
                        B::base() as int,
                        (self.len() - 2) as nat,
                    )) * B::base() + self.last(); {
                        lemma_mul_is_distributive_add_other_way(
                            B::base() as int,
                            self.drop_last().drop_first().to_nat_right() as int,
                            self.first() * pow(B::base() as int, (self.len() - 2) as nat),
                        );
                    }
                    (self.drop_last().drop_first().to_nat_right() + self.first() * pow(
                        B::base() as int,
                        (self.len() - 2) as nat,
                    )) * B::base() + self.last(); {
                        assert((self.drop_last().drop_first().to_nat_right() + self.first() * pow(
                            B::base() as int,
                            (self.len() - 2) as nat,
                        )) == self.drop_last().to_nat_right()) by {
                            lemma_pow_positive(B::base() as int, (self.len() - 2) as nat);
                        };
                    }
                    (self.drop_last().to_nat_right() * B::base() + self.last()) as int; {
                        self.drop_last().nat_left_eq_nat_right_big();
                    }
                    self.to_nat_left() as int;
                }
            }
        }
    }

    /// Converts a nat to a sequence
    pub uninterp spec fn from_nat(n: nat) -> Self;

    /// Converts a nat to a sequence of a specified length
    pub uninterp spec fn from_nat_with_len(n: nat, len: nat) -> Self
        recommends pow(B::base() as int, len) > n;

    // proof fn from_nat_with_len_ensures(n: nat, len: nat)
    //     requires 
    //         pow(B::base() as int, len) > n,
    //     ensures 
    //         Self::from_nat_with_len(n, len).len() == len,
    //         Self::from_nat_with_len(n, len).to_nat() == n,
    // {
    //     assume(false);
    // }

    // proof fn lemma_from_nat_injective(n: nat)
    //     ensures
    //         Self::from_nat(n).to_nat() == n,
    // {
    //     assume(false);
    // }  

    // /////////////////////////////////////////////////// //
    //         Conversion Routines                         //
    // /////////////////////////////////////////////////// //

    /// SMALL::base() to the power of exp() is BIG::base()
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

    pub open spec fn from_big<BIG>(n: EndianNat<BIG>) -> Self
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>
        decreases n.len(),
    {
        if n.len() == 0 {
            EndianNat::new(n.endian, Seq::empty())
        } else {
            EndianNat::from_nat_with_len(n.first(), Self::exp()).append(Self::from_big(n.drop_first()))
        }
    }

    #[verifier::opaque]
    pub open spec fn to_big<BIG>(n: EndianNat<B>) -> EndianNat<BIG>
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        recommends n.len() % Self::exp() == 0,
        decreases n.len(),
        when n.len() % Self::exp() == 0
        via Self::to_big_decreases
    {
        if n.len() == 0 {
            EndianNat::new(n.endian, Seq::empty())
        } else {
            EndianNat::new(n.endian, seq![n.take(Self::exp()).to_nat() as int]).append(Self::to_big(n.skip(Self::exp())))
        }
    }

    #[via_fn]
    proof fn to_big_decreases<BIG>(n: EndianNat<B>) 
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
    {
        Self::exp_ensures();
        if n.len() != 0 {
            assert(Self::exp() <= n.len()) by {
                broadcast use crate::vstd::arithmetic::div_mod::lemma_mod_is_zero;
            }
            assert(n.skip(Self::exp()).len() < n.len());
        }
    }

    // /// Converting from a BIG base to a SMALL base does not change the fundamental value
    // pub proof fn to_small_ensures<BIG>(n: EndianNat<BIG>)
    //     where
    //         BIG: BasePow2,
    //         B: CompatibleSmallerBaseFor<BIG>,
    //     ensures
    //         Self::from_big(n).len() == n.len() * Self::exp(),
    //         Self::from_big(n).to_nat() == n.to_nat(),
    // {
    //     assume(false);
    // }

    // /// Converting from a SMALL base to a BIG base does not change the fundamental value
    // pub proof fn to_big_ensures<BIG>(n: EndianNat<B>)
    //     where
    //         BIG: BasePow2,
    //         B: CompatibleSmallerBaseFor<BIG>,
    //     requires
    //         n.len() % Self::exp() == 0,
    //     ensures
    //         Self::to_big(n).len() == n.len() / Self::exp(),
    //         Self::to_big(n).to_nat() == n.to_nat(),
    // {
    //     assume(false);
    // }

    // // to_small is injective
    // pub proof fn to_small_injective<BIG>(x: EndianNat<BIG>, y: EndianNat<BIG>)
    //     where
    //         BIG: BasePow2,
    //         B: CompatibleSmallerBaseFor<BIG>,
    //     requires
    //         Self::from_big(x) == Self::from_big(y),
    //         x.len() == y.len(),
    //         x.endian == y.endian,
    //     ensures
    //         x == y,
    // {
    //     assume(false);
    // }

    // // to_big is injective
    // pub proof fn to_big_injective<BIG>(x: EndianNat<B>, y: EndianNat<B>)
    //     where
    //         BIG: BasePow2,
    //         B: CompatibleSmallerBaseFor<BIG>,
    //     requires
    //         x.len() % Self::exp() == 0,
    //         y.len() % Self::exp() == 0,
    //         Self::to_big(x) == Self::to_big(y),
    //         x.len() == y.len(),
    //         x.endian == y.endian,
    //     ensures
    //         x == y,
    // {
    //     assume(false);
    // }

    // pub proof fn to_big_cycle<BIG>(x: EndianNat<B>)
    //     where
    //         BIG: BasePow2,
    //         B: CompatibleSmallerBaseFor<BIG>,
    //     requires
    //         x.len() % Self::exp() == 0,
    //     ensures
    //         Self::from_big(Self::to_big(x)) == x,
    // {
    //     assume(false);
    // }

    // pub proof fn from_big_cycle<BIG>(x: EndianNat<BIG>)
    //     where
    //         BIG: BasePow2,
    //         B: CompatibleSmallerBaseFor<BIG>,
    //     ensures
    //         Self::to_big(Self::from_big(x)) == x,
    // {
    //     assume(false);
    // }

    // TODO: Generalize this to: Self::to_big(x).index(i) == x.skip(i * Self.exp()).take(Self::exp()).to_nat_right() as int,
    pub proof fn to_big_initial<BIG>(x: EndianNat<B>)
        where
            BIG: BasePow2,
            B: CompatibleSmallerBaseFor<BIG>,
        requires
            x.len() % Self::exp() == 0,
            x.len() > 0,
        ensures
            Self::to_big(x).index(0) == x.take(Self::exp()).to_nat() as int,
    {
        reveal(EndianNat::to_big);
        assert(x.skip(Self::exp()).len() % Self::exp() == 0) by {
            assert(Self::exp() <= x.len()) by {
                Self::exp_ensures();
                crate::vstd::arithmetic::div_mod::lemma_mod_is_zero(x.len(), Self::exp());
            };
            assert(x.skip(Self::exp()).len() == x.len() - Self::exp());
            broadcast use crate::vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish;
        }
        assert(Self::to_big(x) == EndianNat::new(x.endian, seq![x.take(Self::exp()).to_nat() as int]).append(Self::to_big(x.skip(Self::exp()))));
    }

}

/***** Functions involving both little and big endian *****/

pub open spec fn to_seq_int<B>(n: Seq<B>) -> Seq<int>
    where 
        B: PrimitiveInt + Integer,
{
    Seq::new(n.len(), |i: int| n[i] as int)
}

// TODO: something relating PrimitiveInt to Integer, so that if it's a primitive int, then casting is fine
pub open spec fn to_big_ne<BIG, B>(n: Seq<B>) -> EndianNat<BIG>
    where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG> + PrimitiveInt + Integer,
{
    EndianNat::<B>::to_big::<BIG>(EndianNat::<B>::new(endianness(), to_seq_int(n)))
}

pub proof fn lemma_little_right_eq_big_left_const<B>(n: Seq<int>, x: int)
    where 
        B: Base,
    requires
        forall |i| 0 <= i < n.len() ==> n[i] == x,
    ensures
        EndianNat::<B>::new(Endian::Little, n).to_nat() == EndianNat::<B>::new(Endian::Big, n).to_nat(),
    decreases n.len()
{
    reveal(EndianNat::to_nat);

    if n.len() == 0 {}
    else {
        lemma_little_right_eq_big_left_const::<B>(n.drop_first(), x);
        lemma_little_right_eq_big_left_const::<B>(n.drop_last(), x);

        assert(n.drop_first() == n.drop_last());
    }
}

/***** Implementations and proofs for specific types *****/

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

// proof fn test(x: EndianNat<u64>, y: EndianNat<u8>) 
//     requires y.len() % 8 == 0,
// {
//     let x8 = EndianNat::<u8>::from_big(x);
//     let x8_64 = EndianNat::<u8>::to_big::<u64>(x8);
//     assert(x == x8_64) by {
//         EndianNat::<u8>::from_big_cycle(x);
//     };

//     let y_64 = EndianNat::<u8>::to_big::<u64>(y);
//     if y.len() > 0 {
//         assert(y_64.index(0) == y.take(8).to_nat() as int) by {
//             EndianNat::<u8>::to_big_initial::<u64>(y);
//         };
//     }
// }

pub proof fn lemma_to_nat_bitwise_and(x: EndianNat<u8>, y: EndianNat<u8>)
    requires
        x.to_nat() as usize & y.to_nat() as usize == 0,
        x.len() == y.len() <= size_of::<usize>(),
        x.wf(),
        y.wf(),
        x.endian == y.endian,
    ensures
        forall |i| 0 <= i < x.len() ==> #[trigger] x.index(i) as u8 & y.index(i) as u8 == 0,
    decreases x.len(),
{
    reveal(EndianNat::to_nat);

    if x.len() == 0 {}
    else if x.len() == 1 {
        reveal_with_fuel(EndianNat::to_nat, 2);
    }
    else {
        let x_rest = x.drop_least().to_nat() as usize;
        let y_rest = y.drop_least().to_nat() as usize;
        let x_least = x.least() as u8;
        let y_least = y.least() as u8;

        // To compute pow(256, x.drop_least().len()), which is the upper bound on x.drop_least().to_nat(), 
        // at most we need to unfold pow size_of::<usize>() times, since x.drop_least().len() < size_of::<usize>().
        // Since size_of::<usize>() <= 8, we reveal with fuel 8.
        reveal_with_fuel(pow, 8);
        assert(x.drop_least().to_nat() * 256 <= usize::MAX) by {x.drop_least().to_nat_upper_bound()};
        assert(y.drop_least().to_nat() * 256 <= usize::MAX) by {y.drop_least().to_nat_upper_bound()};

        assert((x_rest * 256 + x_least) as usize & (y_rest * 256 + y_least) as usize == 0 ==> x_least & y_least == 0) by (bit_vector);
        assert((x_rest * 256 + x_least) as usize & (y_rest * 256 + y_least) as usize == 0 ==> (x_rest * 256) as usize & (y_rest * 256) as usize == 0) by (bit_vector);

        let x_rest_times = (x_rest * 256) as usize;
        let y_rest_times = (y_rest * 256) as usize;
        
        assert(x_rest_times & y_rest_times == 0 ==> x_rest & y_rest == 0) 
            by (bit_vector)
            requires 
                x_rest_times == x_rest * 256,
                y_rest_times == y_rest * 256,
            ;

        lemma_to_nat_bitwise_and(x.drop_least(), y.drop_least());

        assert(forall |i: int| 1 <= i < x.len() ==> x.drop_first().index(i-1) == x.index(i));
        assert(forall |i: int| 1 <= i < y.len() ==> y.drop_first().index(i-1) == y.index(i));
        assert(forall |i: int| 0 <= i < x.len() - 1 ==> x.drop_last().index(i) == #[trigger] x.index(i));
        assert(forall |i: int| 0 <= i < y.len() - 1 ==> y.drop_last().index(i) == #[trigger] y.index(i));
    }
}

} // verus!

