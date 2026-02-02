/*!
Reasoning about representations of non-negative numbers with endianness, including conversion between bases.
*/
use crate::vstd::arithmetic::mul::*;
use crate::vstd::arithmetic::power::*;
use crate::vstd::arithmetic::power2::*;
use crate::vstd::calc_macro::*;
use crate::vstd::group_vstd_default;
use crate::vstd::layout;
use crate::vstd::prelude::*;
use core::marker::PhantomData;

verus! {

broadcast use group_vstd_default;

/// Represents a base with value [`Self::base()`].
pub trait Base {
    spec fn base() -> nat;

    proof fn base_min()
        ensures
            Self::base() > 1,
    ;
}

/// The exclusive upper bound on values that can be stored with `len` digits in base [`B::base()`].
///
/// [`B::base()`]: Base::base
pub open spec fn base_upper_bound_excl<B: Base>(len: nat) -> int {
    pow(B::base() as int, len)
}

/// Represents a base which is a power of 2 specified by [`Self::bits()`].
pub trait BasePow2: Base {
    spec fn bits() -> nat;

    proof fn bits_to_base()
        ensures
            Self::bits() > 1,
            Self::base() == pow2(Self::bits()),
    ;
}

/// Represents a base for which each digit of `BIG` converts to multiple digits in this base.
pub trait CompatibleSmallerBaseFor<BIG: BasePow2>: BasePow2 {
    proof fn compatible()
        ensures
            BIG::bits() > Self::bits() && BIG::bits() % Self::bits() == 0,
    ;
}

/// Represents little-endian or big-endian interpretation.
pub enum Endian {
    Little,
    Big,
}

/// Abstracts the endianness of the currently executing hardware.
/// Use this when you want to use the same endianness everywhere, but don't wish to specify which endianness is used.
pub uninterp spec fn endianness() -> Endian;

/// Provides either little-endian or big-endian interpretation of a sequence of numbers with a given base. This interpretation may have any number of leading zeros.
/// With little-endian, the first digit is the least significant position; the last digit is the most significant position.
/// With big-endian, the last digit of a sequence is the least significant position; the first digit is the most significant position.
#[verifier::ext_equal]
pub struct EndianNat<B: Base> {
    pub endian: Endian,
    pub digits: Seq<int>,
    pub phantom: core::marker::PhantomData<B>,
}

impl<B: Base> EndianNat<B> {
    /// True when all numbers in `s` are valid digits in the given base.
    pub open spec fn in_bounds(s: Seq<int>) -> bool {
        forall|i| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < B::base()
    }

    /// True when all of `self.digits` are valid digits in the given base.
    pub open spec fn wf(self) -> bool {
        Self::in_bounds(self.digits)
    }

    /// Creates a new `EndianNat` with the given digits and endianness.
    pub open spec fn new(endian: Endian, digits: Seq<int>) -> Self
        recommends
            Self::in_bounds(digits),
    {
        EndianNat { endian, digits, phantom: PhantomData }
    }

    /// Creates a new `EndianNat` with the given digits and the default endianness ([`endianness()`]).
    pub open spec fn new_default(digits: Seq<int>) -> Self
        recommends
            Self::in_bounds(digits),
    {
        EndianNat { endian: endianness(), digits, phantom: PhantomData }
    }

    /// Number of digits in this `EndianNat`.
    pub open spec fn len(self) -> nat {
        self.digits.len()
    }

    /// The `i`th digit in this `EndianNat`.
    pub open spec fn index(self, i: int) -> int
        recommends
            0 <= i < self.digits.len(),
    {
        self.digits[i]
    }

    /// The first digit in this `EndianNat`. Ignores endianness.
    pub open spec fn first(self) -> nat
        recommends
            self.digits.len() > 0,
    {
        self.digits.first() as nat
    }

    /// The last digit in this `EndianNat`. Ignores endianness.
    pub open spec fn last(self) -> nat
        recommends
            self.digits.len() > 0,
    {
        self.digits.last() as nat
    }

    /// The least significant digit in this `EndianNat`.
    pub open spec fn least(self) -> nat
        recommends
            self.digits.len() > 0,
    {
        match self.endian {
            Endian::Little => self.first(),
            Endian::Big => self.last(),
        }
    }

    /// The most significant digit in this `EndianNat`.
    pub open spec fn most(self) -> nat
        recommends
            self.digits.len() > 0,
    {
        match self.endian {
            Endian::Little => self.last(),
            Endian::Big => self.first(),
        }
    }

    /// Constructs an `EndianNat` by skipping the first `n` digits of the original `EndianNat`. Ignores endianness.
    pub open spec fn skip(self, n: nat) -> Self
        recommends
            0 <= n <= self.digits.len(),
    {
        EndianNat { endian: self.endian, digits: self.digits.skip(n as int), phantom: self.phantom }
    }

    /// Constructs an `EndianNat` by taking only the first `n` digits of the original `EndianNat`. Ignores endianness.
    pub open spec fn take(self, n: nat) -> Self
        recommends
            0 <= n <= self.digits.len(),
    {
        EndianNat { endian: self.endian, digits: self.digits.take(n as int), phantom: self.phantom }
    }

    /// Constructs an `EndianNat` by skipping the least significant `n` digits of the original `EndianNat`.
    pub open spec fn skip_least(self, n: nat) -> Self
        recommends
            0 <= n <= self.digits.len(),
    {
        match self.endian {
            Endian::Little => self.skip(n),
            Endian::Big => self.take((self.len() - n) as nat),
        }
    }

    /// Constructs an `EndianNat` by skipping the most significant `n` digits of the original `EndianNat`.
    pub open spec fn skip_most(self, n: nat) -> Self
        recommends
            0 <= n <= self.digits.len(),
    {
        match self.endian {
            Endian::Little => self.take((self.len() - n) as nat),
            Endian::Big => self.skip(n),
        }
    }

    /// Constructs an `EndianNat` by taking only the least significant `n` digits of the original `EndianNat`.
    pub open spec fn take_least(self, n: nat) -> Self
        recommends
            0 <= n <= self.digits.len(),
    {
        match self.endian {
            Endian::Little => self.take(n),
            Endian::Big => self.skip((self.len() - n) as nat),
        }
    }

    /// Constructs an `EndianNat` by taking only the most significant `n` digits of the original `EndianNat`.
    pub open spec fn take_most(self, n: nat) -> Self
        recommends
            0 <= n <= self.digits.len(),
    {
        match self.endian {
            Endian::Little => self.skip((self.len() - n) as nat),
            Endian::Big => self.take(n),
        }
    }

    /// Constructs an `EndianNat` by dropping the first digit of the original `EndianNat`. Ignores endianness.
    pub open spec fn drop_first(self) -> Self
        recommends
            self.len() > 0,
    {
        EndianNat { endian: self.endian, digits: self.digits.drop_first(), phantom: self.phantom }
    }

    /// Constructs an `EndianNat` by dropping the last digit of the original `EndianNat`. Ignores endianness.
    pub open spec fn drop_last(self) -> Self
        recommends
            self.len() > 0,
    {
        EndianNat { endian: self.endian, digits: self.digits.drop_last(), phantom: self.phantom }
    }

    /// Constructs an `EndianNat` by dropping the least significant digit of the original `EndianNat`.
    pub open spec fn drop_least(self) -> Self
        recommends
            self.len() > 0,
    {
        match self.endian {
            Endian::Little => self.drop_first(),
            Endian::Big => self.drop_last(),
        }
    }

    /// Constructs an `EndianNat` by dropping the most significant digits of the original `EndianNat`.
    pub open spec fn drop_most(self) -> Self
        recommends
            self.len() > 0,
    {
        match self.endian {
            Endian::Little => self.drop_last(),
            Endian::Big => self.drop_first(),
        }
    }

    /// Constructs an `EndianNat` by appending the digits of `other` to the end of the digits of `self`. Ignores endianness.
    pub open spec fn append(self, other: Self) -> Self
        recommends
            self.endian == other.endian,
    {
        EndianNat::new(self.endian, self.digits + other.digits)
    }

    /// Constructs an `EndianNat` by appending the digits of `other` to the digits of `self` in the least significant position
    /// (i.e., `other` becomes the least significant bits).
    pub open spec fn append_least(self, other: Self) -> Self
        recommends
            self.endian == other.endian,
    {
        match self.endian {
            Endian::Little => other.append(self),
            Endian::Big => self.append(other),
        }
    }

    /// Constructs an `EndianNat` by appending the digits of `other` to the digits of `self` in the most significant position
    /// (i.e., `other` becomes the most significant bits).
    pub open spec fn append_most(self, other: Self) -> Self
        recommends
            self.endian == other.endian,
    {
        match self.endian {
            Endian::Little => self.append(other),
            Endian::Big => other.append(self),
        }
    }

    /// Constructs an `EndianNat` by appending `n` to the front of the digits of `self`. Ignores endianness.
    pub open spec fn push_first(self, n: int) -> Self
        recommends
            n < B::base(),
    {
        EndianNat { endian: self.endian, digits: seq![n].add(self.digits), phantom: self.phantom }
    }

    /// Constructs an `EndianNat` by appending `n` to the end of the digits of `self`. Ignores endianness.
    pub open spec fn push_last(self, n: int) -> Self
        recommends
            n < B::base(),
    {
        EndianNat { endian: self.endian, digits: self.digits.push(n), phantom: self.phantom }
    }

    /// Constructs an `EndianNat` by appending `n` to the least significant position in the digits of `self`.
    pub open spec fn push_least(self, n: int) -> Self
        recommends
            n < B::base(),
    {
        match self.endian {
            Endian::Little => self.push_first(n),
            Endian::Big => self.push_last(n),
        }
    }

    /// Constructs an `EndianNat` by appending `n` to the most significant position in the digits of `self`.
    pub open spec fn push_most(self, n: int) -> Self
        recommends
            n < B::base(),
    {
        match self.endian {
            Endian::Little => self.push_last(n),
            Endian::Big => self.push_first(n),
        }
    }

    /// Converts an `EndianNat` to the natural number that it represents, hiding the details of endianness.
    #[verifier::opaque]
    pub open spec fn to_nat(self) -> nat
        decreases self.len(),
    {
        if self.len() == 0 {
            0
        } else {
            self.drop_least().to_nat() * B::base() + self.least()
        }
    }

    pub broadcast proof fn to_nat_properties(self)
        requires
            self.wf(),
        ensures
            #[trigger] self.to_nat() < base_upper_bound_excl::<B>(self.len()),
        decreases self.len(),
    {
        reveal(EndianNat::to_nat);
        reveal(pow);
        if self.len() == 0 {
        } else {
            self.drop_least().to_nat_properties();

            calc! {
                (<)
                self.to_nat(); (==) {}
                self.drop_least().to_nat() * B::base() + self.least(); (<) {}
                self.drop_least().to_nat() * B::base() + B::base(); (<=) {
                    broadcast use lemma_mul_inequality, lemma_mul_is_distributive_sub_other_way;

                    assert((base_upper_bound_excl::<B>((self.len() - 1) as nat) - 1)
                        * B::base() as nat == (base_upper_bound_excl::<B>((self.len() - 1) as nat)
                        * B::base() - B::base()) as nat);
                }
                (base_upper_bound_excl::<B>((self.len() - 1) as nat) * B::base() - B::base()
                    + B::base()) as nat; (==) {
                    broadcast use lemma_pow1;

                }
                (base_upper_bound_excl::<B>((self.len() - 1) as nat) * pow(
                    B::base() as int,
                    1,
                )) as nat; (==) {
                    broadcast use lemma_pow_sub_add_cancel;

                }
                base_upper_bound_excl::<B>(self.len()) as nat;
            }
        }
    }

    pub proof fn to_nat_append_least(endian: Self, other: Self)
        requires
            endian.wf(),
            other.wf(),
            endian.endian == other.endian,
        ensures
            endian.append_least(other).to_nat() == (endian.to_nat() * base_upper_bound_excl::<B>(
                other.len(),
            )) + other.to_nat(),
        decreases other.len(),
    {
        reveal(EndianNat::to_nat);
        reveal(pow);
        if other.len() == 0 {
        } else {
            let least = other.least();
            let rest = other.drop_least();
            Self::to_nat_append_least(endian, rest);
            assert(endian.append_least(other).drop_least() =~= endian.append_least(rest));
            assert(endian.to_nat() * base_upper_bound_excl::<B>(rest.len()) * B::base()
                == endian.to_nat() * base_upper_bound_excl::<B>(rest.len() + 1)) by {
                broadcast use lemma_pow1;

                assert(B::base() == pow(B::base() as int, 1));
                broadcast use lemma_pow_adds;

                assert(pow(B::base() as int, rest.len() + 1) == pow(B::base() as int, rest.len())
                    * pow(B::base() as int, 1));
                assert(endian.to_nat() * base_upper_bound_excl::<B>(rest.len()) * B::base()
                    == endian.to_nat() * base_upper_bound_excl::<B>(rest.len() + 1))
                    by (nonlinear_arith)
                    requires
                        base_upper_bound_excl::<B>(rest.len()) * B::base()
                            == base_upper_bound_excl::<B>(rest.len() + 1),
                ;
            }
            assert(endian.append_least(other).to_nat() == (endian.to_nat()
                * base_upper_bound_excl::<B>(other.len())) + other.to_nat()) by (nonlinear_arith)
                requires
                    endian.append_least(other).to_nat() == endian.append_least(rest).to_nat()
                        * B::base() + least,
                    other.to_nat() == rest.to_nat() * B::base() + least,
                    endian.append_least(rest).to_nat() == (endian.to_nat()
                        * base_upper_bound_excl::<B>(rest.len())) + rest.to_nat(),
                    endian.to_nat() * base_upper_bound_excl::<B>(rest.len()) * B::base()
                        == endian.to_nat() * base_upper_bound_excl::<B>(rest.len() + 1),
                    other.len() == rest.len() + 1,
            ;
        }
    }

    /// Converts a natural number to an `EndianNat` representation with the specified number of digits (`len`) and default endianness ([`endianness()`]).
    /// `n` should be less than the maximum number that can be represented in `len` digits in this base.
    pub open spec fn from_nat(n: nat, len: nat) -> Self
        recommends
            n < base_upper_bound_excl::<B>(len),
        decreases len,
    {
        if len == 0 {
            EndianNat { digits: Seq::empty(), endian: endianness(), phantom: PhantomData }
        } else {
            let least = (n % B::base()) as int;
            let rest = n / B::base();
            let rest_endian = Self::from_nat(rest, (len - 1) as nat);
            rest_endian.push_least(least)
        }
    }

    proof fn base_upper_bound_excl_len(n: nat, len: nat)
        requires
            n < base_upper_bound_excl::<B>(len),
            0 < len,
        ensures
            n / B::base() < base_upper_bound_excl::<B>((len - 1) as nat),
    {
        reveal(pow);
        assert(n / B::base() < base_upper_bound_excl::<B>((len - 1) as nat)) by (nonlinear_arith)
            requires
                n < B::base() * base_upper_bound_excl::<B>((len - 1) as nat),
                B::base() > 0,
        ;
    }

    pub broadcast proof fn from_nat_properties(n: nat, len: nat)
        requires
            n < base_upper_bound_excl::<B>(len),
        ensures
            #![trigger Self::from_nat(n, len)]
            Self::from_nat(n, len).len() == len,
            Self::from_nat(n, len).endian == endianness(),
            Self::from_nat(n, len).wf(),
        decreases len,
    {
        if len == 0 {
        } else {
            Self::base_upper_bound_excl_len(n, len);
            let endian_nat = Self::from_nat(n, len);
            let least = endian_nat.least();
            Self::from_nat_properties(n / B::base(), (len - 1) as nat);
            B::base_min();
            assert(least < B::base()) by (nonlinear_arith)
                requires
                    B::base() > 0,
                    least == (n % B::base()),
            ;
        }
    }

    /// Ensures that performing [`from_nat`] and then [`to_nat`] results in the original value,
    /// provided that the value can be encoded in the given base in the given number of digits.
    ///
    /// [`from_nat`]: EndianNat::from_nat
    /// [`to_nat`]: EndianNat::to_nat
    pub broadcast proof fn from_nat_to_nat(n: nat, len: nat)
        requires
            n < base_upper_bound_excl::<B>(len),
        ensures
            #[trigger] Self::from_nat(n, len).to_nat() == n,
        decreases Self::from_nat(n, len).len(),
    {
        reveal(pow);
        reveal(EndianNat::to_nat);
        if Self::from_nat(n, len).len() == 0 {
        } else {
            let endian_nat = Self::from_nat(n, len);
            let least = endian_nat.least();
            let rest = endian_nat.drop_least();
            assert(rest =~= Self::from_nat(n / B::base(), (len - 1) as nat));
            Self::base_upper_bound_excl_len(n, len);
            Self::from_nat_to_nat(n / B::base(), (len - 1) as nat);
            assert((n % B::base()) + (n / B::base()) * B::base() == n) by (nonlinear_arith)
                requires
                    B::base() > 0,
            ;
        }
    }

    /// Ensures that performing [`to_nat`] and then [`from_nat`] results in the original `EndianNat`.
    ///
    /// [`from_nat`]: EndianNat::from_nat
    /// [`to_nat`]: EndianNat::to_nat
    pub broadcast proof fn to_nat_from_nat(endian_nat: Self)
        requires
            endian_nat.wf(),
            endian_nat.endian == endianness(),
        ensures
            #[trigger] Self::from_nat(endian_nat.to_nat(), endian_nat.len()) == endian_nat,
        decreases endian_nat.len(),
    {
        reveal(pow);
        reveal(EndianNat::to_nat);
        if endian_nat.len() == 0 {
        } else {
            let n = endian_nat.to_nat();
            let least = endian_nat.least();
            let rest = endian_nat.drop_least();
            Self::to_nat_from_nat(rest);
            assert(least == n % B::base()) by (nonlinear_arith)
                requires
                    n == rest.to_nat() * B::base() + least,
                    least < B::base(),
            ;
            assert(rest.to_nat() == n / B::base()) by (nonlinear_arith)
                requires
                    n == rest.to_nat() * B::base() + least,
                    least < B::base(),
            ;
        }
    }

    /// Converts an `EndianNat` to the natural number that it represents, working from "left to right" in the per-digit representation.
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
                },
            }
        }
    }

    /// Converts an `EndianNat` to the natural number that it represents, working from "right to left" in the per-digit representation.
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
                },
                Endian::Big => self.drop_last().to_nat_left() * B::base() + self.last(),
            }
        }
    }

    /// Ensures that [`to_nat`], [`to_nat_right`], and [`to_nat_left`] agree.
    ///
    /// [`to_nat`]: EndianNat::to_nat
    /// [`to_nat_right`]: EndianNat::to_nat_right
    /// [`to_nat_left`]: EndianNat::to_nat_left
    pub proof fn to_nat_left_right_eq(self)
        requires
            self.wf(),
        ensures
            self.to_nat() == self.to_nat_right() == self.to_nat_left(),
    {
        self.to_nat_big_left_little_right_eq();
        match self.endian {
            Endian::Little => self.nat_left_eq_nat_right_little(),
            Endian::Big => self.nat_left_eq_nat_right_big(),
        }
    }

    proof fn to_nat_big_left_little_right_eq(self)
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
            self.drop_least().to_nat_big_left_little_right_eq();
        }
    }

    proof fn nat_left_eq_nat_right_little(self)
        requires
            self.wf(),
            self.endian == Endian::Little,
        ensures
            self.to_nat_left() == self.to_nat_right(),
        decreases self.len(),
    {
        reveal(EndianNat::to_nat_left);
        reveal(EndianNat::to_nat_right);
        if self.len() == 0 {
        } else {
            if self.drop_last().len() == 0 {
                calc! {
                    (==)
                    self.to_nat_left(); {
                        assert(self.drop_last().to_nat_left() == 0);
                    }
                    (self.last() * pow(B::base() as int, (self.len() - 1) as nat)) as nat; {
                        reveal(pow);
                    }
                    self.last(); {}
                    self.first(); {
                        assert(self.drop_first().to_nat_right() == 0);
                        assert(0 * B::base() == 0);
                    }
                    self.to_nat_right();
                };
            } else {
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

    proof fn nat_left_eq_nat_right_big(self)
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
}

// /////////////////////////////////////////////////// //
//         Conversion Routines                         //
// /////////////////////////////////////////////////// //
impl<B: Base> EndianNat<B> {
    /// [`B::base()`] to the power of `exp()` is [`BIG::base()`].
    /// In other words, `exp()` is the number of digits in base `B` that correspond to a single digit in base `BIG`.
    ///
    /// [`B::base()`]: Base::base
    /// [`BIG::base()`]: Base::base
    pub open spec fn exp<BIG>() -> nat where BIG: BasePow2, B: CompatibleSmallerBaseFor<BIG> {
        BIG::bits() / B::bits()
    }

    pub broadcast proof fn exp_properties<BIG>() where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,

        ensures
            #![trigger Self::exp()]
            base_upper_bound_excl::<B>(Self::exp()) == BIG::base(),
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
            base_upper_bound_excl::<B>(Self::exp()); {
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

    /// Converts an `EndianNat` representation in the "big" base `BIG` to an `EndianNat` representation in the "small" base `B`.
    /// The result represents the same non-negative number as the original.
    pub open spec fn from_big<BIG>(n: EndianNat<BIG>) -> Self where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,

        decreases n.len(),
    {
        if n.len() == 0 {
            EndianNat::new(n.endian, Seq::empty())
        } else {
            Self::from_big(n.drop_least()).append_least(EndianNat::from_nat(n.least(), Self::exp()))
        }
    }

    pub broadcast proof fn from_big_properties<BIG>(n: EndianNat<BIG>) where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,

        requires
            n.wf(),
            n.endian == endianness(),
        ensures
            #![trigger Self::from_big(n)]
            Self::from_big(n).wf(),
            Self::from_big(n).endian == endianness(),
            Self::from_big(n).len() == n.len() * Self::exp(),
            Self::from_big(n).to_nat() == n.to_nat(),
        decreases n.len(),
    {
        reveal(EndianNat::to_nat);
        broadcast use EndianNat::exp_properties;

        if n.len() == 0 {
        } else {
            let least = n.least();
            let rest = n.drop_least();
            Self::from_big_properties(rest);
            Self::from_nat_properties(least, Self::exp());
            assert(Self::from_big(n).len() == n.len() * Self::exp()) by (nonlinear_arith)
                requires
                    Self::from_big(n).len() == (n.len() - 1) * Self::exp() + Self::exp(),
            ;
            let small_least = EndianNat::from_nat(least, Self::exp());
            let small_rest = Self::from_big(rest);
            Self::to_nat_append_least(small_rest, small_least);
            Self::from_nat_to_nat(least, Self::exp());
        }
    }

    /// Converts an `EndianNat` representation in the "small" base `B` to an `EndianNat` representation in the "big" base `BIG`.
    /// The result represents the same non-negative number as the original.
    #[verifier::opaque]
    pub open spec fn to_big<BIG>(n: EndianNat<B>) -> EndianNat<BIG> where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,

        recommends
            n.len() % Self::exp() == 0,
        decreases n.len(),
        when n.len() % Self::exp() == 0
        via Self::to_big_decreases
    {
        if n.len() == 0 {
            EndianNat::new(n.endian, Seq::empty())
        } else {
            Self::to_big(n.skip_least(Self::exp())).append_least(
                EndianNat::new(n.endian, seq![n.take_least(Self::exp()).to_nat() as int]),
            )
        }
    }

    #[via_fn]
    proof fn to_big_decreases<BIG>(n: EndianNat<B>) where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,
     {
        broadcast use EndianNat::exp_properties;

        if n.len() != 0 {
            assert(Self::exp() <= n.len()) by {
                broadcast use crate::vstd::arithmetic::div_mod::lemma_mod_is_zero;

            }
            assert(n.skip_least(Self::exp()).len() < n.len());
        }
    }

    pub broadcast proof fn to_big_properties<BIG>(n: EndianNat<B>) where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,

        requires
            n.wf(),
            n.endian == endianness(),
            n.len() % Self::exp() == 0,
        ensures
            #![trigger Self::to_big(n)]
            Self::to_big(n).wf(),
            Self::to_big(n).endian == endianness(),
            Self::to_big(n).len() == n.len() / Self::exp(),
            Self::to_big(n).to_nat() == n.to_nat(),
        decreases n.len(),
    {
        reveal(EndianNat::to_big);
        reveal(EndianNat::to_nat);
        broadcast use EndianNat::exp_properties;

        if n.len() == 0 {
        } else {
            let least = n.take_least(Self::exp());
            let rest = n.skip_least(Self::exp());
            assert(n.len() >= Self::exp()) by (nonlinear_arith)
                requires
                    n.len() % Self::exp() == 0,
                    Self::exp() > 0,
                    n.len() > 0,
            ;
            assert(rest.len() % Self::exp() == 0) by (nonlinear_arith)
                requires
                    rest.len() == n.len() - Self::exp(),
                    n.len() % Self::exp() == 0,
            ;
            Self::to_big_properties(rest);
            Self::to_nat_properties(least);
            let big_least = EndianNat::<BIG>::new(n.endian, seq![least.to_nat() as int]);
            let big_rest = Self::to_big(rest);
            assert(Self::to_big(n).to_nat() == n.to_nat()) by {
                assert(big_rest.append_least(big_least).to_nat() == (big_rest.to_nat()
                    * base_upper_bound_excl::<BIG>(big_least.len())) + big_least.to_nat()) by {
                    EndianNat::<BIG>::to_nat_append_least(big_rest, big_least);
                }
                assert(big_least.to_nat() == least.to_nat()) by {
                    assert(big_least.least() == least.to_nat());
                    reveal_with_fuel(EndianNat::to_nat, 2);
                }
                assert(n.to_nat() == (rest.to_nat() * base_upper_bound_excl::<B>(Self::exp()))
                    + least.to_nat()) by {
                    assert(n =~= rest.append_least(least));
                    EndianNat::<B>::to_nat_append_least(rest, least);
                }
                assert(base_upper_bound_excl::<B>(Self::exp()) == base_upper_bound_excl::<BIG>(
                    big_least.len(),
                )) by {
                    broadcast use lemma_pow1;

                }
            }
            assert(Self::to_big(n).len() == n.len() / Self::exp()) by {
                assert(Self::to_big(n).len() == n.len() / Self::exp()) by (nonlinear_arith)
                    requires
                        big_rest.len() == rest.len() / Self::exp(),
                        Self::to_big(n).len() == big_rest.len() + 1,
                        n.len() == rest.len() + Self::exp(),
                        Self::exp() > 0,
                ;
            }
        }

    }

    /// Ensures that performing [`to_big`] and then [`from_big`] results in the original `EndianNat<B>`.
    ///
    /// [`to_big`]: EndianNat::to_big
    /// [`from_big`]: EndianNat::from_big
    pub broadcast proof fn to_big_from_big<BIG>(n: EndianNat<B>) where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,

        requires
            n.wf(),
            n.endian == endianness(),
            n.len() % Self::exp() == 0,
        ensures
            #[trigger] Self::from_big(Self::to_big(n)) == n,
        decreases n.len(),
    {
        reveal(EndianNat::to_big);
        broadcast use EndianNat::exp_properties;

        if n.len() == 0 {
        } else {
            let least = n.take_least(Self::exp());
            let rest = n.skip_least(Self::exp());
            assert(n.len() >= Self::exp()) by (nonlinear_arith)
                requires
                    n.len() % Self::exp() == 0,
                    Self::exp() > 0,
                    n.len() > 0,
            ;
            assert(rest.len() % Self::exp() == 0) by (nonlinear_arith)
                requires
                    rest.len() == n.len() - Self::exp(),
                    n.len() % Self::exp() == 0,
            ;
            Self::to_big_from_big(rest);
            let big = Self::to_big(n);
            assert(big =~= Self::to_big(rest).append_least(
                EndianNat::new(n.endian, seq![least.to_nat() as int]),
            ));
            let big_least = big.least();
            let big_rest = big.drop_least();
            assert(big_rest =~= Self::to_big(rest));
            assert(Self::from_big(big_rest) == rest);
            Self::to_nat_from_nat(least);
            assert(EndianNat::<B>::from_nat(big_least, Self::exp()) == least);
        }
    }

    /// Ensures that performing [`from_big`] and then [`to_big`] results in the original `EndianNat<BIG>`.
    ///
    /// [`to_big`]: EndianNat::to_big
    /// [`from_big`]: EndianNat::from_big
    pub broadcast proof fn from_big_to_big<BIG>(n: EndianNat<BIG>) where
        BIG: BasePow2,
        B: CompatibleSmallerBaseFor<BIG>,

        requires
            n.wf(),
            n.endian == endianness(),
        ensures
            #[trigger] Self::to_big(Self::from_big(n)) == n,
        decreases n.len(),
    {
        reveal(EndianNat::to_big);
        reveal(EndianNat::to_nat);
        broadcast use EndianNat::exp_properties;

        if n.len() == 0 {
            Self::from_big_properties(n);
            let small = Self::from_big(n);
            assert(small.len() % Self::exp() == 0) by (nonlinear_arith)
                requires
                    small.len() == 0,
                    Self::exp() > 0,
            ;
            Self::to_big_properties(small);
            assert(Self::to_big(Self::from_big(n)).digits == n.digits);
            assert(Self::to_big(Self::from_big(n)).endian == n.endian);
        } else {
            let least = n.least();
            let rest = n.drop_least();
            Self::from_big_to_big(rest);
            Self::from_big_properties(rest);

            let small = Self::from_big(n);
            let small_least = small.take_least(Self::exp());
            let small_rest = small.skip_least(Self::exp());
            Self::from_nat_properties(least, Self::exp());
            let from_nat_least = EndianNat::<B>::from_nat(least, Self::exp());
            assert(small_least =~= from_nat_least);
            EndianNat::<B>::from_nat_to_nat(least, Self::exp());

            assert(small_rest =~= Self::from_big(rest));
            assert(small_rest.len() % Self::exp() == 0) by (nonlinear_arith)
                requires
                    small_rest.len() == rest.len() * Self::exp(),
                    Self::exp() > 0,
            ;

            Self::from_big_properties(n);
            assert(small.len() % Self::exp() == 0) by (nonlinear_arith)
                requires
                    small.len() == n.len() * Self::exp(),
                    Self::exp() > 0,
            ;
        }
    }
}

/***** Functions involving both little and big endian *****/

/// Converts a sequence of digits in base `B` in default endianness ([`endianness()`]) to an `EndianNat` in the larger base `BIG`.
pub open spec fn to_big_from_digits<BIG, B>(n: Seq<B>) -> EndianNat<BIG> where
    BIG: BasePow2,
    B: CompatibleSmallerBaseFor<BIG> + Integer,
 {
    EndianNat::<B>::to_big::<BIG>(EndianNat::<B>::new(endianness(), n.map(|i, d| d as int)))
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

pub broadcast group group_endian_nat_axioms {
    EndianNat::from_nat_properties,
    EndianNat::to_nat_properties,
    EndianNat::from_nat_to_nat,
    EndianNat::to_nat_from_nat,
    EndianNat::exp_properties,
    EndianNat::to_big_properties,
    EndianNat::from_big_properties,
    EndianNat::from_big_to_big,
    EndianNat::to_big_from_big,
}

} // verus!
