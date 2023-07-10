use core::{marker};

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;

verus! {

/// `Seq<A>` is a sequence type for specifications.
/// To use a "sequence" in compiled code, use an `exec` type like [`vec::Vec`](crate::vec::Vec)
/// that has `Seq<A>` as its specification type.
///
/// An object `seq: Seq<A>` has a length, given by [`seq.len()`](Seq::len),
/// and a value at each `i` for `0 <= i < seq.len()`, given by [`seq[i]`](Seq::index).
///
/// Sequences can be constructed in a few different ways:
///  * [`Seq::empty`] construct an empty sequence (`len() == 0`)
///  * [`Seq::new`] construct a sequence of a given length, initialized according
///     to a given function mapping indices `i` to values `A`.
///  * The [`seq!`] macro, to construct small sequences of a fixed size (analagous to the
///     [`std::vec!`] macro).
///  * By manipulating an existing sequence with [`Seq::push`], [`Seq::update`],
///    or [`Seq::add`].
///
/// To prove that two sequences are equal, it is usually easiest to use the
/// [`assert_seqs_equal!`](crate::seq_lib::assert_seqs_equal) macro.

#[verifier::external_body]
#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
pub struct Seq<A> {
    dummy: marker::PhantomData<A>,
}

impl<A> Seq<A> {
    /// An empty sequence (i.e., a sequence of length 0).

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::empty"]
    pub spec fn empty() -> Seq<A>;

    /// Construct a sequence `s` of length `len` where entry `s[i]` is given by `f(i)`.

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::new"]
    pub spec fn new(len: nat, f: impl Fn(int) -> A) -> Seq<A>;

    #[verifier(inline)]
    pub open spec fn singleton(elt: A) -> Seq<A> {
        Self::empty().push(elt)
    }

    /// The length of a sequence.

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::len"]
    pub spec fn len(self) -> nat;

    /// Gets the value at the given index `i`.
    ///
    /// If `i` is not in the range `[0, self.len())`, then the resulting value
    /// is meaningless and arbitrary.

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::index"]
    pub spec fn index(self, i: int) -> A
        recommends 0 <= i < self.len();

    /// `[]` operator, synonymous with `index`

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A
        recommends 0 <= i < self.len()
    {
        self.index(i)
    }

    /// Appends the value `a` to the end of the sequence.
    /// This always increases the length of the sequence by 1.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn push_test() {
    ///     assert_seqs_equal!(
    ///           seq![10, 11, 12].push(13),
    ///           seq![10, 11, 12, 13],
    ///     );
    /// }
    /// ```

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::push"]
    pub spec fn push(self, a: A) -> Seq<A>;

    /// Updates the sequence at the given index, replacing the element with the given
    /// value, and leaves all other entries unchanged.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn update_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     let t = s.update(2, -5);
    ///     assert_seqs_equal!(t, seq![10, 11, -5, 13, 14]);
    /// }
    /// ```

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::update"]
    pub spec fn update(self, i: int, a: A) -> Seq<A>
        recommends 0 <= i < self.len();

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns `true` if the two sequences are pointwise equal, i.e.,
    /// they have the same length and the corresponding values are equal
    /// at each index. This is equivalent to the sequences being actually equal
    /// by [`axiom_seq_ext_equal`].
    ///
    /// To prove that two sequences are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_seqs_equal!`](crate::seq_lib::assert_seqs_equal) macro,
    /// rather than using `.ext_equal` directly.

    #[deprecated = "use =~= or =~~= instead"]
    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::ext_equal"]
    pub open spec fn ext_equal(self, s2: Seq<A>) -> bool {
        self =~= s2
    }

    /// Returns a sequence for the given subrange.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn subrange_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     //                  ^-------^
    ///     //          0   1   2   3   4   5
    ///     let sub = s.subrange(2, 4);
    ///     assert_seqs_equal!(sub, seq![12, 13]);
    /// }
    /// ```

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::subrange"]
    pub spec fn subrange(self, start_inclusive: int, end_exclusive: int) -> Seq<A>
        recommends 0 <= start_inclusive <= end_exclusive <= self.len();

    /// Returns a sequence containing only the first n elements of the original sequence
    #[verifier(inline)]
    pub open spec fn take(self, n: int) -> Seq<A>{
        self.subrange(0,n)
    } 

    /// Returns a sequence that drops the first n elements of the original sequence
    #[verifier(inline)]
    pub open spec fn drop(self, n: int) -> Seq<A>{
        self.subrange(n,self.len() as int)
    }

    /// Concatenates the sequences.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn add_test() {
    ///     assert_seqs_equal!(
    ///         seq![10, 11].push(seq![12, 13, 14]),
    ///         seq![10, 11, 12, 13, 14],
    ///     );
    /// }
    /// ```

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::add"]
    pub spec fn add(self, rhs: Seq<A>) -> Seq<A>;

    /// `+` operator, synonymous with `add`

    #[verifier(inline)]
    pub open spec fn spec_add(self, rhs: Seq<A>) -> Seq<A> {
        self.add(rhs)
    }

    /// Returns the last element of the sequence.

    #[rustc_diagnostic_item = "verus::pervasive::seq::Seq::last"]
    pub open spec fn last(self) -> A
        recommends 0 < self.len()
    {
        self[self.len() as int - 1]
    }

    /// Returns the first element of the sequence.
    
    #[rustc_diagnostic_item = "vstd::seq::Seq::first"]
    pub open spec fn first(self) -> A
        recommends 0 < self.len()
    {
        self[0]
    }
}

// Trusted axioms

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger](decreases_to!(s => s[i])),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_new_len<A>(len: nat, f: FnSpec(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_new_index<A>(len: nat, f: FnSpec(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        Seq::new(len, f)[i] == f(i),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.push(a)[i] == s[i],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        0 <= i1 < s.len(),
        0 <= i2 < s.len(),
        i1 != i2,
    ensures
        s.update(i2, a)[i1] == s[i1],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        s.subrange(j, k)[i] == s[i + j],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures #[trigger] s1.add(s2).len() == s1.len() + s2.len()
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        s1.add(s2)[i] == s1[i],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= s1.len(),
        i < s1.len() as int + s2.len(),
    ensures
        s1.add(s2)[i] == s2[i - s1.len()],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_contains<A>(s: Seq<A>, x: A)
    ensures
        s.contains(x) <==> exists |i: int| 0<= i < s.len() && #[trigger] s[i]==x,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_empty_contains_nothing<A>(x: A)
    ensures
        !(#[trigger] Seq::<A>::empty().contains(x)),
{}

// Note: Dafny only does one way implication, but theoretically it could go both ways
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_empty_equality<A>(s: Seq<A>)
    ensures
        #[trigger] s.len() == 0 ==> s=~= Seq::<A>::empty(),
{}

//I have proven in seq_lib
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_concat_contains_all_elements<A>(x: Seq<A>, y: Seq<A>, elt: A)
    ensures
        #[trigger] (x+y).contains(elt) <==> x.contains(elt) ||  y.contains(elt),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    ensures #[trigger] s.push(v).contains(x) <==> v==x || s.contains(x),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_elements<A>(s: Seq<A>, start: int, stop: int, x: A)
    ensures #[trigger] s.subrange(start,stop).contains(x) <==> 
        exists |i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x,
{}

// ----------------optional singleton axioms? ------------------- //
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_singleton_length<A>(elt: A)
    ensures
        #[trigger] Seq::<A>::singleton(elt).len() == 1
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_singleton_index<A>(elt: A)
    ensures
        #[trigger] Seq::<A>::singleton(elt)[0] == elt,
{}

// ----------------optional Take/Drop axioms? ------------------- //
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> #[trigger] s.take(n).len() == n,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_contains<A>(s: Seq<A>, n: int, x: A)
    ensures
        #[trigger] s.take(n).contains(x) <==> exists |i: int| 0<= i < n && i < s.len() && #[trigger] s[i] == x,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0<= j < n && j < s.len() ==> #[trigger] s.take(n)[j] == s[j],
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> #[trigger] s.drop(n).len() == s.len() - n,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_contains<A>(s: Seq<A>, n: int, x: A)
    ensures
        #[trigger] s.drop(n).contains(x) <==> exists |i: int| 0<= i < s.len() && n <= i && #[trigger] s[i] == x,
{}

// PROBLEMATIC, made a proof in pervasive/bytes fail
// fixed with making spec functions in bytes.rs opaque
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <=n && 0<= j < (s.len() - n) ==> #[trigger] s.drop(n)[j] == s[j+n],
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_index2<A>(s: Seq<A>, n: int, k: int, diff: int)
    ensures 
        0 <= n <= k < s.len() && diff == k-n ==> #[trigger] s.drop(n)[diff] == #[trigger] s[k]
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_append_take_drop<A>(a: Seq<A>, b: Seq<A>, n: int)
    ensures
        n == a.len() ==> (#[trigger] (a+b).take(n) == a && #[trigger] (a+b).drop(n) == b),
{}

// Commutability of Take and Drop with Update.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> #[trigger] s.update(i,v).take(n) =~= s.take(n).update(i,v),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        n <= i < s.len() ==> #[trigger] s.update(i,v).take(n) =~= s.take(n),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i,v).drop(n) =~= s.drop(n).update(i-n,v),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> #[trigger] s.update(i,v).drop(n) =~= s.drop(n),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_build_commut<A>(s: Seq<A>, v: A, n: int)
    ensures
        0<= n <= s.len() ==> #[trigger] s.push(v).drop(n) == s.drop(n).push(v), 
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_nothing<A>(s: Seq<A>, n: int)
    ensures
        n==0 ==> #[trigger] s.drop(n) == s,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_nothing<A>(s: Seq<A>, n: int)
    ensures
        n==0 ==> #[trigger] s.take(n) == Seq::<A>::empty(),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_of_drop<A>(s: Seq<A>, m: int, n: int)
    ensures
        (0 <= m && 0 <= n && m+n <= s.len()) ==> s.drop(m).drop(n) == s.drop(m+n),
{}

// ------------- Macros ---------------- //

#[doc(hidden)]
#[macro_export]
macro_rules! seq_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::seq::Seq::empty()
            $(.push($elem))*
    }
}

/// Creates a [`Seq`] containing the given elements.
///
/// ## Example
///
/// ```rust
/// let s = seq![11, 12, 13];
///
/// assert(s.len() == 3);
/// assert(s[0] == 11);
/// assert(s[1] == 12);
/// assert(s[2] == 13);
/// ```

#[macro_export]
macro_rules! seq {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::seq::seq_internal!($($tail)*))
    };
}

#[doc(hidden)]
pub use seq_internal;
pub use seq;

} // verus!
