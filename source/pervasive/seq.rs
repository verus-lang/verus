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

    /// Returns a constant sequence of a given length
    spec fn fill(val: A, length: nat) -> Seq<A>
    {
        if length <= 0 {Self::empty()}
        else {
           Self::new(length, |i: int| val)
        }
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

    pub open spec fn rank(self) -> int;

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

// Ported from Dafny prelude
//#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_contains<A>(s: Seq<A>, x: A)
    ensures
        s.contains(x) <==> exists |i: int| 0<= i < s.len() && #[trigger] s[i]==x,
{}

// Ported from Dafny prelude
//#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_empty_contains_nothing<A>(x: A)
    ensures
        !(#[trigger] Seq::<A>::empty().contains(x)),
{}

// Ported from Dafny prelude
// Note: Dafny only does one way implication, but theoretically it could go both ways
//#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_empty_equality<A>(s: Seq<A>)
    ensures
        #[trigger] s.len() == 0 ==> s=~= Seq::<A>::empty(),
{}

// Ported from Dafny prelude
//#[verifier(external_body)]
//#[verifier(broadcast_forall)]
/// The concatenation of two sequences contains only the elements
/// of the two sequences
pub proof fn axiom_seq_concat_contains_all_elements<A>(x: Seq<A>, y: Seq<A>, elt: A)
    ensures
        #[trigger] (x+y).contains(elt) <==> x.contains(elt) ||  y.contains(elt),
    decreases
        x.len(),
{
    if x.len() == 0 && y.len() >0 {
        assert((x+y) =~= y);
    } else {
        assert forall |elt: A| #[trigger] x.contains(elt) implies #[trigger] (x+y).contains(elt)
        by {
            let index = choose |i: int| 0 <= i < x.len() && x[i] == elt;
            assert((x+y)[index] == elt);
        }
        assert forall |elt: A| #[trigger] y.contains(elt) implies #[trigger] (x+y).contains(elt)
        by {
            let index = choose |i: int| 0 <= i < y.len() && y[i] == elt;
            assert((x+y)[index+x.len()] == elt);
        }
    }
}

// Ported from Dafny prelude
//#[verifier(external_body)]
//#[verifier(broadcast_forall)]
/// After pushing an element onto a sequence, the sequence contains that element
pub proof fn axiom_seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    ensures 
        (#[trigger] s.push(v).contains(x) <==> v==x || s.contains(x))
            && #[trigger] s.push(v).contains(v),
{
    assert forall |elt: A| #[trigger] s.contains(elt) implies #[trigger] s.push(v).contains(elt)
    by {
        let index = choose |i: int| 0 <= i < s.len() && s[i] == elt;
        assert(s.push(v)[index] == elt);
    }
    assert(s.push(v)[s.len() as int] == v);
}

// Ported from Dafny prelude
//#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_elements<A>(s: Seq<A>, start: int, stop: int, x: A)
    requires
        0 <= start <= stop <= s.len(),
    ensures s.subrange(start,stop).contains(x) <==> 
        (exists |i: int| 0 <= start <= i < stop <= s.len() && s[i] == x),
{
    assert((exists |i: int| 0 <= start <= i < stop <= s.len() && s[i] == x) ==> s.subrange(start,stop).contains(x)) by {
        if exists |i: int| 0 <= start <= i < stop <= s.len() && s[i] == x
        {
            let index = choose |i: int| 0 <= start <= i < stop <= s.len() && s[i] == x;
            assert(s.subrange(start,stop)[index - start] == s[index]);
        }
        
    }
    
}

// ----------------optional singleton axioms? ------------------- //

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_singleton_length<A>(elt: A)
    ensures
        #[trigger] Seq::<A>::singleton(elt).len() == 1
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_singleton_index<A>(elt: A)
    ensures
        #[trigger] Seq::<A>::singleton(elt)[0] == elt,
{}

// ----------------optional Take/Drop axioms? ------------------- //

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> #[trigger] s.take(n).len() == n,
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_contains<A>(s: Seq<A>, n: int, x: A)
    ensures
        #[trigger] s.take(n).contains(x) <==> (exists |i: int| 0<= i < n && i < s.len() && #[trigger] s[i] == x),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0<= j < n <= s.len() ==> #[trigger] s.take(n)[j] == s[j],
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> #[trigger] s.drop(n).len() == s.len() - n,
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_contains<A>(s: Seq<A>, n: int, x: A)
    ensures
        #[trigger] s.drop(n).contains(x) <==> (exists |i: int| 0<= i < s.len() && n <= i && #[trigger] s[i] == x),
{}

// PROBLEMATIC, made a proof in pervasive/bytes fail
// fixed with making spec functions in bytes.rs opaque
// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <=n && 0<= j < (s.len() - n) ==> #[trigger] s.drop(n)[j] == s[j+n],
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_index2<A>(s: Seq<A>, n: int, k: int)
    ensures 
        0 <= n <= k < s.len() ==> (#[trigger] s.drop(n))[k-n] == #[trigger] s[k]
{}

// // Ported from Dafny prelude
// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_seq_append_take_drop<A>(a: Seq<A>, b: Seq<A>, n: int)
//     ensures
//         n == a.len() ==> (#[trigger] (a+b).take(n) == a && #[trigger] (a+b).drop(n) == b),
// {}

// Commutability of Take and Drop with Update.
// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> #[trigger] s.update(i,v).take(n) == s.take(n).update(i,v),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i,v).take(n) == s.take(n),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i,v).drop(n) == s.drop(n).update(i-n,v),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> #[trigger] s.update(i,v).drop(n) == s.drop(n),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_build_commut<A>(s: Seq<A>, v: A, n: int)
    ensures
        0<= n <= s.len() ==> #[trigger] s.push(v).drop(n) == s.drop(n).push(v), 
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_nothing<A>(s: Seq<A>, n: int)
    ensures
        n==0 ==> #[trigger] s.drop(n) == s,
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_take_nothing<A>(s: Seq<A>, n: int)
    ensures
        n==0 ==> #[trigger] s.take(n) == Seq::<A>::empty(),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_drop_of_drop<A>(s: Seq<A>, m: int, n: int)
    ensures
        (0 <= m && 0 <= n && m+n <= s.len()) ==> s.drop(m).drop(n) == s.drop(m+n),
{}

// ----------Rank function specifications-------- //

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_rank_take<A>(s: Seq<A>, i: int)
    ensures 
        0 <= i < s.len() ==> #[trigger] s.take(i).rank() < s.rank()
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_rank_drop<A>(s: Seq<A>, i: int)
    ensures 
        0 < i <= s.len() ==> #[trigger] s.drop(i).rank() < s.rank()
{}

// Ported from Dafny prelude
#[verifier(external_body)]
//#[verifier(broadcast_forall)]
pub proof fn axiom_seq_rank_append_take_drop<A>(s: Seq<A>, i: int, j: int)
    ensures 
        0 <= i < j <= s.len() ==> #[trigger] (s.take(i) + s.drop(j)).rank() < s.rank()
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

// auto style axiom bundle
pub proof fn seq_magic<A>() 
    ensures
        forall |s: Seq<A>, x: A| s.contains(x) <==> exists |i: int| 0<= i < s.len() && #[trigger] s[i]==x, //axiom_seq_contains(s, x),
        forall |x: A| !(#[trigger] Seq::<A>::empty().contains(x)), //axiom_seq_empty_contains_nothing(x),
        forall |s: Seq<A>| #[trigger] s.len() == 0 ==> s=~= Seq::<A>::empty(),//axiom_seq_empty_equality(s),
        forall |x: Seq<A>, y: Seq<A>, elt: A| #[trigger] (x+y).contains(elt) <==> x.contains(elt) ||  y.contains(elt),//axiom_seq_concat_contains_all_elements(x, y, elt),
        forall |s: Seq<A>, v: A, x: A| (#[trigger] s.push(v).contains(x) <==> v==x || s.contains(x))
                && #[trigger] s.push(v).contains(v),//axiom_seq_contains_after_push(s, v, x)
        forall |s: Seq<A>, start: int, stop: int, x: A| (0<=start<=stop<=s.len() && #[trigger] s.subrange(start,stop).contains(x)) <==> 
               (exists |i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x),//axiom_seq_subrange_elements(s, start, stop, x),
        forall |elt: A| #[trigger] Seq::<A>::singleton(elt).len() == 1, //axiom_seq_singleton_length(elt),
        forall |elt: A| #[trigger] Seq::<A>::singleton(elt)[0] == elt, //axiom_seq_singleton_index(elt),
        forall |s: Seq<A>, n: int| 0 <= n <= s.len() ==> #[trigger] s.take(n).len() == n, //axiom_seq_take_len(s, n)
        forall |s: Seq<A>, n: int, x: A| #[trigger] s.take(n).contains(x) 
                <==> (exists |i: int| 0<= i < n && i < s.len() && #[trigger] s[i] == x),//axiom_seq_take_contains(s, n, x),
        forall |s: Seq<A>, n: int, j: int|  0<= j < n <= s.len() ==> #[trigger] s.take(n)[j] == s[j],//axiom_seq_take_index(s, n, j),
        forall |s: Seq<A>, n: int| 0 <= n <= s.len() ==> #[trigger] s.drop(n).len() == s.len() - n, //axiom_seq_drop_len(s, n),
        forall |s: Seq<A>, n: int, x: A| #[trigger] s.drop(n).contains(x) 
                <==> (exists |i: int| 0<= i < s.len() && n <= i && #[trigger] s[i] == x),//axiom_seq_drop_contains(s, n, x),
        forall |s: Seq<A>, n: int, j: int| 0 <=n && 0<= j < (s.len() - n) ==> #[trigger] s.drop(n)[j] == s[j+n],//axiom_seq_drop_index(s, n, j),
       // forall |a: Seq<A>, b: Seq<A>, n: int| n == a.len() ==> (#[trigger] (a+b).take(n) == a && #[trigger] (a+b).drop(n) == b),//axiom_seq_append_take_drop(a, b, n),
        forall |s: Seq<A>, i: int, v: A, n: int| 0 <= i < n <= s.len() ==> #[trigger] s.update(i,v).take(n) == s.take(n).update(i,v),//axiom_seq_take_update_commut1(s, i, v, n),
        forall |s: Seq<A>, i: int, v: A, n: int| 0 <= n <= i < s.len() ==> #[trigger] s.update(i,v).take(n) == s.take(n),//axiom_seq_take_update_commut2(s, i, v, n),
        forall |s: Seq<A>, i: int, v: A, n: int| 0 <= n <= i < s.len() ==> #[trigger] s.update(i,v).drop(n) == s.drop(n).update(i-n,v),//axiom_seq_drop_update_commut1(s, i, v, n),
        forall |s: Seq<A>, i: int, v: A, n: int| 0 <= i < n <= s.len() ==> #[trigger] s.update(i,v).drop(n) == s.drop(n),//axiom_seq_drop_update_commut2(s, i, v, n),
        forall |s: Seq<A>, v: A, n: int| 0 <= n <= s.len() ==> #[trigger] s.push(v).drop(n) == s.drop(n).push(v),//axiom_seq_drop_build_commut(s, v, n),
        forall |s: Seq<A>, n: int| n==0 ==> #[trigger] s.drop(n) == s,//axiom_seq_drop_nothing(s, n),
        forall |s: Seq<A>, n: int| n==0 ==> #[trigger] s.take(n) == Seq::<A>::empty(), //axiom_seq_take_nothing(s, n),
        forall |s: Seq<A>, m: int, n: int| (0 <= m && 0 <= n && m+n <= s.len()) ==> s.drop(m).drop(n) == s.drop(m+n),//axiom_seq_drop_of_drop(s, m, n),
        forall |s: Seq<A>, i: int| 0 <= i < s.len() ==> #[trigger] s.take(i).rank() < s.rank(),//axiom_seq_rank_take(s, i),
        forall |s: Seq<A>, i: int|  0 < i <= s.len() ==> #[trigger] s.drop(i).rank() < s.rank(),//axiom_seq_rank_drop(s, i),
        forall |s: Seq<A>, i: int, j: int| 0 <= i < j <= s.len() ==> #[trigger] (s.take(i) + s.drop(j)).rank() < s.rank(),//axiom_seq_rank_append_take_drop(s, i, j),
{
    assert forall |x: Seq<A>, y: Seq<A>, elt: A| #[trigger] (x+y).contains(elt) implies x.contains(elt) ||  y.contains(elt) by {
        axiom_seq_concat_contains_all_elements(x, y, elt);
    }
    assert forall |x: Seq<A>, y: Seq<A>, elt: A| x.contains(elt) ||  y.contains(elt) implies #[trigger] (x+y).contains(elt) by {
        axiom_seq_concat_contains_all_elements(x, y, elt);
    }
    assert forall |s: Seq<A>, v: A, x: A| #[trigger] s.push(v).contains(x) implies v==x || s.contains(x) by {
        axiom_seq_contains_after_push(s, v, x);
    }
    assert forall |s: Seq<A>, v: A, x: A| v==x || s.contains(x) implies #[trigger] s.push(v).contains(x) by {
        axiom_seq_contains_after_push(s, v, x);
    }
    assert forall |s: Seq<A>, start: int, stop: int, x: A| 0<=start<=stop<=s.len() && #[trigger] s.subrange(start,stop).contains(x) implies 
            exists |i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x by {
        axiom_seq_subrange_elements(s, start, stop, x);
    }
    assert forall |s: Seq<A>, start: int, stop: int, x: A| exists |i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x 
            implies #[trigger] s.subrange(start,stop).contains(x) by {
        axiom_seq_subrange_elements(s, start, stop, x);
    }
    assert forall |s: Seq<A>, n: int, x: A| #[trigger] s.take(n).contains(x) 
            implies (exists |i: int| 0<= i < n && i < s.len() && #[trigger] s[i] == x) by {
        axiom_seq_take_contains(s, n, x);
    }
    assert forall |s: Seq<A>, n: int, x: A| (exists |i: int| 0<= i < n && i < s.len() && #[trigger] s[i] == x) 
            implies #[trigger] s.take(n).contains(x) by {
        axiom_seq_take_contains(s, n, x);
    }
    assert forall |s: Seq<A>, n: int, j: int| 0<= j < n <= s.len() implies #[trigger] s.take(n)[j] == s[j] by {
        axiom_seq_take_len(s,n);
        assert(0 <= n <= s.len() ==> s.take(n).len() == n);
        assert(0 <= n <= s.len());
        assert(s.take(n).len() == n);
        axiom_seq_take_index(s, n, j);
    }
    assert forall |s: Seq<A>, n: int, x: A| #[trigger] s.drop(n).contains(x) 
            implies (exists |i: int| 0<= i < s.len() && n <= i && #[trigger] s[i] == x) by {
        axiom_seq_drop_contains(s, n, x);
    }
    assert forall |s: Seq<A>, n: int, x: A| (exists |i: int| 0<= i < s.len() && n <= i && #[trigger] s[i] == x) 
            implies #[trigger] s.drop(n).contains(x) by {
        axiom_seq_drop_contains(s, n, x);
    }
    // assert forall |a: Seq<A>, b: Seq<A>, n: int| n == a.len() implies (#[trigger] (a+b).take(n) == a && #[trigger] (a+b).drop(n) == b) by {
    //     axiom_seq_append_take_drop(a, b, n);
    // }
    assert forall |s: Seq<A>, i: int, v: A, n: int| 0 <= i < n <= s.len() implies #[trigger] s.update(i,v).take(n) == s.take(n).update(i,v) by {
        axiom_seq_take_update_commut1(s, i, v, n);
    }
    assert forall |s: Seq<A>, i: int, v: A, n: int| 0 <= n <= i < s.len() implies #[trigger] s.update(i,v).take(n) == s.take(n) by {
        axiom_seq_take_update_commut2(s, i, v, n);
    }
    assert forall |s: Seq<A>, i: int, v: A, n: int| 0 <= n <= i < s.len() implies #[trigger] s.update(i,v).drop(n) == s.drop(n).update(i-n,v) by {
        axiom_seq_drop_update_commut1(s, i, v, n);
    }
    assert forall |s: Seq<A>, i: int, v: A, n: int|  0 <= i < n <= s.len() implies #[trigger] s.update(i,v).drop(n) == s.drop(n) by {
        axiom_seq_drop_update_commut2(s, i, v, n);
    }
    assert forall |s: Seq<A>, v: A, n: int| 0 <= n <= s.len() implies #[trigger] s.push(v).drop(n) == s.drop(n).push(v) by {
        axiom_seq_drop_build_commut(s, v, n);
    }
    assert forall |s: Seq<A>, n: int| n==0 implies #[trigger] s.drop(n) == s by {
        axiom_seq_drop_nothing(s, n);
    }
    assert forall |s: Seq<A>, n: int| n==0 implies #[trigger] s.take(n) == Seq::<A>::empty() by {
        axiom_seq_take_nothing(s, n);
    }
    assert forall |s: Seq<A>, m: int, n: int| (0 <= m && 0 <= n && m+n <= s.len()) implies s.drop(m).drop(n) == s.drop(m+n) by {
        axiom_seq_drop_of_drop(s, m, n);
    }
    assert forall |s: Seq<A>, i: int| 0 <= i < s.len() implies #[trigger] s.take(i).rank() < s.rank() by {
        axiom_seq_rank_take(s, i);
    }
    assert forall |s: Seq<A>, i: int|  0 < i <= s.len() implies #[trigger] s.drop(i).rank() < s.rank() by {
        axiom_seq_rank_drop(s, i);
    }
    assert forall |s: Seq<A>, i: int, j: int| 0 <= i < j <= s.len() implies #[trigger] (s.take(i) + s.drop(j)).rank() < s.rank() by {
        axiom_seq_rank_append_take_drop(s, i, j);
    }
}

#[doc(hidden)]
pub use seq_internal;
pub use seq;

} // verus!
