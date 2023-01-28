#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

verus! {

impl<A> Seq<A> {
    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    /// The `int` parameter of `f` is the index of the element being mapped.

    pub open spec fn map<B>(self, f: FnSpec(int, A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(i, self[i]))
    }

    // TODO is_sorted -- extract from summer_school e22
    pub open spec fn contains(self, needle: A) -> bool {
        exists|i: int| 0 <= i < self.len() && self[i] == needle
    }

    pub open spec fn index_of(self, needle: A) -> int {
        choose|i: int| 0 <= i < self.len() && self[i] == needle
    }

    /// Drops the last element of a sequence and returns a sequence whose length is
    /// thereby 1 smaller.
    ///
    /// If the input sequence is empty, the result is meaningless and arbitrary.

    pub open spec fn drop_last(self) -> Seq<A>
        recommends self.len() >= 1
    {
        self.subrange(0, self.len() as int - 1)
    } 
}

#[doc(hidden)]
#[verifier(inline)]
pub open spec fn check_argument_is_seq<A>(s: Seq<A>) -> Seq<A> { s }

/// Prove two sequences `s1` and `s2` are equal by proving that their elements are equal at each index.
///
/// More precisely, `assert_seqs_equal!` requires:
///  * `s1` and `s2` have the same length (`s1.len() == s2.len()`), and
///  * for all `i` in the range `0 <= i < s1.len()`, we have `s1[i] == s2[i]`.
///
/// The property that equality follows from these facts is often called _extensionality_.
///
/// `assert_seqs_equal!` can handle many trivial-looking
/// identities without any additional help:
///
/// ```rust
/// proof fn subrange_concat(s: Seq<u64>, i: int) {
///     requires([
///         0 <= i && i <= s.len(),
///     ]);
/// 
///     let t1 = s.subrange(0, i);
///     let t2 = s.subrange(i, s.len());
///     let t = t1.add(t2);
/// 
///     assert_seqs_equal!(s, t);
/// 
///     assert(s == t);
/// }
/// ```
///
/// In more complex cases, a proof may be required for the equality of each element pair.
/// For example,
/// 
/// ```rust
/// proof fn bitvector_seqs() {
///     let s = Seq::<u64>::new(5, |i| i as u64);
///     let t = Seq::<u64>::new(5, |i| i as u64 | 0);
/// 
///     assert_seqs_equal!(s, t, i => {
///         // Need to show that s[i] == t[i]
///         // Prove that the elements are equal by appealing to a bitvector solver:
///         let j = i as u64;
///         assert_bit_vector(j | 0 == j);
///         assert(s[i] == t[i]);
///     });
/// }
/// ```

#[macro_export]
macro_rules! assert_seqs_equal {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::pervasive::seq_lib::assert_seqs_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_seqs_equal_internal {
    ($s1:expr, $s2:expr $(,)?) => {
        assert_seqs_equal_internal!($s1, $s2, idx => { })
    };
    ($s1:expr, $s2:expr, $idx:ident => $bblock:block) => {
        #[spec] let s1 = $crate::pervasive::seq_lib::check_argument_is_seq($s1);
        #[spec] let s2 = $crate::pervasive::seq_lib::check_argument_is_seq($s2);
        ::builtin::assert_by(::builtin::equal(s1, s2), {
            $crate::pervasive::assert(s1.len() == s2.len());
            ::builtin::assert_forall_by(|$idx : ::builtin::int| {
                ::builtin::requires(::builtin_macros::verus_proof_expr!(0 <= $idx && $idx < s1.len()));
                ::builtin::ensures(::builtin::equal(s1.index($idx), s2.index($idx)));
                { $bblock }
            });
            $crate::pervasive::assert(s1.ext_equal(s2));
        });
    }
}

#[doc(hidden)]
pub use assert_seqs_equal_internal;
pub use assert_seqs_equal;

} // verus!
