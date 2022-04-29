#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

impl<A> Seq<A> {
    #[spec] #[verifier(publish)]
    pub fn map<B, F: Fn(int, A) -> B>(self, f: F) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(i, self.index(i)))
    }

    // TODO is_sorted -- extract from summer_school e22
    #[spec] #[verifier(publish)]
    pub fn contains(self, needle: A) -> bool {
        exists(|i: nat| i<self.len() && equal(self.index(i), needle))
    }

    #[spec] #[verifier(publish)]
    pub fn drop_last(self) -> Seq<A> {
        recommends(self.len() >= 1);
        self.subrange(0, self.len() as int - 1)
    } 
}

/// Prove two sequences equal by extensionality. Usage is:
///
/// ```rust,ignore
/// assert_seqs_equal!(map1, map2);
/// ```
/// 
/// or,
/// 
/// ```rust,ignore
/// assert_seqs_equal!(seq1, seq2, i => {
///     // assuming that i is in-bounds for the sequences
///     // prove that seq1[i] == seq2[i]
/// });
/// ```

#[macro_export]
macro_rules! assert_seqs_equal {
    ($s1:expr, $s2:expr) => {
        assert_seqs_equal!($s1, $s2, idx => { })
    };
    ($s1:expr, $s2:expr, $idx:ident => $bblock:block) => {
        let s1 = $s1;
        let s2 = $s2;
        ::builtin::assert_by(::builtin::equal(s1, s2), {
            $crate::pervasive::assert(s1.len() == s2.len());
            ::builtin::assert_forall_by(|$idx : ::builtin::int| {
                ::builtin::requires(0 <= $idx && $idx < s1.len());
                ::builtin::ensures(::builtin::equal(s1.index($idx), s2.index($idx)));
                { $bblock }
            });
            $crate::pervasive::assert(s1.ext_equal(s2));
        });
    }
}
