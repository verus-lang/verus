#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;

/// sequence type for specifications
#[verifier(external_body)]
pub struct Seq<A> {
    dummy: std::marker::PhantomData<A>,
}

#[spec]
#[verifier(pub_abstract)]
pub fn seq_empty<A>() -> Seq<A> {
    arbitrary()
}

#[spec]
#[verifier(pub_abstract)]
pub fn seq_new<A, F: Fn(int) -> A>(len: nat, f: F) -> Seq<A> {
    arbitrary()
}

impl<A> Seq<A> {
    #[spec]
    #[verifier(pub_abstract)]
    pub fn len(self) -> nat {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn index(self, i: int) -> A {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn push(self, a: A) -> Seq<A> {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn update(self, i: int, a: A) -> Seq<A> {
        arbitrary()
    }

    #[spec]
    pub fn ext_equal(self, s2: Seq<A>) -> bool {
        self.len() == s2.len() &&
        forall(|i: int| 0 <= i && i < self.len() >>= equal(self.index(i), s2.index(i)))
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn subrange(self, start_inclusive: int, end_exclusive: int) -> Seq<A> {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn add(self, rhs: Seq<A>) -> Seq<A> {
        arbitrary()
    }
}

// Trusted axioms

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_empty<A>() {
    ensures(#[trigger] seq_empty::<A>().len() == 0);
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_new_len<A, F: Fn(int) -> A>(len: nat, f: F) {
    ensures(#[trigger] seq_new(len, f).len() == len);
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_new_index<A, F: Fn(int) -> A>(len: nat, f: F, i: int) {
    requires([
        0 <= i,
        i < len,
    ]);
    ensures(equal(seq_new(len, f).index(i), f(i)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_push_len<A>(s: Seq<A>, a: A) {
    ensures(#[trigger] s.push(a).len() == s.len() + 1);
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A) {
    ensures(equal(#[trigger] s.push(a).index(s.len()), a));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int) {
    requires([
        0 <= i,
        i < s.len(),
    ]);
    ensures(equal(s.push(a).index(i), s.index(i)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_update_len<A>(s: Seq<A>, i: int, a: A) {
    requires([
        0 <= i,
        i < s.len(),
    ]);
    ensures(#[trigger] s.update(i, a).len() == s.len());
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_update_same<A>(s: Seq<A>, i: int, a: A) {
    requires([
        0 <= i,
        i < s.len(),
    ]);
    ensures(equal(#[trigger] s.update(i, a).index(i), a));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A) {
    requires([
        0 <= i1,
        i1 < s.len(),
        0 <= i2,
        i2 < s.len(),
    ]);
    ensures(equal(s.update(i2, a).index(i1), s.index(i1)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>) {
    ensures(s1.ext_equal(s2) == equal(s1, s2));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_subrange_len<A>(s: Seq<A>, j: int, k: int) {
    requires([
        0 <= j,
        j <= k,
        k <= s.len(),
    ]);
    ensures(#[trigger] s.subrange(j, k).len() == k - j);
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int) {
    requires([
        0 <= j,
        j <= k,
        k <= s.len(),
        0 <= i,
        i < k - j,
    ]);
    ensures(equal(s.subrange(j, k).index(i), s.index(i + j)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>) {
    ensures(#[trigger] s1.add(s2).len() == s1.len() + s2.len());
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int) {
    requires([
        0 <= i,
        i < s1.len(),
    ]);
    ensures(equal(s1.add(s2).index(i), s1.index(i)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int) {
    requires([
        0 <= s1.len(),
        i < s1.len() as int + s2.len(),
    ]);
    ensures(equal(s1.add(s2).index(i), s2.index(i - s1.len())));
}

#[macro_export]
macro_rules! seq_insert_rec {
    [$val:expr;] => {
        $val
    };
    [$val:expr;$elem:expr] => {
        seq_insert_rec![$val.push($elem);]
    };
    [$val:expr;$elem:expr,$($tail:tt)*] => {
        seq_insert_rec![$val.push($elem);$($tail)*]
    }
}

#[macro_export]
macro_rules! seq {
    [$($tail:tt)*] => {
        seq_insert_rec![$crate::pervasive::seq::seq_empty();$($tail)*]
    }
}
