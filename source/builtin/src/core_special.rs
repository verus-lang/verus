use crate::verus_builtin::Tracked;

#[rustc_const_unstable(feature = "const_convert", issue = "143773")]
#[cfg(all(verus_keep_ghost, verus_verify_core))]
impl<A> const core::ops::Deref for Tracked<A> {
    type Target = A;
    fn deref(&self) -> &Self::Target {
        unimplemented!();
    }
}

#[rustc_const_unstable(feature = "const_convert", issue = "143773")]
#[cfg(all(verus_keep_ghost, verus_verify_core))]
impl<A> const core::ops::DerefMut for Tracked<A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unimplemented!();
    }
}
