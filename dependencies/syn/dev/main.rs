syn_dev::r#mod! {
    // Write Rust code here and run `cargo check` to have Syn parse it.

    pub fn ref_mut_array_unsizing_coercion<T, const N: usize>(r: &mut [T; N]) -> (out: &mut [T])
    ensures
        out.view() === old(r).view(),
        final(out).view() === final(r).view(),
    opens_invariants none
    no_unwind
{
    r   
}
}
