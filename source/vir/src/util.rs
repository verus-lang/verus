pub fn box_slice_map<A, B, F: FnMut(&A) -> B>(slice: &[A], f: F) -> Box<[B]> {
    slice.iter().map(f).collect::<Vec<B>>().into_boxed_slice()
}

pub fn box_slice_map_result<A, B, C, F>(slice: &[A], f: F) -> Result<Box<[B]>, C>
where
    F: Fn(&A) -> Result<B, C>,
{
    Ok(slice.iter().map(f).collect::<Result<Vec<B>, C>>()?.into_boxed_slice())
}
