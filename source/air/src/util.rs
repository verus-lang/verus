#[allow(dead_code)]
pub fn box_slice_map<A, B, F: Fn(&A) -> B>(slice: &[A], f: F) -> Box<[B]> {
    slice.iter().map(f).collect::<Vec<B>>().into_boxed_slice()
}
