pub(crate) fn vec_map<A, B, F: Fn(&A) -> B>(v: &Vec<A>, f: F) -> Vec<B> {
    v.iter().map(f).collect::<Vec<B>>()
}
