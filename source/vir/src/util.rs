pub(crate) fn vec_map<A, B, F: Fn(&A) -> B>(v: &Vec<A>, f: F) -> Vec<B> {
    v.iter().map(f).collect::<Vec<B>>()
}

pub(crate) fn vec_map_result<A, B, C, F>(v: &Vec<A>, f: F) -> Result<Vec<B>, C>
where
    F: FnMut(&A) -> Result<B, C>,
{
    v.iter().map(f).collect::<Result<Vec<B>, C>>()
}
