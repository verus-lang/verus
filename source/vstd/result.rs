#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

#[is_variant]
pub enum Result<T, E> {
    Ok(T),
    Err(E)
}
