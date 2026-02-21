#![allow(unused_imports)]

use super::pervasive::*;
use super::prelude::*;

verus! {

pub trait Predicate<V> {
    spec fn predicate(&self, v: V) -> bool;
}

impl<V> Predicate<V> for spec_fn(V) -> bool {
    open spec fn predicate(&self, v: V) -> bool {
        self(v)
    }
}

} // verus!
