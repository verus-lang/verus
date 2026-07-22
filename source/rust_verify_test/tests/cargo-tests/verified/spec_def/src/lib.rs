use vstd::prelude::*;

trait Seal {}
#[allow(private_bounds)]
pub trait T: Seal {}
impl Seal for u8 {}
impl T for u8 {}

verus! {

trait VSeal {}
#[allow(private_bounds)]
pub trait VT: VSeal {}
impl VSeal for u8 {}
impl VT for u8 {}


// Spec function for use in verified functions
pub open spec fn double(x: u16) -> (z: int)
{
    x + x
}

pub fn concrete_a(x: u16) -> u16 
    requires double(x) < 100,
{
    x
}


} // verus!
