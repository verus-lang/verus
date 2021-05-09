pub fn admit() {
    unimplemented!();
}

// Can only appear at beginning of function body
pub fn requires<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
pub fn ensures<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of loop body
pub fn invariant<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
pub fn decreases<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
pub fn hide<F>(_f: F) {
    unimplemented!();
}

pub fn reveal<F>(_f: F) {
    unimplemented!();
}

pub fn reveal_with_fuel<F>(_f: F, _n: u32) {
    unimplemented!();
}

pub fn imply(_b1: bool, _b2: bool) -> bool {
    unimplemented!();
}

pub fn forall<A>(_a: A) -> bool {
    unimplemented!();
}

pub fn exists<A>(_a: A) -> bool {
    unimplemented!();
}

#[allow(non_camel_case_types)]
pub struct int;

impl std::ops::Add for int {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Sub for int {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Mul for int {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Neg for int {
    type Output = Self;
    fn neg(self) -> Self::Output {
        unimplemented!()
    }
}

impl PartialEq for int {
    fn eq(&self, _other: &Self) -> bool {
        unimplemented!()
    }
}

impl Eq for int {}

impl std::cmp::PartialOrd for int {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        unimplemented!()
    }
}

impl std::cmp::Ord for int {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        unimplemented!()
    }
}

#[allow(non_camel_case_types)]
pub struct nat;

impl std::ops::Add for nat {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Sub for nat {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Mul for nat {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl PartialEq for nat {
    fn eq(&self, _other: &Self) -> bool {
        unimplemented!()
    }
}

impl Eq for nat {}

impl std::cmp::PartialOrd for nat {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        unimplemented!()
    }
}

impl std::cmp::Ord for nat {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        unimplemented!()
    }
}
