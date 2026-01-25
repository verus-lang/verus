use spec_use::*;

pub fn test_calling(x: u16) {
    let y = concrete_b(x);
    let z = concrete_caller(y);
    println!("{}", z);
}
