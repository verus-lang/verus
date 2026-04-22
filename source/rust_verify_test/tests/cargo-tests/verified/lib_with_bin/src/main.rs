use lib_with_bin::double;

fn main() {
    let result = double(21);
    assert!(result == 42);
    println!("double(21) = {}", result);
}
