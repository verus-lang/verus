use trace_var::trace_var;

fn main() {
    println!("{}", factorial(8));
}

#[trace_var(p, n)]
fn factorial(mut n: u64) -> u64 {
    let mut p = 1;
    while n > 1 {
        p *= n;
        n -= 1;
    }
    p
}
