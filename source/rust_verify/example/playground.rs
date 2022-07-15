mod pervasive;
use pervasive::string::StrSlice;


const GREETING: StrSlice<'static> = StrSlice::new("Hello World");
fn myconstfn() {
    let _:() = GREETING.reveal();
}

fn main() {}

