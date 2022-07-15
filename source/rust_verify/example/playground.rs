mod pervasive;
use pervasive::string::StrSlice;


const GREETING: StrSlice<'static> = StrSlice::new("Hello World");
fn myconstfn() {
    GREETING.reveal();
}

fn main() {}

