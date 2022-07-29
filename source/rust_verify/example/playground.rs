mod pervasive;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use pervasive::string::*;

verus! {
    use pervasive::string::*; 
    const GREETING: StrSlice<'static> = StrSlice::new("Hello World");
    const PARTIAL_GREETING: StrSlice<'static> = StrSlice::new("Hello");
    const OTHER_GREETING: StrSlice<'static> = new_strlit("Hello World!", true);

    fn string_lit<'a>() {
        GREETING.reveal();
        PARTIAL_GREETING.reveal();

        assert(GREETING.is_ascii());
        assert(PARTIAL_GREETING.is_ascii());
        let part = GREETING.substring(0, 5);
        assert(part.view().ext_equal(PARTIAL_GREETING.view()));
        assert(part.view() === PARTIAL_GREETING.view());
    }

    // fn str_1<'a>(s1: StrSlice<'a>, s2: StrSlice<'a>)
    //     requires
    //         s1.view() === s2.view(),
    //         s1.view().len() == 10,
    // {
    //     let a1 = s1.substring(3, 5);
    //     let a2 = s2.substring(3, 5);
    //     assert(a1.view() === a2.view());
    // }
}

fn main() {}

