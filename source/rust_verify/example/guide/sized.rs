#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {
    // ANCHOR: sized_foo 
    #[repr(C)]
    struct Foo {
        a: u32,
        b: u64,
    }

    global size_of Foo == 16;
    // ANCHOR_END: sized_foo
    
    /*
    // ANCHOR: layout_foo
    global layout Foo is size == 16, align == 8;
    // ANCHOR_END: layout_foo
    */
    
    /*
    // ANCHOR: sized_check
    #[repr(C)]
    struct Bar {
        c: u32,
        d: u64
    }

    fn check_size() {
        assert(core::mem::size_of::<Foo>() == 16); // succeeds; Foo's size was set above
        assert(core::mem::size_of::<Bar>() == 16); // fails; the size of Bar has not been set
    }
    */

    // ANCHOR_END: sized_check
}