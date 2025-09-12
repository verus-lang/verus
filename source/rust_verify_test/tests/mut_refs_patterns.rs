use vstd::prelude::*;

verus!{

struct Foo(u64);

fn test_foo(o: Foo, orig: Foo) {
    assume(orig == o);

    let mut o = o;
    let mut o_ref = &mut o;
    match o_ref {
        Foo(i) => {
            assert(orig == Foo(*i));

            *i = 20;
        }
    }

    assert(o === Foo(20));
}

fn test_foo_fails(o: Foo, orig: Foo) {
    assume(orig == o);

    let mut o = o;
    let mut o_ref = &mut o;
    match o_ref {
        Foo(i) => {
            *i = 20;
        }
    }

    assert(false); // FAILS
}

fn test_opt(o: Option<u64>, orig: Option<u64>) {
    assume(orig == o);

    let mut o = o;
    let mut o_ref = &mut o;
    match o_ref {
        Some(i) => {
            assert(orig == Some(*i));

            *i = 20;
        }
        None => {
        }
    }

    assert(orig is None ==> o is None);
    assert(orig is Some ==> o === Some(20));
}

fn test_opt_fails1(o: Option<u64>, orig: Option<u64>) {
    assume(orig == o);

    let mut o = o;
    let mut o_ref = &mut o;
    match o_ref {
        Some(i) => {
            assert(orig == Some(*i));

            *i = 20;
        }
        None => {
        }
    }

    assert(orig is None ==> o is None);
    assert(orig is Some ==> o === Some(20));

    assert(o is Some); // FAILS
    assert(o is None); // FAILS
}

fn test_explicit_ref_mut(o: Option<u64>, orig: Option<u64>) {
    assume(orig == o);

    let mut o = o;
    match o {
        Some(ref mut i) => {
            assert(orig == Some(*i));

            *i = 20;
        }
        None => {
        }
    }

    assert(orig is None ==> o is None);
    assert(orig is Some ==> o === Some(20));

    assert(o is Some); // FAILS
    assert(o is None); // FAILS
}

fn test_explicit_redundant_ref_mut(o: Option<u64>, orig: Option<u64>) {
    assume(orig == o);

    let mut o = o;
    let mut o_ref = &mut o;
    match o_ref {
        // The ref mut here doesn't have any effect because o_ref is already a mutable borrow
        Some(ref mut i) => {
            assert(orig == Some(*i));

            *i = 20;
        }
        None => {
        }
    }

    assert(orig is None ==> o is None);
    assert(orig is Some ==> o === Some(20));

    assert(o is Some); // FAILS
    assert(o is None); // FAILS
}


fn test_mut_mut(o: Option<u64>, orig: Option<u64>) {
    assume(orig == o);

    let mut o = o;
    let mut o_ref = &mut o;
    let mut o_ref_ref = &mut o_ref;
    match o_ref {
        Some(i) => {
            assert(orig == Some(*i));

            *i = 20;
        }
        None => {
        }
    }

    assert(orig is None ==> o is None);
    assert(orig is Some ==> o === Some(20));

    assert(o is Some); // FAILS
    assert(o is None); // FAILS
}

fn test_ref_mut_binder_copy_in_subpat(o: Option<u64>, orig: Option<u64>) {
    assume(orig == o);

    let mut o = o;
    match o {
        ref mut opt @ Some(i) => {
            assert(orig == Some(i));
            assert(*opt == orig);

            *opt = None;
        }
        None => {
        }
    }

    assert(o is None);
}


fn test_ref_mut_binder_copy_in_subpat_fails(o: Option<u64>, orig: Option<u64>) {
    assume(orig == o);

    let mut o = o;
    match o {
        ref mut opt @ Some(i) => {
            assert(orig == Some(i));
            assert(*opt == orig);

            *opt = None;
        }
        None => {
        }
    }

    assert(o is None);
    
    assert(orig is None); // FAILS
    assert(orig is Some); // FAILS
}


fn test_ref_mut_binder_copy_in_subpat_nested(o: Option<Option<u64>>, orig: Option<Option<u64>>)
    requires (match o {
        Some(Some(x)) => x < 5,
        _ => true,
    })
{
    assume(orig == o);

    let mut o = o;
    match o {
        Some(ref mut opt @ Some(i)) => {
            *opt = Some(i + 1);
        }
        Some(ref mut opt @ None) => {
            *opt = Some(0);
        }
        None => {
        }
    }

    assert(o === match orig {
        Some(Some(x)) => Some(Some((x+1) as u64)),
        Some(None) => Some(Some(0)),
        None => None,
    });
}

fn test_ref_mut_binder_copy_in_subpat_nested_fails(o: Option<Option<u64>>, orig: Option<Option<u64>>)
    requires (match o {
        Some(Some(x)) => x < 5,
        _ => true,
    })
{
    assume(orig == o);

    let mut o = o;
    match o {
        Some(ref mut opt @ Some(i)) => {
            *opt = Some(i + 1);
        }
        Some(ref mut opt @ None) => {
            *opt = Some(0);
        }
        None => {
        }
    }

    assert(o === match orig {
        Some(Some(x)) => Some(Some((x+1) as u64)),
        Some(None) => Some(Some(0)),
        None => None,
    });
    assert(false); // FAILS
}

enum BigEnum<'a, 'b, 'c> {
    A((&'a mut Box<&'b mut u64>, &'c mut u64)),
    B(&'c mut u64)
}

fn test_big_enum(o: BigEnum, orig: BigEnum) {
    let mut o = o;
}


}

