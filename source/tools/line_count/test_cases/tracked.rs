use vstd::prelude::*;
use vstd::atomic::*;

verus! {

fn foo(Tracked(perm): Tracked<&PermissionU32>, x: u32) {
}

fn bar(x: u32, Tracked(perm): Tracked<&PermissionU32>) {
}

fn baz(
    Tracked(perm1): Tracked<&PermissionU32>,
    x: u32,
    Tracked(perm2): Tracked<&PermissionU32>,
    y: u32,
) {
}

fn tracked_args() {
    let (a, Tracked(p)) = PAtomicU32::new(0);
    let y = a.load(Tracked(&p));
    foo(Tracked(&p), 4);
    bar(4, Tracked(&p));
    baz(
        Tracked(&p),
        4,
        Tracked(&p),
        y,
    );
}

// Tracked parameter, with the body's opening brace on a separate line
fn tracked_param_brace_separate(Tracked(perm): Tracked<&PermissionU32>, x: u32)
    requires
        x > 0,
{
}

// Tracked struct fields
struct Wrapper {
    perm: Tracked<PermissionU32>,
    x: u32,
}

// Tracked struct fields sharing a line with exec fields
struct OneLineWrapper { x: u32, perm: Tracked<PermissionU32> }

struct OneLineWrapperTrackedFirst { perm: Tracked<PermissionU32>, x: u32 }

struct TupleWrapper(Tracked<PermissionU32>, u32);

enum TrackedEnum {
    A(Tracked<PermissionU32>, u32),
    B { perm: Tracked<PermissionU32>, x: u32 },
}

// Tracked return types
fn ret_named() -> (t: Tracked<PermissionU32>) {
    let (a, Tracked(p)) = PAtomicU32::new(0);
    Tracked(p)
}

fn ret_unnamed() -> Tracked<PermissionU32> {
    let (a, Tracked(p)) = PAtomicU32::new(0);
    // below is counted as Proof Exec -- after ghost erasure, would still have return;
    return Tracked(p); 
}

#[verifier::external_body]
fn ret_tup() -> ((Tracked<PermissionU32>, Tracked<PermissionU32>)) {
    (Tracked::assume_new(), Tracked::assume_new())
}

// Variable bindings with Tracked or tracked
fn tracked_bindings() {
    let (a, Tracked(p1)) = PAtomicU32::new(0);
    let (b, Tracked(p2)) = PAtomicU32::new(0);
    let (c, Tracked(p3)) = PAtomicU32::new(0);
    let tracked q1 = p1;
    let t1 = Tracked(q1);
    let Tracked(q1) = t1;
    let w = Wrapper { perm: Tracked(q1), x: 1 };
    let y = Wrapper {
        perm: Tracked(p2),
        x: 1
    };
    let o = Some(Tracked(p3));
    let (Tracked(v1), Tracked(v2)) = ret_tup();
}

// Tracked nested inside other types
struct OptWrapper {
    opt: Option<Tracked<PermissionU32>>,
}

fn nested_param(o: Option<Tracked<&PermissionU32>>) {
}

fn nested_ret() -> (t: Option<Tracked<PermissionU32>>) {
    let v: Vec<Tracked<PermissionU32>> = Vec::new();
    None
}

} // verus!
