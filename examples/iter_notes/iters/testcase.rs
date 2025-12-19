use vstd::prelude::*;

verus! {

fn test() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = Vec::new();

    for x in y: v 
        invariant
            w.len() as int == y.index@,
            forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i],
            //forall |i| 0 <= i < w.len() ==> w[i] == v[i],
    {
        w.push(x);
    }
    assert(w.len() == v.len());
    assert(w@ == v@);
}

}

fn main() {}
