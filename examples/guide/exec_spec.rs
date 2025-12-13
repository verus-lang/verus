// ANCHOR: example
use vstd::prelude::*;
use vstd::contrib::exec_spec::*;

verus! {

exec_spec! {

struct Point {
    x: i64,
    y: i64,
}

spec fn on_line(points: Seq<Point>) -> bool {
    forall |i: usize| #![auto] 0 <= i < points.len()
        ==> points[i as int].y == points[i as int].x
}

}

}
// ANCHOR_END: example

// ANCHOR: check
verus! {
    fn main() {
        let p1 = ExecPoint { x: 1, y: 1 };
        let p2 = ExecPoint { x: 2, y: 2 };
        let points = vec![p1, p2];
        assert(on_line(points.deep_view()));
        let b = exec_on_line(points.as_slice());
        assert(b);
    }
}
// ANCHOR_END: check
