// A port of `knights_tour_creusot.rs` from Creusot annotations to Verus.
// https://github.com/creusot-rs/creusot/blob/bef58f6aa7493ac8c8012164a8eeab462c346d1a/tests/should_succeed/vector/06_knights_tour.rs

use vstd::prelude::*;
use vstd::std_specs::iter::*;
use vstd::std_specs::range::*;

verus! {

#[derive(Copy, Clone)]
struct Point {
    pub x: isize,
    pub y: isize,
}

impl Point {
    fn mov(&self, p: &(isize, isize)) -> (result: Self)
        requires
            -10000 <= self.x@ <= 10000,
            -10000 <= self.y@ <= 10000,
            -10000 <= p.0@ <= 10000,
            -10000 <= p.1@ <= 10000,
        ensures
            result.x@ == self.x@ + p.0@,
            result.y@ == self.y@ + p.1@,
    {
        Self { x: (self.x + p.0), y: (self.y + p.1) }
    }
}

pub struct Board {
    pub size: usize,
    pub field: Vec<Vec<usize>>,
}

impl Board {
    spec fn wf(self) -> bool {
        &&& self.size@ <= 1_000
        &&& self.field@.len() == self.size@
        &&& forall|i: int| 0 <= i < self.size@ ==> (#[trigger] self.field[i]@).len() == self.size@
    }

    fn new(size: usize) -> (result: Self)
        requires
            size@ <= 1000,
        ensures
            result.size == size,
            result.wf(),
    {
        let rows: Vec<Vec<usize>> = (0..size).map(
            |_x: usize| -> (r: Vec<usize>)
                ensures r@.len() == size@
            { vec![0; size] },
        ).collect();
        Self { size, field: rows }
    }

    fn available(&self, p: Point) -> (result: bool)
        requires
            self.wf(),
        ensures
            result ==> self.in_bounds(p),
    {
        0 <= p.x
            && (p.x as usize) < self.size
            && 0 <= p.y
            && (p.y as usize) < self.size
            && self.field[p.x as usize][p.y as usize] == 0
    }

    spec fn in_bounds(self, p: Point) -> bool {
        0 <= p.x@ && p.x@ < self.size@ && 0 <= p.y@ && p.y@ < self.size@
    }

    // calculate the number of possible moves
    fn count_degree(&self, p: Point) -> usize
        requires
            self.wf(),
            self.in_bounds(p),
    {
        let mut count = 0;

        for m in it: moves()
            invariant
                self.wf(),
                self.in_bounds(p),
                it.seq().len() == 8,
                count <= it.index(),
                forall|i: int| 0 <= i < it.seq().len() ==>
                    -2 <= (#[trigger] it.seq()[i]).0@ <= 2 && -2 <= it.seq()[i].1@ <= 2,
        {
            let next = p.mov(&m);
            if self.available(next) {
                count += 1;
            }
        }
        count
    }

    fn set(&mut self, p: Point, v: usize)
        requires
            old(self).wf(),
            old(self).in_bounds(p),
        ensures
            final(self).wf(),
            final(self).size == old(self).size,
    {
        self.field[p.x as usize][p.y as usize] = v
    }
}

// Creusot assumes this.  We prove it.
fn moves() -> (result: Vec<(isize, isize)>)
    ensures
        result@.len() == 8,
        forall|i: int| 0 <= i < 8 ==>
            -2 <= (#[trigger] result[i]).0@ <= 2 && -2 <= result[i].1@ <= 2,
{
    let mut v = Vec::new();
    v.push((2, 1));
    v.push((1, 2));
    v.push((-1, 2));
    v.push((-2, 1));
    v.push((-2, -1));
    v.push((-1, -2));
    v.push((1, -2));
    v.push((2, -1));
    v
}

fn min(v: &Vec<(usize, Point)>) -> (result: Option<&(usize, Point)>)
    ensures
        forall|r: &(usize, Point)| result == Some(r) ==>
            exists|i: int| 0 <= i < v@.len() && v[i] == *r,
{
    let mut min = None;
    for x in it: v
        invariant
            it.seq().len() == v@.len(),
            forall|k: int| 0 <= k < it.seq().len() ==> *(#[trigger] it.seq()[k]) == v@[k],
            forall|r: &(usize, Point)| min == Some(r) ==>
                exists|i: int| 0 <= i < v@.len() && v[i] == *r,
    {
        match min {
            None => min = Some(x),
            Some(m) => {
                if x.0 < m.0 {
                    min = Some(x)
                }
            }
        };
    }
    min
}

// Unclear why Creusot factored this out
proof fn dumb_nonlinear_arith(a: usize)
    requires
        a@ <= 1_000,
    ensures
        a@ * a@ <= 1_000_000,
{
    assert(a@ * a@ <= 1_000_000) by (nonlinear_arith)
        requires a@ <= 1_000;
}

pub fn knights_tour(size: usize, x: usize, y: usize) -> Option<Board>
    requires
        1 < size@ <= 1000,
        x < size,
        y < size,
{
    broadcast use group_range_axioms;

    let mut board = Board::new(size);
    let mut p = Point { x: x as isize, y: y as isize };
    board.set(p, 1);

    proof {
        dumb_nonlinear_arith(size);
        assert(2 <= size * size) by (nonlinear_arith)
            requires 2 <= size@;
    }
    for step in 2..(size * size)
        invariant
            board.size == size,
            board.wf(),
            board.in_bounds(p),
    {
        // choose next square by Warnsdorf's rule
        let mut candidates: Vec<(usize, Point)> = Vec::new();
        for m in it: moves()
            invariant
                board.wf(),
                board.size == size,
                board.in_bounds(p),
                it.seq().len() == 8,
                forall|i: int| 0 <= i < it.seq().len() ==>
                    -2 <= (#[trigger] it.seq()[i]).0@ <= 2 && -2 <= it.seq()[i].1@ <= 2,
                forall|i: int| 0 <= i < candidates@.len() ==>
                    board.in_bounds(#[trigger] candidates[i].1),
        {
            let adj = p.mov(&m);
            if board.available(adj) {
                let degree = board.count_degree(adj);
                candidates.push((degree, adj));
            }
        }
        match min(&candidates) {
            Some(pair) => p = pair.1,
            None => return None,
        };
        board.set(p, step);
    }
    Some(board)
}

fn main() {}

} // verus!
