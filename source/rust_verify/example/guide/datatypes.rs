#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: point
struct Point {
    x: int,
    y: int,
}
// ANCHOR_END: point

// ANCHOR: point-impl
impl Point {
    spec fn len2(&self) -> int {
        self.x * self.x + self.y * self.y
    }
}

fn rotate_90(p: Point) -> (o: Point)
    ensures o.len2() == p.len2()
{
    let o = Point { x: -p.y, y: p.x };
    assert((-p.y) * (-p.y) == p.y * p.y) by(nonlinear_arith);
    o
}
// ANCHOR_END: point-impl

// ANCHOR: beverage
enum Beverage {
    Coffee { creamers: nat, sugar: bool },
    Soda { flavor: Syrup },
    Water { ice: bool },
}
// ANCHOR_END: beverage

// ANCHOR: syrup
enum Syrup {
    Cola,
    RootBeer,
    Orange,
    LemonLime,
}
// ANCHOR_END: syrup

struct Dessert {}
impl Dessert {
    fn new() -> Dessert {
        Dessert {}
    }
}

// ANCHOR: make_float
fn make_float(bev: Beverage) -> Dessert
    requires bev is Soda
{
    Dessert::new(/*...*/)
}
// ANCHOR_END: make_float

// ANCHOR: count_creamers
proof fn sufficiently_creamy(bev: Beverage) -> bool
    requires bev is Coffee
{
   bev->creamers >= 2
}
// ANCHOR_END: count_creamers

// ANCHOR: life
enum Life {
    Mammal { legs: int, has_pocket: bool },
    Arthropod { legs: int, wings: int },
    Plant { leaves: int },
}

spec fn is_insect(l: Life) -> bool
{
    l is Arthropod && l->Arthropod_legs == 6
}
// ANCHOR_END: life

// ANCHOR: shape
enum Shape {
    Circle(int),
    Rect(int, int),
}

spec fn area_2(s: Shape) -> int {
    match s {
        Shape::Circle(radius) => { radius * radius * 3 },
        Shape::Rect(width, height) => { width * height }
    }
}
// ANCHOR_END: shape

// ANCHOR: rect_height
spec fn rect_height(s: Shape) -> int
    recommends s is Rect
{
    s->1
}
// ANCHOR_END: rect_height

// ANCHOR: cuddly
use Life::*;
spec fn cuddly(l: Life) -> bool {
    ||| l matches Mammal { legs, .. } && legs == 4
    ||| l matches Arthropod { legs, wings } && legs == 8 && wings == 0
}
// ANCHOR_END: cuddly

// ANCHOR: kangaroo
spec fn is_kangaroo(l: Life) -> bool {
    &&& l matches Life::Mammal { legs, has_pocket }
    &&& legs == 2
    &&& has_pocket
}

spec fn walks_upright(l: Life) -> bool {
    l matches Life::Mammal { legs, .. } ==> legs == 2
}
// ANCHOR_END: kangaroo

fn main() {
}

} // verus!
