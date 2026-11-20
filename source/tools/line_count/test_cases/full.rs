//! This test tries to use most of the verus syntax to test the line_counter
use vstd::prelude::*;

verus! {

/// How a dog barks
pub trait Barker {
    type Env;

    /// Whether bark obeys the spec (should be deterministic wrt the environment)
    spec fn obeys_bark_spec() -> bool;

    /// Specification of bark
    spec fn spec_bark(self, env: Self::Env) -> u64;

    /// Preconditions on bark
    spec fn bark_pre(self, env: Self::Env) -> bool;

    /// Returns the loudness of the bark
    fn bark(&self, env: &Self::Env) -> (r: u64)
        requires
            self.bark_pre(*env),
        ensures
            Self::obeys_bark_spec() ==> r == self.spec_bark(*env),
        ;
}

impl Barker for u64 {
    type Env = ();

    open spec fn obeys_bark_spec() -> bool {
        true
    }

    open spec fn spec_bark(self, env: Self::Env) -> u64 {
        self
    }

    open spec fn bark_pre(self, env: Self::Env) -> bool {
        true
    }

    fn bark(&self, env: &Self::Env) -> u64 {
        *self
    }
}

#[derive(PartialEq, Eq)]
pub struct Dog<B: Barker> {
    pub fur: bool,
    pub barker: B,
}

#[derive(PartialEq, Eq)]
pub enum Animal {
    Dog(Dog<u64>),
    Cat(bool),
    Mouse,
}

impl Animal {
    pub fn bark(&self) -> (r: u64)
        ensures
            r == self.spec_bark()
    {
        match self {
            Animal::Dog(d) => d.barker.bark(&()),
            _ => 0
        }
    }

    pub open spec fn spec_bark(self) -> u64 {
        match self {
            Animal::Dog(d) => d.barker.spec_bark(()),
            _ => 0
        }
    }
}

fn test_struct_1(p: u64) {
    let c1 = Dog { fur: true, barker: p };
    assert(c1.barker == p);
    assert((Dog { barker: p, fur: true }).barker == p);
    let bark = (Dog { barker: p, fur: true }).barker.bark(&());
    assert(bark == p);
    assert((Dog { barker: p, fur: true }).barker.spec_bark(()) == p);
}

fn test_structural_eq(barker: u64) {
    let d1 = Dog { barker, fur: true };
    let d2 = Dog { barker, fur: false };
    let d3 = Dog { barker, fur: true };
    assert(d1 == d3);
    assert(d1 != d2);
    let cat = Animal::Cat(true);
    let dog = Animal::Dog(d1);
    assert(cat != dog);
    let cat_bark = cat.bark();
    let dog_bark = dog.bark();
    assert(cat_bark == 0);
    assert(dog_bark == barker);
}

// Cats don't bark
proof fn equal_bark_means_dog_mute(dog: Animal, cat: Animal)
    requires
        dog is Dog,
        cat is Cat,
    ensures
        dog.spec_bark() == cat.spec_bark() ==> dog->Dog_0.barker == 0
{
    admit();
}

spec fn sum_3_barks<B: Barker>(b: B, env: B::Env) -> int {
    b.spec_bark(env) + b.spec_bark(env) + b.spec_bark(env)
}

pub broadcast axiom fn dog_louder_than_cat(cat: Animal, dog: Animal)
    requires
        cat is Cat,
        dog is Dog,
    ensures
        #[trigger] dog.spec_bark() >= #[trigger] cat.spec_bark()
;

fn main() {}

} // verus!
