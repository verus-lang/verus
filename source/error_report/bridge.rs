use vstd::prelude::*;

verus! {

enum NextCar {
    A,
    B,
    Both,
    Neither
}

#[derive(PartialEq, Eq, Structural)]
enum TrafficLight {
    Red,
    Green
}

impl TrafficLight {
    fn clone(&self) -> (res:Self)
        ensures
            res == *self
    {
        match self {
            TrafficLight::Red => TrafficLight::Red,
            TrafficLight::Green => TrafficLight::Green,
        }
    }
}

struct State {
    LightA : TrafficLight,
    LightB : TrafficLight,
    W_A : u64,
    W_B : u64,
    Cross_Counter : u64,
}

spec fn Valid(s : State) -> bool {
    &&& true
    &&& 0 <= s.W_A <= 1_0000_0000
    &&& 0 <= s.W_B <= 1_0000_0000
    // the two lights are never green at the same time
    &&& (s.LightA == TrafficLight::Red || s.LightB == TrafficLight::Red)
    // initial state
    &&& (s.LightA == TrafficLight::Red && s.LightB == TrafficLight::Red ==> s.Cross_Counter == 0)
    // cross counter always behave
    &&& 0 <= s.Cross_Counter <= 5
}

fn Init() -> (s:State)
    ensures Valid(s)
{
    State {
        LightA : TrafficLight::Red,
        LightB : TrafficLight::Red,
        W_A : 0,
        W_B : 0,
        Cross_Counter : 0,
    }
}

// state modification is done in place (imperative style), rather than
// the functional style dafny uses. We need to implment a bunch of clone
// traits if we want to do it otherwise.
fn Increment_W_A(s: &mut State)
    requires 
        Valid(*old(s)),
        old(s).W_A <= 9999_9999, // why dafny does not need this?
    ensures 
        Valid(*s),
        s.W_B == old(s).W_B,
        s.Cross_Counter == old(s).Cross_Counter,
        s.W_A == old(s).W_A + 1,
        s.LightA == old(s).LightA,
        s.LightB == old(s).LightB
{
    s.W_A = s.W_A + 1;
}

fn Increment_W_B(s: &mut State)
    requires 
        Valid(*old(s)),
        old(s).W_B <= 9999_9999 // why dafny does not need this?
    ensures 
        Valid(*s),
        s.Cross_Counter == old(s).Cross_Counter,
        s.W_A == old(s).W_A,
        s.W_B == old(s).W_B + 1,
        s.LightA == old(s).LightA,
        s.LightB == old(s).LightB
{
    s.W_B = s.W_B + 1;
}

fn Increment_Cross_Counter(s: &mut State)
    requires
        Valid(*old(s)),
        old(s).Cross_Counter <= 9999_9999,
        0 <= old(s).Cross_Counter <= 4,
        old(s).LightA == TrafficLight::Green || old(s).LightB == TrafficLight::Green
    ensures 
        Valid(*s),
        s.W_A == old(s).W_A,
        s.W_B == old(s).W_B,
        s.LightA == old(s).LightA,
        s.LightB == old(s).LightB,
{
    s.Cross_Counter = s.Cross_Counter + 1;
}

fn Reset_Cross_Counter(s: &mut State)
    requires Valid(*old(s))
    ensures 
        Valid(*s),
        s.Cross_Counter == 0,
        s.W_A == old(s).W_A,
        s.W_B == old(s).W_B,
        s.LightA == old(s).LightA,
        s.LightB == old(s).LightB
{
    s.Cross_Counter = 0;
}

fn Cross(s: &mut State)
    requires 
        Valid(*old(s)),
        old(s).W_A > 0 && old(s).W_B > 0, // added for underflow
        old(s).Cross_Counter <= 9999_9999,
        0 <= old(s).Cross_Counter <= 4,
        old(s).LightA == TrafficLight::Green || old(s).LightB == TrafficLight::Green
    ensures 
        Valid(*s),
        s.LightA == old(s).LightA,
        s.LightB == old(s).LightB,
{
    // the cross example might be good to explain shared reference

    // naive method will error
    // cannot move out of `s.LightA` which is behind a mutable reference

    // this is not supported by verus
    // let f = |s: &State| {
    //     s.LightA == TrafficLight::Green
    // };

    // old(s).LightA == TrafficLight::Green  makes the compiler panic

    // wanrs abonut shared reference
    // let s_lighta : &TrafficLight = &s.LightA;
    // if *s_lighta == TrafficLight::Green {

    // I ended up using clone
    let s_lighta : TrafficLight = s.LightA.clone();
    if s_lighta == TrafficLight::Green {
        s.W_A = s.W_A - 1;
        Increment_Cross_Counter(s);
    } else {
        s.W_B = s.W_B - 1;
        Increment_Cross_Counter(s);
    }
}

fn Switch_Lights(s: &mut State)
    requires 
        Valid(*old(s)),
        !(old(s).LightA == TrafficLight::Red && old(s).LightB == TrafficLight::Red)
    ensures 
        Valid(*s),
        s.W_A == old(s).W_A,
        s.W_B == old(s).W_B,
        s.LightA == TrafficLight::Green || s.LightB == TrafficLight::Green 
{
    let s_lighta : TrafficLight = s.LightA.clone();
    let s_lightb : TrafficLight = s.LightB.clone();
    // assert(s_lighta == s.LightA && s_lightb == s.LightB);
    
    if s_lighta == TrafficLight::Red {
        s.LightA = TrafficLight::Green;
    } else {
        s.LightA = TrafficLight::Red;
    }
    if s_lightb == TrafficLight::Red {
        s.LightB = TrafficLight::Green;
    } else {
        s.LightB = TrafficLight::Red;
    }
}

fn Tick(next:NextCar, s: &mut State)
    requires 
        Valid(*old(s)), 
        0 <= old(s).Cross_Counter <= 9999_9999, // this is only for overflow
        0 <= old(s).W_A <= 9999_9999,
        0 <= old(s).W_B <= 9999_9999
    ensures 
        Valid(*s),
        (old(s).LightA == TrafficLight::Red && old(s).LightB == TrafficLight::Red && next == NextCar::Both) ==> s.LightA == TrafficLight::Green
{
    
    match next {
        NextCar::A => { Increment_W_A(s); },
        NextCar::B => { Increment_W_B(s); },
        NextCar::Both => { Increment_W_A(s); Increment_W_B(s); },
        NextCar::Neither => {}
    }
    
    // assert((next == NextCar::Both) ==> (s.W_A > 0 && s.W_B > 0));

    // hmm, seems like s.W_A is not afraid to be directly called, maybe
    // because struct is on the heap?
    let light_a = s.LightA.clone();    
    let light_b = s.LightB.clone();
    // need to verify the clone method
    // assert(light_a == s.LightA && light_b == s.LightB);

    if ((s.W_A == 0) || (s.W_B == 0)) && !(s.W_A == 0 && s.W_B == 0){
        // Simple case
        Reset_Cross_Counter(s);
        if s.W_A > 0 {
            // assert (s.W_B == 0);
            if light_a == TrafficLight::Red {
                s.LightA = TrafficLight::Green;
                s.LightB = TrafficLight::Red;
            }
            s.W_A = s.W_A - 1;
            Increment_Cross_Counter(s);
        }
        // end of simple case
    } else if s.W_A > 0 || s.W_B > 0 {
        // Car waiting on both sides
        if light_a == TrafficLight::Red && light_b == TrafficLight::Red {
            // initial state, break the tie in favour of the A side
            s.LightA = TrafficLight::Green;
            s.W_A = s.W_A - 1;
            Increment_Cross_Counter(s);
        } else {
            if s.Cross_Counter < 5 {
                Cross(s);
            } else {
                Switch_Lights(s);
                Reset_Cross_Counter(s);
                Cross(s);
            }
        }
    }
}

}

fn main() {

}
