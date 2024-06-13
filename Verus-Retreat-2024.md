# Verus Retreat @ Secure Foundations Lab, CMU -- June 25-27 2024

We are organizing a retreat for people involved in the Verus project.
Bryan Parno (@parno) and the Secure Foundations Lab will be hosting the retreat at CMU during the week of June 24th.

We are planning 3 days of "official" semi-structured time (Tuesday the 25th through Thursday the 27th), but there will likely be informal meet-ups, discussion, and hacking the Monday before (6/24) and the Friday after (6/28).

Sessions will begin at 9:30 AM.  We will be meeting in the [Collaborative Innovation Center (CIC)](https://www.cylab.cmu.edu/about/visiting.html), room 2101.

## Potential Topics
- Overview of new/upcoming features 
- Issue triage
- Feature prioritization
- Documentation write-a-thon
- Experience reports building systems in Verus: What's working well and what isn't working
- Language design, planned changes, and discussion
- Proof stability
- Specifying and Verifying Rust's standard library 
- Verus and AI
- Syntactic suggestions (1 hour max)
- Benchmarking suite and CI
- Paper planning
- cvc5 integration
- Termination checking for `exec`

## Program

This is a tentative program.


### Tuesday, June 25th

*Experience reports building systems in Verus (~2 hours)*
- Each report should include:
   - What was built/verified
   - What Verus did well
   - What problems did you encounter and/or which features would have been useful?
- Systems:
   * Owl: Cryptographic protocol implementations (Pratap Singh)
   * Vest: Verified parser/serializer combinators (Yi Cai)
   * Anvil: Liveness of Kubernetes clusters (Xudong Sun)
   * Persistent storage (Hayley LeBlanc)
   * Atmosphere microkernel (Xiangdong Chen and Zhaofeng Li)

*Overview of new/upcoming features (~2 hours in the morning)*

- Iterators (Chris)
- Traits (Chris, Andrea)
- Mutable reference encoding (Andrea)
- Brief advertisements for `verusfmt`, `cargo verus`

*Feature request triage (1-2 hours in the afternoon)*

- E.g., termination checking for `exec`

*6:00 PM -- Collaboration Dinner at [Butterjoint](https://maps.app.goo.gl/wVz6SbFGEf9T58pQ7)*

### Wednesday, June 26th

- Documentation write-a-thon  (2-3 hours in the morning)

- Setting up CI that includes other Verus projects (a-la crater) (Andrea)

- Issue triage (1-2 hours in the afternoon)

- Verus and AI (1 hour in the afternoon)

- Hike in Frick Park (~2 hours in the late afternoon)

- Evening: Mini-golf outing

### Thursday, June 27th

- Brainstorming next big steps for Verus (1-2 hours in the morning)
    - Verifying the Rust standard library (Travis)

- cvc5 + SMT encoding

- Evening: Board games!