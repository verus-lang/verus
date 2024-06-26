# Verus Retreat @ Secure Foundations Lab, CMU -- June 25-27 2024

We are organizing a retreat for people involved in the Verus project.
Bryan Parno (@parno) and the Secure Foundations Lab will be hosting the retreat at CMU during the week of June 24th.

We are planning 3 days of "official" semi-structured time (Tuesday the 25th through Thursday the 27th), but there will likely be informal meet-ups, discussion, and hacking the Monday before (6/24) and the Friday after (6/28).

Sessions will begin at 9:30 AM.  We will be meeting in the [Collaborative Innovation Center (CIC)](https://www.cylab.cmu.edu/about/visiting.html), room 2101.

---

# The up-to-date-agenda is in a separate document during the event

# If you would like access, email andrea@lattuada.me


---

## Additional Potential Topics
- Proof stability
- Syntactic suggestions (1 hour max)

## Program

This is a tentative program.


### Tuesday, June 25th

*Experience reports building systems in Verus (2-3 hours)*
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
   * Concurrent page table implementation (Matthias Brun, Johanna Polzin)
   * VeriSplinter (Jon Howell)

*Overview of new/upcoming features (~1.5 hours in the morning/early afternoon)*

- Iterators (Chris)
- Traits (Chris, Andrea)
- Broadcast groups (Andrea)
- Mutable reference encoding (Andrea)
- Brief advertisements for new tooling:
   - `verusfmt` (Jay Bosamiya)
   - `cargo verus` 
   - Verus find (Matthias Brun)
   - HumanEval in Verus (Bryan Parno)

*Feature request triage (1-2 hours in the afternoon)*

- Examples:
   - Termination checking for `exec`
   - [`From` and `Into` traits](https://github.com/verus-lang/verus/discussions/1129#discussioncomment-9492707)
   - [Vector literals](https://github.com/verus-lang/verus/discussions/1129#discussioncomment-9492710)
   - vstd functions for [(debug) printing](https://github.com/verus-lang/verus/discussions/1129#discussioncomment-9736972)
   - Support for [dyn](https://github.com/verus-lang/verus/discussions/1047)
   - [Type invariants](https://github.com/verus-lang/verus/discussions/962)
   - Separating and identifying [trusted vs. untrusted code](https://github.com/verus-lang/verus/discussions/112)
   - Ensures clauses for spec functions

*6:30 PM -- Collaboration Dinner at [Butterjoint](https://maps.app.goo.gl/wVz6SbFGEf9T58pQ7)*

### Wednesday, June 26th

- Documentation write-a-thon  (2-3 hours in the morning)
  - +Wiki updates

- Setting up CI that includes other Verus projects (a-la crater) (Andrea)

- State machine syntax brainstorming (Travis, Andrea, Jialin, Jon, Matthias, Johanna, ...)

- Adopt an issue (1-2 hours in the afternoon)

- Verus and AI (1 hour in the afternoon)

- Hike in Frick Park (~2 hours in the late afternoon)

- Evening: Mini-golf outing

### Thursday, June 27th

- Brainstorming next big steps for Verus (1-2 hours in the morning)
    - Verifying the Rust standard library (Travis)

- cvc5 + SMT encoding (1-1.5 hours in the morning)

- 11:15 AM: *Retreat Photograph* 

- Feature design discussion (afternoon)
  - Lean integration
  - Attaching specifications to standard library with traits, e.g., `HashMap<Key: View>`

- Evening: Board games!

### Friday, June 28th (optional)

- Internal issue triage