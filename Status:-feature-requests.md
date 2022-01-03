This document tracks paper-cuts and other usability issues that are not critical at this stage, but we would like to record for the future.

## Modes

* Default a variable's mode to the least upper bound of a datatype's constructor mode and the current mode:

  ```
  #[proof] struct A { … }
  
  // exec
  fn a() {
    let a: A = A { … } 
  }
  ```

  Variable `a` should be `proof` by default.

  Suggested by @tjhance.