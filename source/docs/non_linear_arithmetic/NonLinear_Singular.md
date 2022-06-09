# Non Linear Arithmetic in Verus

## 1. Proving with Z3
Note that default Verus runs with `smt.arith.nl=false`. Therefore, Verus might fail to prove easy proof without using one of the strategies in this document. You can turn on Z3's non-linear arithmetic support using one of the below two functionalities.
### `assert_nonlinear_by`
This assertion generates a separate query with `smt.arith.nl=true`. The `requires` inside the `assert_nonlinear_by` is assumed inside `assert_nonlinear_by`, whereas these are transformed into assertions in the main query. In the main query, the `ensures` inside the `assert_nonlinear_by` is assumed. The separted non-linear query does not recognize surrounding facts other than variables' type invariants. Users should provide required contexts using `requires` in `assert_nonlinear_by`. For example:
```
#[proof]
fn bound_checking(x: u32, z:u32) {
    requires([
        x <= 0xffff,
        z <= 0xffff,
    ]);
    assert_nonlinear_by({
        requires([
            x <= 0xffff,
            z <= 0xffff,
        ]);
        ensures((x as int) * (z as int) == ((x*z) as int));
        assert(0 <= (x as int) * (z as int));
        assert((x as int) * (z as int) <= 0xffff*0xffff);
    });
    assert((x as int) * (z as int) == ((x*z) as int));
}
```
### `#[verifier(nonlinear)]`
When annotated with `#[verifier(nonlinear)]`, the query for this function runs with `smt.arith.nl=true`.


## 2. Proving with Singular

Even if you use `assert_nonlinear_by` or `verifier(nonlinear)`, it is easy to get timeout or unknown for non-linear arithmetics, since it is not easy to deal with non-linear arithmetics for SMT solvers. Therefore, Verus further supports utilizing a separate solver called Singular. 

### `#[verifier(integer_ring)]`
When a proof function is annotated with `verifier(integer_ring`), instead of Z3, Singular uses the Groebner basis for the ideal membership problem. First, it registers all polynomials from requires clauses as a basis. These basis forms an ideal, and the Groebner basis is computed from it. If the ensures polynomial is reduced to 0, it returns Valid, otherwise, it returns invalid.

Using this functionality help users to prove facts with `mod` much easier. For example, the below example is instantly proved, while it is not easy to prove in Z3.
```
#[verifier(integer_ring)]
#[proof]
fn simple_modulo(x: int, y: int, z:int, m:int){
    requires( (x-y) % m == 0);
    ensures( (x*z- y*z) % m == 0);
}
```

### Installing Singular
To use Singular's standard libary(which includes Groebner basis), you need more than just Singular executable binary. Using the system's package manager is preferred, but you can find other options as well. 

- Mac: `brew install Singular` and add `VERUS_SINGULAR_PATH` when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/local/bin/Singular`). For more options, see OS X installation guide: https://www.singular.uni-kl.de/index.php/singular-download/install-os-x.html 

  
- Linux: `apt-get update`, `apt-get install singular`, and add `VERUS_SINGULAR_PATH` when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/bin/Singular`). For more options, see Linux installation guide: https://www.singular.uni-kl.de/index.php/singular-download/install-linuxunix.html 

- Windows: https://www.singular.uni-kl.de/index.php/singular-download/install-windows.html 

### Compiliing with Feature 'Singular'
This `integer_ring` functionality is conditionally compiled when `singular` feature is set. To use this, add flag `--features singular` when `cargo build`.

### Details/Limitations
- This can be used only with **int** parameters.
- With current encoding, proving inequalities are not supported.   
- Function calls are interpreted into uninterpreted functions. Users can to feed the function's behavior in `requires`. Instead, users can consider using macros.
- `/` Division is not supported.

#### Workarounds for limitations
- Since it is only with `int`, users need to check bounds when they want to prove properties about bounded integers. One example for this is at `source/rust_verify/examples/integer_ring/integer_ring_bound_check.rs`.
- Proving about inequalities and division is not supported. However, users might be able to use Singular by adding additional variables. One example for this is at `source/rust_verify/examples/integer_ring/integer_ring.rs, line 115: multiple_offsed_mod_gt_0_int`.
   
