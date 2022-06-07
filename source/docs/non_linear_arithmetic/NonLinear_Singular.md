# Non Linear Arithmetic in Verus

## 1. Proving Non Linear equations with Singular

Since SMT solvers have difficulties with non-linear arithmetic sometimes, Verus supports a separate backend called Singular.
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
Alternatively, you can use this script(`source/tools/get-singular.sh`) for downloading Singular.        
  

- Windows: https://www.singular.uni-kl.de/index.php/singular-download/install-windows.html 

### Details/Limitations
- This can be used only with **int** parameters.
- With current encoding, proving inequalities are not supported.   
- Function calls are interpreted into uninterpreted functions. Users can to feed the function's behavior in `requires`. Instead, users can consider using macros.
- `/` Division is not supported.
   
   
   
## 2. Proving with Z3
Note that default Verus runs with `smt.arith.nl=false`. You can turn on Z3's non-linear arithmetic using below functionalities.
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