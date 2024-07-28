use crate::ast::CommandX;
use crate::context::{SmtSolver, ValidityResult};
use crate::messages::Reporter;
#[allow(unused_imports)]
use crate::parser::Parser;
#[allow(unused_imports)]
use crate::printer::macro_push_node;
#[allow(unused_imports)]
use sise::Node;

#[allow(dead_code)]
fn run_nodes_as_test(should_typecheck: bool, should_be_valid: bool, nodes: &[Node]) {
    let message_interface = std::sync::Arc::new(crate::messages::AirMessageInterface {});
    let reporter = Reporter {};
    // TODO: Support testing with cvc5 too
    let mut air_context = crate::context::Context::new(message_interface.clone(), SmtSolver::Z3);
    air_context.set_z3_param("air_recommended_options", "true");
    match Parser::new(message_interface.clone()).nodes_to_commands(&nodes) {
        Ok(commands) => {
            for command in commands.iter() {
                let result = air_context.command(
                    &*message_interface,
                    &reporter,
                    &command,
                    Default::default(),
                );
                match (&**command, should_typecheck, should_be_valid, result) {
                    (_, false, _, ValidityResult::TypeError(_)) => {}
                    (_, true, _, ValidityResult::TypeError(s)) => {
                        panic!("type error: {}", s);
                    }
                    (_, _, true, ValidityResult::Valid(..)) => {} // REVIEW: test unsat_core output
                    (_, _, false, ValidityResult::Invalid(..)) => {}
                    (CommandX::CheckValid(_), _, _, res) => {
                        panic!("unexpected result {:?}", res);
                    }
                    _ => {}
                }
                if matches!(**command, CommandX::CheckValid(..)) {
                    air_context.finish_query();
                }
            }
        }
        Err(s) => {
            println!("{}", s);
            panic!();
        }
    }
}

#[allow(unused_macros)]
macro_rules! yes {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(true, true, &v)
       }
    };
}

#[allow(unused_macros)]
macro_rules! no {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(true, false, &v)
       }
    };
}

#[allow(unused_macros)]
macro_rules! untyped {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(false, false, &v)
       }
    };
}

#[test]
fn yes_true() {
    yes!(
        (check-valid
            (assert true)
        )
    );
}

#[test]
fn no_false() {
    no!(
        (check-valid
            (assert false)
        )
    );
}

#[test]
fn yes_int_const() {
    yes!(
        (check-valid
            (assert
                (= (+ 2 2) 4)
            )
        )
    );
}

#[test]
fn no_int_const() {
    no!(
        (check-valid
            (assert
                (= (+ 2 2) 5)
            )
        )
    );
}

#[test]
fn yes_int_vars() {
    yes!(
        (check-valid
            (declare-const x Int)
            (declare-const y Int)
            (declare-const z Int)
            (assert
                (= (+ x y z) (+ z y x))
            )
        )
    );
}

#[test]
fn no_int_vars() {
    no!(
        (check-valid
            (declare-const x Int)
            (declare-const y Int)
            (assert
                (= (+ x y) (+ y y))
            )
        )
    );
}

#[test]
fn yes_int_neg() {
    yes!(
        (check-valid
            (declare-const x Int)
            (assert
                (= (+ x (- 2)) (- x 2))
            )
        )
    );
}

#[test]
fn yes_int_axiom() {
    yes!(
        (check-valid
            (declare-const x Int)
            (axiom (> x 3))
            (assert
                (>= x 3)
            )
        )
    );
}

#[test]
fn no_int_axiom() {
    no!(
        (check-valid
            (declare-const x Int)
            (axiom (>= x 3))
            (assert
                (> x 3)
            )
        )
    );
}

#[test]
fn yes_test_block() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (assert (>= x 3))
                (assume (> x 5))
                (assert (>= x 5))
            )
        )
    );
}

#[test]
fn no_test_block() {
    no!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (assert (>= x 3))
                (assert (>= x 5))
                (assume (> x 5))
            )
        )
    );
}

#[test]
fn yes_test_block_nest() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (assume (> x 3))
                (block
                    (assert (>= x 3))
                    (assume (> x 5))
                )
                (assert (>= x 5))
            )
        )
    );
}

#[test]
fn yes_global() {
    yes!(
        (push)
            (axiom false)
            (check-valid
                (assert false)
            )
        (pop)
    );
}

#[test]
fn no_global() {
    no!(
        (push)
            (axiom false)
        (pop)
        (check-valid
            (assert false)
        )
    );
}

#[test]
fn yes_type() {
    yes!(
        (check-valid
            (declare-sort T 0)
            (declare-const x T)
            (assert
                (= x x)
            )
        )
    );
}

#[test]
fn no_type() {
    no!(
        (check-valid
            (declare-sort T 0)
            (declare-const x T)
            (declare-const y T)
            (assert
                (= x y)
            )
        )
    );
}

#[test]
fn yes_assign() {
    yes!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (assign x (+ x 1))
                (assert (= x 102))
                (assert (= y 200))
            )
        )
    );
}

#[test]
fn no_assign() {
    no!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (assign x (+ x 1))
                (assert (not (= x 102)))
            )
        )
    );
}

#[test]
fn yes_havoc() {
    yes!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (havoc x)
                (assert (= y 200))
            )
        )
    );
}

#[test]
fn no_havoc() {
    no!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (havoc y)
                (assert (= y 200))
            )
        )
    );
}

#[test]
fn yes_snapshot() {
    yes!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (snapshot A)
                (snapshot B)
                (assign x (+ x 1))
                (assert (= (old A x) 101))
                (assert (= (old B x) 101))
                (assert (= x 102))
                (assert (= y 200))
                (snapshot A)
                (assert (= (old A x) 102))
                (assert (= (old B x) 101))
            )
        )
    )
}

#[test]
fn yes_test_switch1() {
    yes!(
        (check-valid
            (declare-const x Int)
            (block
                (switch
                    (assume (> x 20))
                    (assume (< x 10))
                )
                (assert (or (> x 20) (< x 10)))
            )
        )
    );
}

#[test]
fn no_test_switch1() {
    no!(
        (check-valid
            (declare-const x Int)
            (block
                (switch
                    (assume (> x 20))
                    (assume (< x 10))
                )
                (assert (> x 20))
            )
        )
    );
}

#[test]
fn yes_test_switch2() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (assign x 10)
                (switch
                    (block
                    )
                    (assign x 15)
                    (block
                        (assign x 20)
                        (assign x (+ x 30))
                        (assign x (- x 40))
                    )
                    (assign x (+ x 7))
                )
                (assert (>= x 10))
                (assert (<= x 20))
            )
        )
    );
}

#[test]
fn no_test_switch2() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (assign x 10)
                (switch
                    (block
                    )
                    (assign x 15)
                    (block
                        (assign x 20)
                        (assign x (+ x 30))
                        (assign x (- x 40))
                    )
                    (assign x (+ x 7))
                )
                (assert (> x 10))
                (assert (<= x 20))
            )
        )
    );
}

#[test]
fn no_test_switch3() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (assign x 10)
                (switch
                    (block
                    )
                    (assign x 15)
                    (block
                        (assign x 20)
                        (assign x (+ x 30))
                        (assign x (- x 40))
                    )
                    (assign x (+ x 7))
                )
                (assert (>= x 10))
                (assert (< x 17))
            )
        )
    );
}

#[test]
fn untyped_scope1() {
    untyped!(
        (declare-const x Int)
        (declare-const x Int) // error: x already in scope
    );
}

#[test]
fn untyped_scope2() {
    untyped!(
        (declare-const x Int)
        (push)
            (declare-const x Int) // error: x already in scope
        (pop)
    );
}

#[test]
fn untyped_scope3() {
    untyped!(
        (declare-const x Int)
        (check-valid
            (declare-const x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope4() {
    untyped!(
        (declare-const x Int)
        (check-valid
            (declare-var x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope5() {
    untyped!(
        (declare-const "x@0" Int)
        (check-valid
            (declare-var x Int) // error: x@0 already in scope
            (assert true)
        )
    );
}

#[test]
fn untyped_scope6() {
    untyped!(
        (declare-var x Int) // error: declare-var not allowed in global scope
    );
}

#[test]
fn untyped_scope7() {
    untyped!(
        (declare-const x Int)
        (declare-fun x (Int Int) Int) // error: x already in scope
    );
}

#[test]
fn yes_scope1() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (push)
            (declare-const x Int)
        (pop)
    );
}

#[test]
fn yes_scope2() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (declare-const x Int)
    );
}

#[test]
fn yes_scope3() {
    yes!(
        (push)
            (declare-const x Int)
        (pop)
        (check-valid
            (declare-var x Int)
            (assert true)
        )
    );
}

#[test]
fn yes_fun1() {
    yes!(
        (check-valid
            (declare-fun f (Int Bool) Bool)
            (block
                (assume (f 10 true))
                (assert (f 10 true))
            )
        )
    )
}

#[test]
fn no_fun1() {
    no!(
        (check-valid
            (declare-fun f (Int Bool) Bool)
            (block
                (assume (f 10 true))
                (assert (f 11 true))
            )
        )
    )
}

#[test]
fn no_typing1() {
    untyped!(
        (axiom 10)
    )
}

#[test]
fn no_typing2() {
    untyped!(
        (axiom b)
    )
}

#[test]
fn no_typing3() {
    untyped!(
        (declare-fun f (Int Bool) Bool)
        (axiom (f 10))
    )
}

#[test]
fn no_typing4() {
    untyped!(
        (declare-fun f (Int Bool) Bool)
        (axiom (f 10 20))
    )
}

#[test]
fn no_typing5() {
    untyped!(
        (check-valid
            (declare-var x Int)
            (assign x true)
        )
    )
}

#[test]
fn yes_let1() {
    yes!(
        (check-valid
            (assert (let ((x 10) (y 20)) (< x y)))
        )
    )
}

#[test]
fn yes_let2() {
    yes!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        40
                        (let ((x (+ x 10))) (+ x y)) // can shadow other let/forall bindings
                    )
                )
            )
        )
    )
}

#[test]
fn yes_let3() {
    yes!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        (let ((x (+ x 10))) (+ x y)) // can shadow other let/forall bindings
                        (+ x x y) // make sure old values are restored here
                    )
                )
            )
        )
    )
}

#[test]
fn yes_let4() {
    yes!(
        (check-valid
            (assert
                (let ((x true) (y 20))
                    (and
                        (=
                            (let ((x (+ y 10))) (+ x y))
                            50
                        )
                        x // make sure old type is restored here
                    )
                )
            )
        )
    )
}

#[test]
fn untyped_let1() {
    untyped!(
        (check-valid
            (assert (let ((x 10) (x 20)) true)) // no duplicates allowed in single let
        )
    )
}

#[test]
fn untyped_let2() {
    untyped!(
        (declare-const y Int)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn untyped_let3() {
    untyped!(
        (declare-fun y (Int) Int)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn untyped_let4() {
    untyped!(
        (declare-sort y 0)
        (check-valid
            (assert (let ((x 10) (y 20)) true)) // cannot shadow global name
        )
    )
}

#[test]
fn no_let1() {
    no!(
        (check-valid
            (assert
                (let ((x 10) (y 20))
                    (=
                        (let ((x (+ x 10))) (+ x y))
                        (+ x y) // make sure old values are restored here
                    )
                )
            )
        )
    )
}

#[test]
fn yes_forall1() {
    yes!(
        (check-valid
            (assert
                (forall ((i Int)) true)
            )
        )
    )
}

#[test]
fn yes_forall2() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall3() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall4() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (declare-fun g (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((g i j))
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_forall5() {
    yes!(
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Bool)
        (axiom
            (forall ((i Int) (j Int)) (!
                (=> (f i) (g j))
                :pattern ((f i) (g j))
            ))
        )
        (check-valid
            (assert
                (=> (f 10) (g 10))
            )
        )
    )
}

#[test]
fn no_forall1() {
    no!(
        (check-valid
            (assert
                (forall ((i Int)) false)
            )
        )
    )
}

#[test]
fn no_forall2() {
    no!(
        (declare-fun f (Int Int) Bool)
        (declare-fun g (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (forall ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((g i j))
                    ))
                    (f 10 20) // doesn't match (g i j)
                )
            )
        )
    )
}

#[test]
fn untyped_forall1() {
    untyped!(
        (check-valid
            (assert
                (let
                    ((
                        x
                        (forall ((i Int)) i)
                    ))
                    true
                )
            )
        )
    )
}

#[test]
fn yes_exists1() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (f 10 20)
                    (exists ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                )
            )
        )
    )
}

#[test]
fn no_exists1() {
    no!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (=>
                    (exists ((i Int) (j Int)) (!
                        (f i j)
                        :pattern ((f i j))
                    ))
                    (f 10 20)
                )
            )
        )
    )
}

#[test]
fn yes_ite1() {
    yes!(
        (check-valid
            (block
                (assert (= (ite true 10 20) 10))
                (assert (= (ite false 10 20) 20))
            )
        )
    )
}

#[test]
fn no_ite1() {
    no!(
        (check-valid
            (assert (= (ite true 10 20) 20))
        )
    )
}

#[test]
fn untyped_ite1() {
    untyped!(
        (check-valid
            (assert (= (ite 0 10 20) 20))
        )
    )
}

#[test]
fn untyped_ite2() {
    untyped!(
        (check-valid
            (assert (= (ite true 10 true) 20))
        )
    )
}

#[test]
fn yes_distinct() {
    yes!(
        (check-valid
            (assert (distinct 10 20 30))
        )
    )
}

#[test]
fn no_distinct() {
    no!(
        (check-valid
            (assert (distinct 10 20 10))
        )
    )
}

#[test]
fn untyped_distinct() {
    untyped!(
        (check-valid
            (assert (distinct 10 20 true))
        )
    )
}

#[test]
fn yes_datatype1() {
    yes!(
        (declare-datatypes ((IntPair 0)) (
            (
                (int_pair
                    (ip1 Int)
                    (ip2 Int)
                )
            )
        ))
        (check-valid
            (declare-const x IntPair)
            (block
                (assume (= x (int_pair 10 20)))
                (assert (= 10 (ip1 x)))
            )
        )
    )
}

#[test]
fn yes_datatype2() {
    yes!(
        (declare-datatypes ((Tree 0) (Pair 0)) (
            (
                (empty)
                (full
                    (children Pair)
                )
            )
            (
                (pair
                    (fst Tree)
                    (snd Tree)
                )
            )
        ))
        (check-valid
            (declare-const x Tree)
            (block
                (assume (= x (full (pair (empty) (empty)))))
                (assert (= (empty) (fst (children x))))
                (assert (is-empty (snd (children x))))
            )
        )
    )
}

#[test]
fn yes_deadend() {
    yes!(
        (declare-const b Bool)
        (check-valid
            (block
                (assume b)
                (deadend
                    (block
                        (assert b)
                    )
                )
                (assert b)
            )
        )
    )
}

#[test]
fn no_deadend1() {
    no!(
        (declare-const b Bool)
        (check-valid
            (block
                (deadend
                    (block
                        (assume b)
                        (assert b)
                    )
                )
                (assert b)
            )
        )
    )
}

#[test]
fn no_deadend2() {
    no!(
        (declare-const b Bool)
        (check-valid
            (block
                (deadend
                    (block
                        (assume b)
                        (assert false)
                    )
                )
                (assert b)
            )
        )
    )
}

#[test]
fn typed_break1() {
    yes!(
        (check-valid
            (breakable L (break L))
        )
    )
}

#[test]
fn typed_break2() {
    yes!(
        (check-valid
            (breakable L (break L))
        )
        (check-valid
            (breakable L (break L))
        )
    )
}

#[test]
fn untyped_break1() {
    untyped!(
        (check-valid
            (breakable L (assert false))
        )
        (check-valid
            (break L)
        )
    )
}

#[test]
fn untyped_break2() {
    untyped!(
        (check-valid
            (breakable L1 (break L2))
        )
    )
}

#[test]
fn untyped_break3() {
    untyped!(
        (check-valid
            (block
                (break L)
                (breakable L (block))
            )
        )
    )
}

#[test]
fn untyped_break4() {
    untyped!(
        (check-valid
            (block
                (breakable L (block))
                (break L)
            )
        )
    )
}

#[test]
fn untyped_break5() {
    untyped!(
        (check-valid
            (switch
                (breakable L (block))
                (break L)
            )
        )
    )
}

#[test]
fn untyped_break6() {
    untyped!(
        (check-valid
            (switch
                (breakable L (block))
                (breakable L (block))
            )
        )
    )
}

#[test]
fn yes_break1() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (block
                        (assign x 9)
                        (assign x 10)
                    )
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break1() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 9)
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break1b() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn yes_break2() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 19)
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break2() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 19)
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 20) (= x 30)))
            )
        )
    )
}

#[test]
fn no_break2b() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L (switch
                    (block
                        (assign x 19)
                        (assign x 20)
                        (break L)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (break L)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20)))
            )
        )
    )
}

#[test]
fn yes_break3() {
    yes!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L1 (switch
                    (block
                        (assign x 20)
                        (break L1)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (breakable L2 (switch
                            (assign x 40)
                            (block
                                (assign x (+ x 1))
                                (break L2)
                            )
                            (block
                                (assign x (+ x 2))
                                (break L1)
                            )
                        ))
                        (assign x (+ x 5))
                        (break L1)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 32) (= x 36) (= x 45)))
            )
        )
    )
}

#[test]
fn no_break3() {
    no!(
        (check-valid
            (declare-var x Int)
            (block
                (breakable L1 (switch
                    (block
                        (assign x 20)
                        (break L1)
                        (assign x 200)
                    )
                    (block
                        (assign x 30)
                        (breakable L2 (switch
                            (assign x 40)
                            (block
                                (assign x (+ x 1))
                                (break L1)
                            )
                            (block
                                (assign x (+ x 2))
                                (break L2)
                            )
                        ))
                        (assign x (+ x 5))
                        (break L1)
                        (assign x 300)
                    )
                    (assign x 10)
                ))
                (assert (or (= x 10) (= x 20) (= x 32) (= x 36) (= x 45)))
            )
        )
    )
}

#[test]
fn yes_array1() {
    yes!(
        (check-valid
            (assert (=
                20
                (apply Int
                    (array 10 20 30)
                    1
                )
            ))
        )
    )
}

#[test]
fn untyped_array1() {
    untyped!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (array 10 true 30)
                    1
                )
            ))
        )
    )
}

#[test]
fn no_array1() {
    no!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (array 10 20 30)
                    2
                )
            ))
        )
    )
}

#[test]
fn yes_array2() {
    yes!(
        (check-valid
            (assert (=
                6
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (array 10 20 (+ x y 1))
                        )
                        2
                        3
                    )
                    2
                )
            ))
        )
    )
}

#[test]
fn no_array2() {
    no!(
        (check-valid
            (assert (=
                5
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (array 10 20 (+ x y 1))
                        )
                        2
                        3
                    )
                    2
                )
            ))
        )
    )
}

#[test]
fn yes_array3() {
    yes!(
        (check-valid
            (assert
                (=
                    (array (+ (- 10 (+ 2 2)) 5))
                    (array (+ (- 10 4) 5))
                )
            )
        )
    )
}

#[test]
fn no_array3() {
    no!(
        (check-valid
            (assert
                (=
                    (array (+ (- 10 (+ 2 3)) 5))
                    (array (+ (- 10 4) 5))
                )
            )
        )
    )
}

#[test]
fn yes_empty_array() {
    yes!(
        (check-valid
            (assert (= (array) (array)))
        )
    )
}

#[test]
fn yes_lambda1() {
    yes!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (lambda ((x Int) (y Int)) (+ x y 5))
                    2
                    3
                )
            ))
        )
    )
}

#[test]
fn untyped_lambda1() {
    untyped!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (lambda ((x Int) (y Int)) (+ x y 5))
                    3
                )
            ))
        )
    )
}

#[test]
fn no_lambda1() {
    no!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (lambda ((x Int) (y Int)) (+ x y 4))
                    2
                    3
                )
            ))
        )
    )
}

#[test]
fn yes_lambda2() {
    yes!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (lambda ((z Int)) (+ x y z 1))
                        )
                        2
                        3
                    )
                    4
                )
            ))
        )
    )
}

#[test]
fn no_lambda2() {
    no!(
        (check-valid
            (assert (=
                10
                (apply Int
                    (apply Fun
                        (lambda ((x Int) (y Int))
                            (lambda ((z Int)) (+ x y z 1))
                        )
                        2
                        3
                    )
                    5
                )
            ))
        )
    )
}

#[test]
fn yes_lambda3() {
    yes!(
        (check-valid
            (assert
                (let ((g
                        (let (
                                (f (lambda ((x Int)) (+ x 1)))
                            )
                            f
                        )
                    ))
                    (=
                        (apply Int g 3)
                        4
                    )
                )
            )
        )
    )
}

#[test]
fn no_lambda3() {
    no!(
        (check-valid
            (assert
                (let ((g
                        (let (
                                (f (lambda ((x Int)) (+ x 1)))
                            )
                            f
                        )
                    ))
                    (=
                        (apply Int g 3)
                        5
                    )
                )
            )
        )
    )
}

#[test]
fn yes_lambda4() {
    yes!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 4) yy))
                )
            )
        )
    )
}

#[test]
fn no_lambda4a() {
    no!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((y Int) (x Int)) (+ (- x 4) y))
                )
            )
        )
    )
}

#[test]
fn no_lambda4b() {
    no!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x 5) y))
                    (lambda ((x Int) (y Int)) (+ (- x 4) y))
                )
            )
        )
    )
}

#[test]
fn yes_lambda5() {
    yes!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 4) yy))
                )
            )
        )
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 4) yy))
                )
            )
        )
    )
}

#[test]
fn no_lambda5() {
    no!(
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 5) yy))
                )
            )
        )
        (check-valid
            (assert
                (=
                    (lambda ((x Int) (y Int)) (+ (- x (+ 2 2)) y))
                    (lambda ((xx Int) (yy Int)) (+ (- xx 5) yy))
                )
            )
        )
    )
}

#[test]
fn yes_lambda6() {
    yes!(
        (declare-const a Fun)
        (axiom (= a (lambda ((x Int)) (+ x 1))))
        (declare-const b Fun)
        (axiom (= b (lambda ((x Int)) (+ x 1))))
        (check-valid
            (assert (= a b))
        )
    )
}

#[test]
fn no_lambda6() {
    no!(
        (declare-const a Fun)
        (axiom (= a (lambda ((x Int)) (+ x 1))))
        (declare-const b Fun)
        (axiom (= b (lambda ((x Int)) (+ x 2))))
        (check-valid
            (assert (= a b))
        )
    )
}

#[test]
fn yes_lambda_trigger1() {
    yes!(
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Bool)
        (declare-const lf Fun)
        (declare-const lg Fun)
        (declare-const i Int)
        // (axiom (= lf (lambda ((x Int)) (f x)))) // fails without the trigger
        (axiom (= lf (lambda ((x Int)) (!
            (f x)
            :pattern ((f x))
        ))))
        (axiom (= lg (lambda ((x Int)) (g x))))
        (declare-fun enslemma (Fun Fun) Bool)
        (axiom (forall ((x Int)) (!
            (=> (apply Bool lf x) (apply Bool lg x))
            :pattern ((apply Bool lf x))
            :pattern ((apply Bool lg x))
        )))
        (check-valid (block
            (assume (f i))
            (assert (g i))
        ))
    )
}

#[test]
fn yes_lambda_trigger2() {
    yes!(
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Bool)
        (declare-const lf Fun)
        (declare-const lg Fun)
        (declare-const i Int)
        // (axiom (= lf (lambda ((x Int)) (f x)))) // fails without the trigger
        (axiom (= lf (lambda ((x Int)) (!
            (f x)
            :pattern ((f x))
        ))))
        (axiom (= lg (lambda ((x Int)) (g x))))
        (declare-fun enslemma (Fun Fun) Bool)
        (axiom (forall ((fn1 Fun) (fn2 Fun)) (!
            (= (enslemma fn1 fn2)
                (forall ((x Int)) (!
                    (=> (apply Bool fn1 x) (apply Bool fn2 x))
                    :pattern ((apply Bool fn1 x))
                    :pattern ((apply Bool fn2 x))
                )))
            :pattern ((enslemma fn1 fn2))
        )))
        (check-valid (block
            (assume (enslemma lf lg))
            (assume (f i))
            (assert (g i))
        ))
    )
}

#[test]
fn yes_choose1() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 3))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (!
                    (f x x)
                    :pattern ((f x x))
                ) x)
                ))
                (f a a)
                )
            )
        )
    )
}

#[test]
fn yes_choose1_2() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 3))
        (check-valid
            (assert
                (let (( a (choose ((x Int) (y Int)) (!
                        (and (f x y) (= x y))
                        :pattern ((f x y))
                    ) (+ x y))
                    ))
                    (f (div a 2) (div a 2))
                )
            )
        )
    )
}

#[test]
fn no_choose1() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (!
                        (f x x)
                        :pattern ((f x x))
                    ) x) ))
                    (f a a)
                )
            )
        )
    )
}

#[test]
fn no_choose1_2() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int) (y Int)) (!
                        (and (f x y) (= x y))
                        :pattern ((f x y))
                    ) (+ x y)) ))
                    (f (div a 2) (div a 2))
                )
            )
        )
    )
}

#[test]
fn yes_choose2() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 3))
        (check-valid
            (assert
                (let (( a
                        (choose ((x Int))
                            (!
                                (f x x)
                                :pattern ((f x x))
                            )
                            x
                        )
                    ))
                    (f a a)
                )
            )
        )
    )
}

#[test]
fn no_choose2() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a
                        (choose ((x Int))
                            (!
                                (f x x)
                                :pattern ((f x x))
                            )
                            x
                        )
                    ))
                    (f a a)
                )
            )
        )
    )
}

#[test]
fn yes_choose3() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (!
                        (f x 4)
                        :pattern ((f x 4))
                    ) x)
                ))
                (f a 4)
                )
            )
        )
    )
}

#[test]
fn no_choose3() {
    no!(
        (declare-fun f (Int Int) Bool)
        (axiom (f 3 4))
        (check-valid
            (assert
                (let (( a (choose ((x Int)) (f x 3) x) ))
                    (f a 3)
                )
            )
        )
    )
}

#[test]
fn yes_choose4() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert (=
                (choose ((x Int)) (f x 4) x)
                (choose ((x Int)) (f x (+ 2 2)) x)
            ))
        )
    )
}

#[test]
fn no_choose4() {
    no!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert (=
                (choose ((x Int)) (f x 5) x)
                (choose ((x Int)) (f x (+ 2 2)) x)
            ))
        )
    )
}

#[test]
fn yes_choose5() {
    yes!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (let (( g
                        (lambda ((m Int))
                            (choose ((x Int)) (f x (+ m 1)) x)
                        )
                    ))
                    (=
                        (apply Int g 4)
                        (apply Int g (+ 2 2))
                    )
                )
            )
        )
    )
}

#[test]
fn no_choose5() {
    no!(
        (declare-fun f (Int Int) Bool)
        (check-valid
            (assert
                (let (( g
                        (lambda ((m Int))
                            (choose ((x Int)) (f x (+ m 1)) x)
                        )
                    ))
                    (=
                        (apply Int g 5)
                        (apply Int g (+ 2 2))
                    )
                )
            )
        )
    )
}

#[test]
fn yes_partial_order() {
    yes!(
        (declare-sort X 0)
        (declare-const c1 X)
        (declare-const c2 X)
        (declare-const c3 X)
        (check-valid
            (axiom ((_ partial-order 77) c1 c2))
            (axiom ((_ partial-order 77) c2 c3))
            (assert ((_ partial-order 77) c1 c3))
        )
    )
}

#[test]
fn no_partial_order() {
    no!(
        (declare-sort X 0)
        (declare-const c1 X)
        (declare-const c2 X)
        (declare-const c3 X)
        (check-valid
            (axiom ((_ partial-order 77) c1 c2))
            (axiom ((_ partial-order 76) c2 c3))
            (assert ((_ partial-order 77) c1 c3))
        )
    )
}
