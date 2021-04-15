use crate::ast::{CommandX, ValidityResult};
#[allow(unused_imports)]
use crate::print_parse::{macro_push_node, nodes_to_commands};
#[allow(unused_imports)]
use sise::Node;

#[allow(dead_code)]
fn run_nodes_as_test(should_succeed: bool, nodes: &[Node]) {
    let mut z3_config = z3::Config::new();
    z3_config.set_param_value("auto_config", "false");
    let z3_context = z3::Context::new(&z3_config);
    let z3_solver = z3::Solver::new(&z3_context);
    let mut air_context = crate::context::Context::new(&z3_context, &z3_solver);
    air_context.set_z3_param("air_recommended_options", "true");
    match nodes_to_commands(&nodes) {
        Ok(commands) => {
            for command in commands.iter() {
                let result = air_context.command(&command);
                match (&**command, should_succeed, result) {
                    (_, true, ValidityResult::Valid) => {}
                    (_, false, ValidityResult::Error(_)) => {}
                    (CommandX::CheckValid(_), _, _) => {
                        panic!("unexpected result");
                    }
                    _ => {}
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
           run_nodes_as_test(true, &v)
       }
    };
}

#[allow(unused_macros)]
macro_rules! no {
    ( $( $x:tt )* ) => {
       {
           let mut v = Vec::new();
           $(macro_push_node(&mut v, node!($x));)*
           run_nodes_as_test(false, &v)
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
            (declare-sort T)
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
            (declare-sort T)
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
    no!(
        (check-valid
            (declare-var x Int)
            (declare-var y Int)
            (block
                (assume (= x 100))
                (assume (= y 200))
                (assign x (+ x 1))
                (assign x (+ x 1))
                (assert (= x 102))
                (assert (= y 100))
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
#[should_panic]
fn panic_scope1() {
    yes!(
        (declare-const x Int)
        (declare-const x Int) // error: x already in scope
    );
}

#[test]
#[should_panic]
fn panic_scope2() {
    yes!(
        (declare-const x Int)
        (push)
            (declare-const x Int) // error: x already in scope
        (pop)
    );
}

#[test]
#[should_panic]
fn panic_scope3() {
    yes!(
        (declare-const x Int)
        (check-valid
            (declare-const x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
#[should_panic]
fn panic_scope4() {
    yes!(
        (declare-const x Int)
        (check-valid
            (declare-var x Int) // error: x already in scope
            (assert true)
        )
    );
}

#[test]
#[should_panic]
fn panic_scope5() {
    yes!(
        (declare-const "x@0" Int)
        (check-valid
            (declare-var x Int) // error: x@0 already in scope
            (assert true)
        )
    );
}

#[test]
#[should_panic]
fn panic_scope6() {
    yes!(
        (declare-var x Int) // error: declare-var not allowed in global scope
    );
}

#[test]
#[should_panic]
fn panic_scope7() {
    yes!(
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
