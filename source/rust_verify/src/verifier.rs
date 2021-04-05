use air::ast::{CommandX, ValidityResult};
use rustc_span::Span;
use vir::ast::Function;

pub struct Verifier {
    pub count_verified: u64,
    pub count_errors: u64,
}

impl Verifier {
    pub fn new() -> Verifier {
        Verifier { count_verified: 0, count_errors: 0 }
    }

    fn verify(&mut self, compiler: &rustc_interface::interface::Compiler, krate: Vec<Function>) {
        let mut z3_config = z3::Config::new();
        z3_config.set_param_value("auto_config", "false");
        z3_config.set_param_value("type_check", "true");
        // z3_config.set_param_value("rlimit", "1");

        let z3_context = z3::Context::new(&z3_config);
        let z3_solver = z3::Solver::new(&z3_context);

        let mut z3_params = z3::Params::new(&z3_context);
        //z3_params.set_bool("auto_config", false);
        z3_params.set_bool("smt.mbqi", false);
        z3_params.set_u32("smt.case_split", 3);
        z3_params.set_f64("smt.qi.eager_threshold", 100.0);
        z3_params.set_bool("smt.delay_units", true);
        z3_params.set_u32("smt.arith.solver", 2);
        z3_params.set_bool("smt.arith.nl", false);
        z3_solver.set_params(&z3_params);
        //z3_params.set_u32("rlimit", 1);
        //dbg!(z3_params);

        let mut air_context = air::context::Context::new(&z3_context, &z3_solver);
        for function in krate {
            let commands = vir::function_to_air(&function);
            for command in commands.iter() {
                let result = air_context.command(&command);
                match result {
                    ValidityResult::Valid => {
                        if let CommandX::CheckValid(_) = **command {
                            self.count_verified += 1;
                        }
                    }
                    ValidityResult::Error(span_option) => {
                        match &*span_option {
                            None => {
                                panic!("internal error: found Error with no span")
                            }
                            Some(span_any) => {
                                let span: &Span = (*span_any)
                                    .downcast_ref::<Span>()
                                    .expect("internal error: failed to cast to Span");
                                dbg!(span);
                                compiler
                                    .session()
                                    .parse_sess
                                    .span_diagnostic
                                    .span_err(*span, "assertion failed");
                            }
                        }
                        self.count_errors += 1;
                    }
                }
            }
        }
    }
}

impl rustc_driver::Callbacks for Verifier {
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let _result = queries.global_ctxt().expect("global_ctxt").peek_mut().enter(|tcx| {
            queries.expansion().expect("expansion");
            rustc_typeck::check_crate(tcx).expect("type error");
            let hir = tcx.hir();
            let vir_crate = crate::rust_to_vir::crate_to_vir(tcx, hir.krate());
            self.verify(&compiler, vir_crate);
        });
        rustc_driver::Compilation::Stop
    }
}
