use crate::config::Args;
use air::ast::{CommandX, ValidityResult};
use rustc_span::Span;
use std::fs::File;
use std::io::Write;
use vir::ast::Function;

pub(crate) struct Verifier {
    pub count_verified: u64,
    pub count_errors: u64,
    args: Args,
}

impl Verifier {
    pub fn new(args: Args) -> Verifier {
        Verifier { count_verified: 0, count_errors: 0, args: args }
    }

    fn verify(&mut self, compiler: &rustc_interface::interface::Compiler, krate: Vec<Function>) {
        let mut z3_config = z3::Config::new();
        z3_config.set_param_value("auto_config", "false");

        let z3_context = z3::Context::new(&z3_config);
        let z3_solver = z3::Solver::new(&z3_context);
        let mut air_context = air::context::Context::new(&z3_context, &z3_solver);

        air_context.set_rlimit(self.args.rlimit * 1000000);
        if let Some(filename) = &self.args.log_air_initial {
            let file = File::create(filename).expect(&format!("could not open file {}", filename));
            air_context.set_air_initial_log(Box::new(file));
        }
        if let Some(filename) = &self.args.log_air_final {
            let file = File::create(filename).expect(&format!("could not open file {}", filename));
            air_context.set_air_final_log(Box::new(file));
        }
        if let Some(filename) = &self.args.log_smt {
            let file = File::create(filename).expect(&format!("could not open file {}", filename));
            air_context.set_smt_log(Box::new(file));
        }

        air_context.set_z3_param_bool("auto_config", false, true);
        air_context.set_z3_param_bool("smt.mbqi", false, true);
        air_context.set_z3_param_u32("smt.case_split", 3, true);
        air_context.set_z3_param_f64("smt.qi.eager_threshold", 100.0, true);
        air_context.set_z3_param_bool("smt.delay_units", true, true);
        air_context.set_z3_param_u32("smt.arith.solver", 2, true);
        air_context.set_z3_param_bool("smt.arith.nl", false, true);

        for function in krate {
            air_context.blank_line();
            air_context.comment(&("Function ".to_string() + &function.x.name));
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
                            Some(air::ast::Span { raw_span, .. }) => {
                                let span: &Span = (*raw_span)
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
            if let Some(filename) = &self.args.log_vir {
                let mut file =
                    File::create(filename).expect(&format!("could not open file {}", filename));
                for func in vir_crate.iter() {
                    writeln!(&mut file, "fn {} @ {:?}", func.x.name, func.span)
                        .expect("cannot write to vir file");
                    for param in func.x.params.iter() {
                        writeln!(
                            &mut file,
                            "parameter {}: {:?} @ {:?}",
                            param.x.name, param.x.typ, param.span
                        )
                        .expect("cannot write to vir file");
                    }
                    write!(&mut file, "body {:#?}", func.x.body).expect("cannot write to vir file");
                    writeln!(&mut file).expect("cannot write to vir file");
                    writeln!(&mut file).expect("cannot write to vir file");
                }
            }
            self.verify(&compiler, vir_crate);
        });
        rustc_driver::Compilation::Stop
    }
}
