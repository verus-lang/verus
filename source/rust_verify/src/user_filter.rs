use crate::config::Args;
use crate::util::error;
use crate::verifier::module_name;
use std::collections::HashSet;
use vir::ast::Fun;
use vir::ast::Function;
use vir::ast::Path;
use vir::ast::VirErr;
use vir::ast_util::friendly_fun_name_crate_relative;

#[derive(Clone)]
pub enum UserFilter {
    /// No filter (i.e., verify everything)
    None,
    /// Verify modules (None for root module)
    Modules(Vec<Option<String>>),
    /// Verify function
    Function(Option<String>, String),
}

impl UserFilter {
    pub fn is_everything(&self) -> bool {
        matches!(self, UserFilter::None)
    }

    pub fn is_function_filter(&self) -> bool {
        matches!(self, UserFilter::Function(..))
    }

    pub fn from_args(args: &Args) -> Result<UserFilter, VirErr> {
        if let Some(func_name) = &args.verify_function {
            if args.verify_module.is_empty() && !args.verify_root {
                return Err(error(
                    "--verify-function option requires --verify-module or --verify-root",
                ));
            }

            if args.verify_module.len() + (if args.verify_root { 1 } else { 0 }) > 1 {
                return Err(error(
                    "--verify-function only allowed with a single --verify-module (or --verify-root)",
                ));
            }

            let module = if args.verify_root { None } else { Some(args.verify_module[0].clone()) };
            return Ok(UserFilter::Function(module, func_name.clone()));
        }

        if args.verify_module.is_empty() && !args.verify_root {
            return Ok(UserFilter::None);
        }

        let mut modules: Vec<Option<String>> =
            args.verify_module.iter().map(|s| Some(s.clone())).collect();
        if args.verify_root {
            modules.push(None);
        }

        Ok(UserFilter::Modules(modules))
    }

    pub fn filter_module_ids(&self, module_ids: &Vec<Path>) -> Result<Vec<Path>, VirErr> {
        let mut remaining_modules: HashSet<&Option<String>> = match self {
            UserFilter::None => {
                return Ok(module_ids.clone());
            }
            UserFilter::Modules(m) => m.iter().collect(),
            UserFilter::Function(m, _) => std::iter::once(m).collect(),
        };

        let module_ids_to_verify = module_ids
            .iter()
            .filter(|m| {
                (m.segments.len() == 0 && remaining_modules.take(&None).is_some())
                    || (m.segments.len() > 0
                        && remaining_modules.take(&Some(module_name(m))).is_some())
            })
            .cloned()
            .collect();

        // Check if any modules from the user's list didn't appear in the krate modules
        if let Some(mod_name) = remaining_modules.into_iter().next() {
            let mut lines = module_ids
                .iter()
                .filter_map(|m| {
                    let name = module_name(m);
                    (!(name.starts_with("pervasive::") || name == "pervasive")
                        && m.segments.len() > 0)
                        .then(|| format!("- {name}"))
                })
                .collect::<Vec<_>>();
            lines.sort(); // Present the available modules in sorted order
            let mod_name = match mod_name {
                None => "[root module]",
                Some(m) => &m,
            };
            let mut msg = vec![
                format!("could not find module {mod_name} specified by --verify-module"),
                format!("available modules are:"),
            ];
            msg.extend(lines);
            msg.push(format!("or use --verify-root, --verify-pervasive"));
            return Err(error(msg.join("\n")));
        }

        Ok(module_ids_to_verify)
    }

    pub fn get_is_function_exact_match(
        &self,
        funs: &Vec<Function>,
        module: &Path,
    ) -> Result<bool, VirErr> {
        let mut verify_function_exact_match = false;
        if let UserFilter::Function(_, verify_function) = self {
            let module_funs = funs.iter().filter(|f| Some(module.clone()) == f.x.owning_module);
            let mut module_fun_names: Vec<String> =
                module_funs.map(|f| friendly_fun_name_crate_relative(&module, &f.x.name)).collect();

            let clean_verify_function = verify_function.trim_matches('*');
            let mut filtered_functions: Vec<&String> =
                module_fun_names.iter().filter(|f| f.contains(clean_verify_function)).collect();

            // no match
            if filtered_functions.len() == 0 {
                module_fun_names.sort();
                let msg = vec![
                    format!(
                        "could not find function {verify_function} specified by --verify-function"
                    ),
                    format!("available functions are:"),
                ]
                .into_iter()
                .chain(module_fun_names.iter().map(|f| format!("  - {f}")))
                .collect::<Vec<String>>()
                .join("\n");
                return Err(error(msg));
            }

            // substring match
            if verify_function == clean_verify_function {
                verify_function_exact_match = filtered_functions
                    .iter()
                    .filter(|f| {
                        // filter for exact match and impl func match
                        *f == &verify_function || f.ends_with(&format!("::{}", verify_function))
                    })
                    .count()
                    == 1;

                if filtered_functions.len() > 1 && !verify_function_exact_match {
                    filtered_functions.sort();
                    let msg = vec![
                        format!(
                            "more than one match found for --verify-function {verify_function}, consider using wildcard *{verify_function}* to verify all matched results,"
                        ),
                        format!(
                            "or specify a unique substring for the desired function, matched results are:"
                        ),
                    ].into_iter()
                    .chain(filtered_functions.iter().map(|f| format!("  - {f}")))
                    .collect::<Vec<String>>()
                    .join("\n");
                    return Err(error(msg));
                }
            } else {
                // wildcard match
                let wildcard_mismatch =
                    match (verify_function.starts_with("*"), verify_function.ends_with("*")) {
                        (true, false) => {
                            !filtered_functions.iter().any(|f| f.ends_with(clean_verify_function))
                        }
                        (false, true) => {
                            !filtered_functions.iter().any(|f| f.starts_with(clean_verify_function))
                        }
                        _ => false,
                    };

                if wildcard_mismatch {
                    filtered_functions.sort();
                    let msg = vec![
                            format!(
                                "could not find function {verify_function} specified by --verify-function,"
                            ),
                            format!(
                                "consider *{clean_verify_function}* if you want to verify similar functions:"
                            ),
                        ].into_iter()
                        .chain(filtered_functions.iter().map(|f| format!("  - {f}")))
                        .collect::<Vec<String>>()
                        .join("\n");
                    return Err(error(msg));
                }
            }
        }
        Ok(verify_function_exact_match)
    }

    /// Check if the function_name matches
    pub fn includes_function(
        &self,
        function_name: &Fun,
        verify_function_exact_match: bool,
        module: &Path,
    ) -> bool {
        if let UserFilter::Function(_, verify_function) = self {
            let name = friendly_fun_name_crate_relative(&module, function_name);
            if verify_function_exact_match {
                if &name != verify_function && !name.ends_with(&format!("::{}", verify_function)) {
                    return false;
                }
            } else {
                let clean_verify_function = verify_function.trim_matches('*');
                let left_wildcard = verify_function.starts_with('*');
                let right_wildcard = verify_function.ends_with('*');

                if left_wildcard && !right_wildcard {
                    if !name.ends_with(clean_verify_function) {
                        return false;
                    }
                } else if !left_wildcard && right_wildcard {
                    if !name.starts_with(clean_verify_function) {
                        return false;
                    }
                } else if !name.contains(clean_verify_function) {
                    return false;
                }
            }

            true
        } else {
            true
        }
    }
}
