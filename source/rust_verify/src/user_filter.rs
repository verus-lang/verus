use crate::config::Args;
use crate::util::error;
use crate::verifier::module_name;
use std::collections::HashSet;
use vir::ast::{Fun, Function, Krate, Path, VirErr};
use vir::ast_util::friendly_fun_name_crate_relative;

#[derive(Clone)]
pub enum UserFilter {
    /// No filter (i.e., verify everything)
    None,
    /// Verify modules
    Modules(Vec<ModuleId>),
    /// Verify function
    /// bool argument = uses exact match
    Function(ModuleId, String, bool),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ModuleId {
    Root,
    /// Colon separated, as the user would input
    Module(String),
}

impl UserFilter {
    pub fn is_everything(&self) -> bool {
        matches!(self, UserFilter::None)
    }

    pub fn is_function_filter(&self) -> bool {
        matches!(self, UserFilter::Function(..))
    }

    pub fn from_args(args: &Args, local_krate: &Krate) -> Result<UserFilter, VirErr> {
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

            let module = if args.verify_root {
                ModuleId::Root
            } else {
                ModuleId::Module(args.verify_module[0].clone())
            };
            let exact_match =
                Self::get_is_function_exact_match(&module, func_name, &local_krate.functions)?;
            return Ok(UserFilter::Function(module, func_name.clone(), exact_match));
        }

        if args.verify_module.is_empty() && !args.verify_root {
            return Ok(UserFilter::None);
        }

        let mut modules: Vec<ModuleId> =
            args.verify_module.iter().map(|s| ModuleId::Module(s.clone())).collect();
        if args.verify_root {
            modules.push(ModuleId::Root);
        }

        Ok(UserFilter::Modules(modules))
    }

    pub fn filter_module_ids(&self, module_ids: &Vec<Path>) -> Result<Vec<Path>, VirErr> {
        let mut remaining_modules: HashSet<&ModuleId> = match self {
            UserFilter::None => {
                return Ok(module_ids.clone());
            }
            UserFilter::Modules(m) => m.iter().collect(),
            UserFilter::Function(m, _, _) => std::iter::once(m).collect(),
        };

        let module_ids_to_verify = module_ids
            .iter()
            .filter(|m| {
                // Return true if the ModuleId is in the remaining_modules set,
                // and if so, remove it from the set.
                remaining_modules.take(&module_id_of_path(m)).is_some()
            })
            .cloned()
            .collect();

        // Check if any modules from the user's list didn't appear in the krate modules
        if let Some(mod_name) = remaining_modules.into_iter().next() {
            let mut lines = module_ids
                .iter()
                .filter_map(|m| {
                    let name = module_name(m);
                    (m.segments.len() > 0).then(|| format!("- {name}"))
                })
                .collect::<Vec<_>>();
            lines.sort(); // Present the available modules in sorted order
            let mod_name = match mod_name {
                ModuleId::Root => "[root module]",
                ModuleId::Module(m) => &m,
            };
            let mut msg = vec![
                format!("could not find module {mod_name} specified by --verify-module"),
                format!("available modules are:"),
            ];
            msg.extend(lines);
            msg.push(format!("or use --verify-root"));
            return Err(error(msg.join("\n")));
        }

        Ok(module_ids_to_verify)
    }

    fn get_is_function_exact_match(
        module_id: &ModuleId,
        verify_function: &String,
        funs: &Vec<Function>,
    ) -> Result<bool, VirErr> {
        let mut verify_function_exact_match = false;
        let mut module_fun_names: Vec<String> = funs
            .iter()
            .filter(|f| match &f.x.owning_module {
                None => false,
                Some(m) => module_id == &module_id_of_path(m),
            })
            .map(|f| {
                friendly_fun_name_crate_relative(f.x.owning_module.as_ref().unwrap(), &f.x.name)
            })
            .collect();

        let clean_verify_function = verify_function.trim_matches('*');
        let mut filtered_functions: Vec<&String> =
            module_fun_names.iter().filter(|f| f.contains(clean_verify_function)).collect();

        // no match
        if filtered_functions.len() == 0 {
            module_fun_names.sort();
            let msg = vec![
                format!("could not find function {verify_function} specified by --verify-function"),
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
        Ok(verify_function_exact_match)
    }

    /// Check if the function is included in the filter.
    /// This assumes the function is already in the correct module
    /// (i.e., it only checks the function name).
    pub fn includes_function(&self, function_name: &Fun, module: &Path) -> bool {
        if let UserFilter::Function(_, verify_function, exact_match) = self {
            let name = friendly_fun_name_crate_relative(&module, function_name);
            if *exact_match {
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

fn module_id_of_path(p: &Path) -> ModuleId {
    if p.segments.len() == 0 { ModuleId::Root } else { ModuleId::Module(module_name(p)) }
}
