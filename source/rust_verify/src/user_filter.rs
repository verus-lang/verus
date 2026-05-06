use crate::buckets::{Bucket, BucketId};
use crate::config::Args;
use crate::util::error;
use crate::verifier::module_name;
use std::collections::HashSet;
use std::sync::Arc;
use vir::ast::{Fun, Function, Krate, VirErr};
use vir::ast_util::{friendly_fun_name_crate_relative, parse_path_segments_from_user_str};

#[derive(Clone, Debug)]
pub enum UserFilter {
    /// No filter (i.e., verify everything)
    None,
    /// Verify modules
    Modules(Vec<ModuleId>),
    /// Verify function
    Function(ModuleId, String, HashSet<Fun>),
}

type ModuleId = vir::ast::Idents;

fn root_module_id() -> ModuleId {
    Arc::new(vec![])
}

impl UserFilter {
    pub fn is_everything(&self) -> bool {
        matches!(self, UserFilter::None)
    }

    pub fn is_function_filter(&self) -> bool {
        matches!(self, UserFilter::Function(..))
    }

    pub fn from_args(args: &Args, local_krate: &Krate) -> Result<UserFilter, VirErr> {
        let validate_module_name = |s: &str| -> Result<vir::ast::Idents, VirErr> {
            let segments = parse_path_segments_from_user_str(s)?;
            if local_krate.modules.iter().find(|m| m.x.path.segments == segments).is_none() {
                let mut lines = local_krate
                    .modules
                    .iter()
                    .filter_map(|m| {
                        let name = module_name(&m.x.path);
                        (m.x.path.segments.len() > 0).then(|| format!("- {name}"))
                    })
                    .collect::<Vec<_>>();
                lines.sort(); // Present the available modules in sorted order
                let mut msg = vec![
                    format!(
                        "could not find module {s} specified by --verify-module or --verify-only-module"
                    ),
                    format!("available modules are:"),
                ];
                msg.extend(lines);
                msg.push(format!("or use --verify-root"));
                return Err(error(msg.join("\n")));
            }
            Ok(segments)
        };

        if let Some(func_name) = &args.verify_function {
            assert!(!(args.verify_only_module.is_empty() && !args.verify_root));
            assert!(!(args.verify_module.len() + (if args.verify_root { 1 } else { 0 }) > 1));
            assert!(args.verify_module.is_empty());

            let module = if args.verify_root {
                root_module_id()
            } else {
                let s = &args.verify_only_module[0];
                validate_module_name(s)?
            };
            let matches = Self::get_matches(&module, func_name, &local_krate.functions)?;
            return Ok(UserFilter::Function(module, func_name.clone(), matches));
        }

        if args.verify_module.is_empty() && args.verify_only_module.is_empty() && !args.verify_root
        {
            return Ok(UserFilter::None);
        }

        let mut modules: Vec<ModuleId> = args
            .verify_module
            .iter()
            .map(|s| {
                let arg_segments = validate_module_name(s)?;
                let mods = local_krate
                    .modules
                    .iter()
                    .map(|m| m.x.path.segments.clone())
                    .filter(|m_segments| {
                        vir::ast_util::path_segments_match_prefix(m_segments, &arg_segments)
                    })
                    .collect::<Vec<ModuleId>>();
                Ok(mods)
            })
            .collect::<Result<Vec<Vec<ModuleId>>, VirErr>>()?
            .into_iter()
            .flatten()
            .collect();

        modules.extend(
            args.verify_only_module
                .iter()
                .map(|s| validate_module_name(s))
                .collect::<Result<Vec<ModuleId>, VirErr>>()?,
        );

        if args.verify_root {
            modules.push(root_module_id());
        }

        Ok(UserFilter::Modules(modules))
    }

    pub fn filter_modules(
        &self,
        modules: &Vec<vir::ast::Module>,
    ) -> Result<Vec<vir::ast::Module>, VirErr> {
        let mut remaining_modules: HashSet<&ModuleId> = match self {
            UserFilter::None => {
                return Ok(modules.clone());
            }
            UserFilter::Modules(m) => m.iter().collect(),
            UserFilter::Function(m, _, _) => std::iter::once(m).collect(),
        };

        let module_ids_to_verify = modules
            .iter()
            .filter(|m| {
                // Return true if the ModuleId is in the remaining_modules set,
                // and if so, remove it from the set.
                remaining_modules.take(&m.x.path.segments).is_some()
            })
            .cloned()
            .collect();

        assert!(remaining_modules.is_empty(), "Some modules were not found in the krate modules");

        Ok(module_ids_to_verify)
    }

    /// Filter the bucket list to only include buckets that contain some
    /// element accepted by the filter.
    /// Assumes the input vector is already restricted to the modules
    /// as returned by `filter_module_ids`.
    pub fn filter_buckets(&self, vec: Vec<(BucketId, Bucket)>) -> Vec<(BucketId, Bucket)> {
        match self {
            UserFilter::None | UserFilter::Modules(_) => vec,
            UserFilter::Function(..) => {
                vec.into_iter()
                    .filter(|(_, bucket)| {
                        // Check if any function in the bucket is accepted.
                        for fun in &bucket.funs {
                            if self.includes_function(fun) {
                                return true;
                            }
                        }
                        return false;
                    })
                    .collect()
            }
        }
    }

    /// Get the functions that match the given string.
    ///
    /// The first part of this process is to
    /// infer whether this is an "exact match" filter.
    /// (If the user doesn't supply any * in the pattern, then it is usuall
    /// exact - however, if there is no exact match, but there is _exactly one_
    /// partial match, then we upgrade to a partial match, i.e., return false)
    ///
    /// Errors if there is no match.
    fn get_matches(
        module_id: &ModuleId,
        function_pattern: &String,
        funs: &Vec<Function>,
    ) -> Result<HashSet<Fun>, VirErr> {
        let module_fun_names: Vec<(Fun, String)> = funs
            .iter()
            .filter(|f| match &f.x.owning_module {
                None => false,
                Some(m) => module_id == &m.segments,
            })
            .map(|f| {
                let name = friendly_fun_name_crate_relative(
                    f.x.owning_module.as_ref().unwrap(),
                    &f.x.name,
                );
                (f.x.name.clone(), name)
            })
            .collect();

        // First, get the matches without doing anything fancy:
        // If the user provides a * pattern, then we filter according to the * pattern;
        // if the user provides an exact match (no *), then filter as an exact match.
        // If we find anything this way, we're done.
        let matches = Self::get_matches_strictly_by_pattern(function_pattern, &module_fun_names);
        if matches.len() > 0 {
            return Ok(matches.into_iter().map(|(f, _)| f.clone()).collect());
        }

        // Get all substring matches, even if the user didn't use any * in their pattern.
        // We might use of these automatically, or if not, this list will at least help us
        // print an informative error message.
        let substring_matches =
            Self::get_all_substring_matches(function_pattern, &module_fun_names);

        let clean = function_pattern.trim_matches('*');
        if clean == function_pattern {
            // If there's no exact match, but there is *exactly one* substring match,
            // then we go ahead and use that function.
            if substring_matches.len() == 1 {
                return Ok(substring_matches.iter().map(|f| f.0.clone()).collect());
            } else if substring_matches.len() > 1 {
                let mut filtered_functions =
                    substring_matches.iter().map(|f| f.1.clone()).collect::<Vec<String>>();
                filtered_functions.sort();
                let msg = vec![
                    format!(
                        "more than one match found for --verify-function {function_pattern}, consider using wildcard *{function_pattern}* to verify all matched results,"
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
            if substring_matches.len() >= 1 {
                let mut filtered_functions =
                    substring_matches.iter().map(|f| f.1.clone()).collect::<Vec<String>>();
                filtered_functions.sort();
                let msg = vec![
                    format!(
                        "could not find function {function_pattern} specified by --verify-function,"
                    ),
                    format!("consider *{clean}* if you want to verify similar functions:"),
                ]
                .into_iter()
                .chain(filtered_functions.iter().map(|f| format!("  - {f}")))
                .collect::<Vec<String>>()
                .join("\n");
                return Err(error(msg));
            }
        }

        // If there were absolutely no substring matches, then we fail by printing
        // out every possible function in the module.
        let mut all_functions = module_fun_names.into_iter().map(|f| f.1).collect::<Vec<String>>();
        all_functions.sort();
        let msg = vec![
            format!("could not find function {function_pattern} specified by --verify-function"),
            format!("available functions are:"),
        ]
        .into_iter()
        .chain(all_functions.iter().map(|f| format!("  - {f}")))
        .collect::<Vec<String>>()
        .join("\n");
        return Err(error(msg));
    }

    fn get_matches_strictly_by_pattern<'a>(
        function_pattern: &String,
        funs: &'a Vec<(Fun, String)>,
    ) -> Vec<&'a (Fun, String)> {
        let clean = function_pattern.trim_matches('*');
        let left_wildcard = function_pattern.starts_with('*');
        let right_wildcard = function_pattern.ends_with('*');

        funs.iter()
            .filter(|(_, name)| {
                if left_wildcard && !right_wildcard {
                    name.ends_with(clean)
                } else if !left_wildcard && right_wildcard {
                    name.starts_with(clean)
                } else if left_wildcard && right_wildcard {
                    name.contains(clean)
                } else {
                    name == clean
                }
            })
            .collect()
    }

    fn get_all_substring_matches<'a>(
        function_pattern: &String,
        funs: &'a Vec<(Fun, String)>,
    ) -> Vec<&'a (Fun, String)> {
        let clean = function_pattern.trim_matches('*');
        funs.iter().filter(|(_, name)| name.contains(clean)).collect()
    }

    /// Check if the function is included in the filter.
    /// This assumes the function is already in the correct module
    /// (i.e., it only checks the function name).
    pub fn includes_function(&self, function_name: &Fun) -> bool {
        if let UserFilter::Function(_module_id, _function, matches) = self {
            matches.contains(function_name)
        } else {
            true
        }
    }
}
