use clap::Parser;
use line_count_lib::attribution::CodeKind;
use line_count_lib::config::Config;
use line_count_lib::config::RunMode;
use line_count_lib::deps::get_dependencies;
use line_count_lib::files::find_rust_files;
use line_count_lib::stats::Summary;
use line_count_lib::*;

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::rc::Rc;

use tabled::settings::Alignment;
use tabled::settings::Modify;
use tabled::settings::Style;
use tabled::settings::object::{Columns, Rows};
use tabled::settings::style::On;

use self::cli::LineCountArgs;

mod cli;

fn run(config: Config, run_mode_paths: RunMode) -> Result<(), String> {
    let config = Rc::new(config);
    let (root_path, files) = match run_mode_paths {
        RunMode::DepsPath(path) => get_dependencies(&path)?,
        RunMode::Files(paths) => {
            find_rust_files(&paths).map_err(|e| format!("failed to find rust files: {e:?}"))?
        }
    };

    let file_stats = files
        .iter()
        .map(|f| process_file(config.clone(), &root_path.join(f)).map(|fs| (f, fs)))
        .collect::<Result<Vec<_>, String>>()?;

    if config.print_all {
        eprintln!("{:18} | {:30} | {}", "Category", "Detailed contents", "");
        eprintln!();
        for (file, file_stats) in file_stats.iter() {
            eprintln!("# {}", file.display());
            for l in file_stats.lines.iter() {
                eprintln!(
                    "{:18} | {:30} | {}",
                    sorted_vec_to_fit_string(&btree_set_to_sorted_vec(&l.kinds)[..], 30),
                    sorted_vec_to_fit_string(&btree_set_to_sorted_vec(&l.line_content)[..], 30),
                    l.text
                );
            }
            eprintln!();
        }
    }

    let file_summaries = file_stats
        .iter()
        .map(|(name, file_stats)| {
            let mut lines_by_kind = BTreeMap::new();
            for l in file_stats.lines.iter() {
                let mut kinds = l.kinds.clone();
                if kinds.contains(&CodeKind::Exec)
                    || kinds.contains(&CodeKind::Proof)
                    || kinds.contains(&CodeKind::Spec)
                {
                    kinds
                        .retain(|x| matches!(x, CodeKind::Exec | CodeKind::Proof | CodeKind::Spec));
                }
                *lines_by_kind.entry(btree_set_to_sorted_vec(&kinds)).or_default() += 1;
            }
            (name, Summary { lines_by_kind })
        })
        .collect::<Vec<_>>();

    let total: Summary = file_summaries.iter().map(|(_, fs)| fs).cloned().sum();

    let kinds: BTreeSet<_> =
        file_summaries.iter().flat_map(|(_, s)| s.lines_by_kind.keys()).cloned().collect();

    if !config.json {
        let columns: Vec<_> = {
            let mut columns: Vec<_> = vec![
                BTreeSet::from([CodeKind::Trusted]),
                BTreeSet::from([CodeKind::Spec]),
                BTreeSet::from([CodeKind::Proof]),
                BTreeSet::from([CodeKind::Exec]),
                BTreeSet::from([CodeKind::Proof, CodeKind::Exec]),
                BTreeSet::from([CodeKind::Comment]),
                BTreeSet::from([CodeKind::Layout]),
                BTreeSet::from([]),
            ];
            let other_columns: Vec<_> = kinds
                .difference(&BTreeSet::from_iter(columns.iter().map(btree_set_to_sorted_vec)))
                .map(|h| BTreeSet::from_iter(h.iter().cloned()))
                .collect();
            columns.extend(other_columns);
            columns.iter().map(btree_set_to_sorted_vec).collect()
        };

        let mut table_data: Vec<Vec<String>> = file_summaries
            .iter()
            .map(|(f, s)| {
                Some(f.display().to_string())
                    .into_iter()
                    .chain(
                        columns.iter().map(|k| format!("{}", s.lines_by_kind.get(k).unwrap_or(&0))),
                    )
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        table_data.insert(
            0,
            Some("file".to_owned())
                .into_iter()
                .chain(columns.iter().map(|k| {
                    if k.is_empty() {
                        format!("unaccounted")
                    } else {
                        k.iter().map(|x| format!("{:?}", x)).collect::<Vec<_>>().join("+")
                    }
                }))
                .collect(),
        );
        table_data.push(
            Some("total".to_owned())
                .into_iter()
                .chain(
                    columns.iter().map(|k| format!("{}", total.lines_by_kind.get(k).unwrap_or(&0))),
                )
                .collect(),
        );

        let mut table = tabled::builder::Builder::from(table_data).build();
        table
            .with(Style::markdown())
            .with(Modify::new(Columns::new(1..=kinds.len() + 1)).with(Alignment::right()))
            .with(
                Modify::new(Rows::last()).with::<tabled::settings::Border<On, On, On, On>>(
                    tabled::settings::Border::default()
                        .corner_top_left('|')
                        .corner_top_right('|')
                        .top('-'),
                ),
            );
        println!("{}", table);
    } else {
        let kinds_map: BTreeMap<_, _> = kinds
            .iter()
            .map(|k| {
                (
                    k,
                    k.iter()
                        .map(|x| format!("{:?}", x).to_lowercase())
                        .collect::<Vec<_>>()
                        .join(","),
                )
            })
            .collect();
        let json = serde_json::json!({
            "kinds": kinds_map.iter().collect::<Vec<(_, _)>>(),
            "files": file_summaries.iter().map(|(f, s)| {
                (f.display().to_string(),
                     s.lines_by_kind.iter().map(|(k, v)| (kinds_map[k].clone(), v)).collect::<BTreeMap<_, _>>())
            }).collect::<BTreeMap<_, _>>(),
            "total": total.lines_by_kind.iter().map(|(k, v)| (kinds_map[k].clone(), v)).collect::<BTreeMap<_, _>>()
        });
        println!("{}", serde_json::to_string_pretty(&json).expect("invalid json"));
    }

    Ok(())
}

fn main() {
    let args = LineCountArgs::parse();
    if let Err(e) = args.validate() {
        eprintln!("{e}");
        return;
    }

    let (config, run_mode) = args.separate_config();

    match run(config, run_mode) {
        Ok(()) => (),
        Err(err) => {
            eprintln!("error: {}", err);
            std::process::exit(1);
        }
    }
}
