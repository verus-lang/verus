use std::{io::Write, path::PathBuf};

use git2::Repository;

pub fn record_history_commit(
    record_history_repo: Option<FoundRecordHistoryRepo>,
    deps: &Vec<std::path::PathBuf>,
    deps_prefix: &std::path::PathBuf,
    toml_value: &toml::Value,
) -> Result<(), String> {
    Ok(
        if let Some(FoundRecordHistoryRepo {
            project_dir,
            git_dir,
            reports_dir,
            repo,
            recorder_id,
        }) = record_history_repo
        {
            let project_repo = Repository::discover(project_dir).ok();
            let project_head_shorthand = project_repo.as_ref().and_then(|pr| {
                pr.head().ok().and_then(|h| {
                    if h.is_branch() { h.shorthand().map(|x| x.to_owned()) } else { None }
                })
            });
            let project_head_hash = project_repo.as_ref().and_then(|pr| {
                pr.head()
                    .ok()
                    .and_then(|h| h.peel_to_commit().ok().map(|commit| commit.id().to_string()))
            });
            let signature = git2::Signature::now("nobody", "nobody").unwrap();

            let ref_name = format!(
                "refs/heads/{}/{}",
                recorder_id,
                project_head_shorthand
                    .as_ref()
                    .unwrap_or(&"verus-record--unknown-branch".to_owned())
            );
            let head = repo.find_reference(&ref_name).ok().unwrap_or_else(|| {
                let tree_oid = repo
                    .treebuilder(None)
                    .expect("failed to create a treebuilder for empty init")
                    .write()
                    .expect("failed to write the empty init tree");
                let tree = repo.find_tree(tree_oid).unwrap();
                let _oid = repo
                    .commit(Some(&ref_name), &signature, &signature, "[init]", &tree, &[])
                    .expect("failed to create init commit");
                repo.find_reference(&ref_name)
                    .expect("failed to find reference that was just created")
            });

            fn insert_dir(
                repo: &Repository,
                treebuilder: &mut git2::TreeBuilder,
                all_deps: &Vec<PathBuf>,
                deps_prefix: &PathBuf,
                cur_path: PathBuf,
            ) -> Result<(), String> {
                let cur_path_components = cur_path.components().count();
                let here: std::collections::HashSet<_> = all_deps
                    .iter()
                    .filter(|d| d.starts_with(&cur_path))
                    .map(|d| {
                        (
                            d.components().skip(cur_path_components).next().unwrap(),
                            d.components().skip(cur_path_components).count() == 1,
                        )
                    })
                    .collect();
                for (name, is_file) in here.into_iter() {
                    let fs_path = deps_prefix.join(&cur_path).join(&name);

                    if is_file {
                        assert!(fs_path.is_file());
                        let contents = std::fs::read_to_string(&fs_path).map_err(|err| {
                            format!(
                                "{}, file name: {}. Check if this file can be opened.",
                                err,
                                fs_path.display(),
                            )
                        })?;
                        let content_oid = repo.blob(contents.as_bytes()).unwrap_or_else(|_| {
                            panic!(
                                "failed to create a git blob for file {}",
                                cur_path.join(&name).display()
                            )
                        });
                        treebuilder.insert(name.as_os_str(), content_oid, 0o100644).unwrap_or_else(
                            |_| panic!("failed to insert file {}", cur_path.join(&name).display()),
                        );
                    } else {
                        let mut inner_treebuilder =
                            repo.treebuilder(None).expect("failed to create treebuilder");
                        insert_dir(
                            repo,
                            &mut inner_treebuilder,
                            all_deps,
                            deps_prefix,
                            cur_path.join(&name),
                        )?;
                        let tree_oid = inner_treebuilder.write().unwrap_or_else(|_| {
                            panic!(
                                "failed to write treebuilder for {}",
                                cur_path.join(&name).display()
                            )
                        });
                        treebuilder.insert(name.as_os_str(), tree_oid, 0o040000).unwrap_or_else(
                            |_| panic!("failed to insert file {}", cur_path.join(&name).display()),
                        );
                    }
                }
                Ok(())
            }

            let mut treebuilder = repo.treebuilder(None).expect("failed to create treebuilder");
            insert_dir(&repo, &mut treebuilder, deps, deps_prefix, PathBuf::new())?;

            let tree_oid = treebuilder.write().expect("failed to write treebuilder");
            let tree = repo.find_tree(tree_oid).unwrap();
            let parent_commit = repo.find_commit(head.target().unwrap()).unwrap();

            let mut toml_value = toml_value.as_table().expect("unexpected toml value").clone();
            let mut record_history_table = toml::Table::new();
            if let Some(project_head_shorthand) = &project_head_shorthand {
                record_history_table.insert(
                    "ref-shorthand".to_owned(),
                    toml::Value::String(project_head_shorthand.to_owned()),
                );
            }
            if let Some(project_head_hash) = &project_head_hash {
                record_history_table.insert(
                    "ref-hash".to_owned(),
                    toml::Value::String(project_head_hash.to_owned()),
                );
            }
            record_history_table
                .insert("recorder-id".to_owned(), toml::Value::String(recorder_id.to_owned()));
            toml_value
                .insert("record-history".to_owned(), toml::Value::Table(record_history_table));

            let report_msg = toml::to_string(&toml_value)
                .map_err(|x| format!("Could not encode TOML value with error message: {}", x))?;

            let report_filename = {
                use chrono::prelude::*;
                let local: DateTime<Local> = Local::now();
                let formatted = local.format("%Y-%m-%d-%H-%M-%S-%3f");
                formatted.to_string() + ".toml"
            };
            let report_path = reports_dir.join(report_filename);
            {
                let mut report = std::fs::File::create(&report_path).unwrap_or_else(|_| {
                    panic!("cannot create report file {}", report_path.display())
                });
                report.write_all(report_msg.as_bytes()).expect("failed to write report");
                report.flush().expect("failed to write report");
            }

            let _commit_oid = repo.commit(
                Some(&ref_name),
                &signature,
                &signature,
                &report_msg,
                &tree,
                &[&parent_commit],
            );
            eprintln!(
                "{} {}",
                yansi::Paint::blue("recorded crate source and verification results at"),
                git_dir.display()
            );
        },
    )
}

pub fn print_verification_results(record: bool, verus_full_stdout: &Vec<u8>) {
    if !record {
        let verification_results = {
            let stdout_json: serde_json::Map<String, serde_json::Value> = serde_json::from_str(
                std::str::from_utf8(verus_full_stdout).expect("invalid rust_verify output"),
            )
            .expect("cannot parse rust_verify output");
            let verification_results =
                stdout_json.get("verification-results").expect("unexpected rust_verify output");
            let encountered_vir_error = verification_results
                .get("encountered-vir-error")
                .and_then(|x| x.as_bool())
                .expect("unexpected rust_verify output");
            if !encountered_vir_error {
                let verified = verification_results
                    .get("verified")
                    .and_then(|x| x.as_i64())
                    .expect("unexpected rust_verify output");
                let errors = verification_results
                    .get("errors")
                    .and_then(|x| x.as_i64())
                    .expect("unexpected rust_verify output");
                let is_verifying_entire_crate = verification_results
                    .get("is-verifying-entire-crate")
                    .and_then(|x| x.as_bool())
                    .expect("unexpected rust_verify output");
                Some((verified, errors, is_verifying_entire_crate))
            } else {
                None
            }
        };

        if let Some((verified, errors, is_verifying_entire_crate)) = verification_results {
            println!(
                "verification results:: {} verified, {} errors{}",
                verified,
                errors,
                if !is_verifying_entire_crate {
                    " (partial verification with `--verify-*`)"
                } else {
                    ""
                }
            );
        }
    }
}

pub struct FoundRecordHistoryRepo {
    pub project_dir: std::path::PathBuf,
    pub git_dir: std::path::PathBuf,
    pub reports_dir: std::path::PathBuf,
    pub repo: Repository,
    pub recorder_id: String,
}

fn gernerate_recorder_id() -> String {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    const CHARSET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
                            abcdefghijklmnopqrstuvwxyz\
                            0123456789";
    (0..32)
        .map(|_| {
            let idx = rng.gen_range(0..CHARSET.len());
            CHARSET[idx] as char
        })
        .collect()
}

pub fn find_record_history_repo(
    record_history_dir: Option<(std::path::PathBuf, std::path::PathBuf)>,
) -> Result<Option<FoundRecordHistoryRepo>, String> {
    let record_history_repo = if let Some((project_dir, history_dir)) = record_history_dir {
        let git_dir = history_dir.join("git");
        let reports_dir = history_dir.join("reports");
        let recorder_id_file = history_dir.join("recorder-id");
        let repo = if !git_dir.exists() {
            git2::Repository::init_bare(&git_dir)
        } else {
            git2::Repository::open_bare(&git_dir)
        };
        if !reports_dir.exists() {
            std::fs::create_dir(&reports_dir).unwrap_or_else(|_| {
                panic!("cannot create reports directory {}", reports_dir.display())
            });
        }
        let recorder_id = if !recorder_id_file.exists() {
            let new_recorder_id = gernerate_recorder_id();
            let mut fw = std::fs::File::create(recorder_id_file)
                .unwrap_or_else(|_| panic!("cannot open file in {}", history_dir.display()));
            fw.write_all(new_recorder_id.as_bytes()).expect("failed to write recorder-id file");
            fw.flush().expect("failed to write recorder-id file");
            new_recorder_id
        } else {
            std::fs::read_to_string(&recorder_id_file)
                .unwrap_or_else(|_| panic!("cannot read file {}", recorder_id_file.display()))
        };
        let repo = repo.map_err(|err| {
            format!("failed to open record-history repo at {} ({})", git_dir.display(), err)
        })?;
        Some(FoundRecordHistoryRepo { project_dir, git_dir, reports_dir, repo, recorder_id })
    } else {
        None
    };
    Ok(record_history_repo)
}
