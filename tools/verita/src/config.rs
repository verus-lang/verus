use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, Hash, Clone)]
pub struct RunConfigurationProject {
    pub name: String,
    pub git_url: String,
    pub refspec: String,
    pub crate_roots: Vec<String>,
    pub extra_args: Option<Vec<String>>,
    pub prepare_script: Option<String>,
    pub prepare_script_windows: Option<String>,
    #[serde(default)]
    pub cargo_verus: bool,
    #[serde(default)]
    pub requires_singular: bool,
    #[serde(default)]
    pub ignore: bool,
}

#[derive(Debug, Serialize, Deserialize, Hash)]
pub struct RunConfiguration {
    pub verus_git_url: String,
    pub verus_refspec: String,
    pub verus_features: Vec<String>,
    pub verus_extra_args: Option<Vec<String>>,
    // #[serde(default = true)]
    // verus_verify_vstd: bool,
    #[serde(rename = "project")]
    pub projects: Vec<RunConfigurationProject>,
}
