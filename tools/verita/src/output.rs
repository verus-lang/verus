use serde::{Deserialize, Serialize};

#[derive(Deserialize, Hash)]
#[serde(rename_all = "kebab-case")]
pub struct VerusOutputSmtTimesMs {
    smt_init: u64,
    smt_run: u64,
    total: u64,
}

#[derive(Deserialize, Hash)]
#[serde(rename_all = "kebab-case")]
pub struct VerusOutputTimesMs {
    estimated_cpu_time: u64,
    total: u64,
    // Absent when Verus exits before reaching SMT (e.g., a VIR error).
    #[serde(default)]
    smt: Option<VerusOutputSmtTimesMs>,
}

#[derive(Debug, Serialize, Deserialize, Hash, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct VerusOutputVerificationResults {
    encountered_vir_error: bool,
    success: Option<bool>,
    verified: Option<u64>,
    errors: Option<u64>,
    is_verifying_entire_crate: Option<bool>,
}

#[derive(Deserialize, Hash)]
#[serde(rename_all = "kebab-case")]
pub struct VerusOutput {
    times_ms: VerusOutputTimesMs,
    verification_results: VerusOutputVerificationResults,
}
