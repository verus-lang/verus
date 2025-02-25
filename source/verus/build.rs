use regex::Regex;

fn main() {
    let output = match std::process::Command::new("rustup")
        .arg("show")
        .arg("active-toolchain")
        .env_remove("RUSTUP_TOOLCHAIN")
        .stderr(std::process::Stdio::inherit())
        .output()
        .map_err(|x| format!("could not execute rustup ({})", x))
    {
        Ok(output) => output,
        Err(err) => panic!("{}", err),
    };
    if !output.status.success() {
        panic!("rustup failed");
    }
    let active_toolchain_re =
        Regex::new(r"^(([A-Za-z0-9.-]+)-(?:aarch64|x86_64)-[A-Za-z0-9]+-[A-Za-z0-9-]+)").unwrap();
    let stdout = match std::str::from_utf8(&output.stdout)
        .map_err(|_| format!("rustup output is invalid utf8"))
    {
        Ok(stdout) => stdout,
        Err(err) => panic!("{}", err),
    };
    let mut captures = active_toolchain_re.captures_iter(&stdout);

    let toolchain = if let Some(cap) = captures.next() {
        let _channel = &cap[2];
        let toolchain = cap[1].to_string();
        if let Some(vargo_toolchain) = std::env::var("VARGO_TOOLCHAIN").ok() {
            if vargo_toolchain != toolchain {
                panic!(
                    "rustup is using the toolchain {toolchain}, we expect {vargo_toolchain}\ndo you have a rustup override set?"
                );
            }
        }
        toolchain
    } else {
        panic!(
            "unexpected output from `rustup show active-toolchain`\nexpected a toolchain override\ngot: {stdout}"
        );
    };

    println!("cargo:rustc-env=VERUS_TOOLCHAIN={toolchain}");
}
