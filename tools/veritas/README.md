NOTE: Veritas is highly experimental at this stage. It should already be useful,
but it is likely to break when encountering unexpected situations.

Veritas is a rust crater-alike tool to run a version of verus on a number of projects,
generating a report of verification success/failures and verification performance data.

Running veritas requires docker (or another container runtime). 


### Running Veritas

1. Run `bash build_images.sh` to create the Docker images Veritas uses locally
    - This only needs to be done when running Veritas for the first time or after an update to Verus that upgrades its Rust version. 
2. Run `bash run.sh path_to_run_configuration.toml`. There is an example run configuration in this directory. 
    - Running that command will start an ephemeral container and will create four permanent docker volumes: `verus-veritas-cargo-cache`, `verus-veritas-repo-cache`, `verus-veritas-rustup`, `verus-veritas-z3-cache`. These volumes cache dowloaded repositories, binaries, and other files, to reduce unnecessary traffic when performing multiple runs.

After an update to Verus that moves to a new version of Rust, Veritas may leave several obsolete volumes that can be removed to free up disk space. To remove these volumes:

1. Run `docker volume ls | grep -E rustup\|cargo` to list all versions of the volumes that cache `cargo` and `rustup`-related files. 
    - The volume names will have the format `verus-veritas-cargo-<version number>-cache` and `verus-veritas-rustup-<version number>`. 
    - You may also see volume names without version numbers from older versions of Veritas; these can also safely be deleted.
2. Run `docker volume rm volume_name`, replacing `volume_name` with the names of `cargo` and `rustup` volumes with old version numbers. 