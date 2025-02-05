FROM --platform=linux/amd64 ghcr.io/utaal/verus-lang/verus-deps

RUN /root/.cargo/bin/rustup install 1.82.0
