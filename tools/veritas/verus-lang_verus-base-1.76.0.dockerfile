FROM --platform=linux/amd64 ghcr.io/utaal/verus-lang/verus-base

RUN /root/.cargo/bin/rustup install 1.76.0
