FROM --platform=linux/amd64 verus-deps

RUN /root/.cargo/bin/rustup install 1.88.0
