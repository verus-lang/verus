FROM --platform=linux/amd64 ubuntu:mantic

RUN DEBIAN_FRONTEND=noninteractive apt-get update && apt-get install -y \
    build-essential curl wget singular git unzip openssh-client pkg-config libssl-dev

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain none
