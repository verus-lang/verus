FROM --platform=linux/amd64 ubuntu:24.04

COPY rustup.sh /root/rustup.sh
RUN \
  DEBIAN_FRONTEND=noninteractive apt-get update -y && \
  DEBIAN_FRONTEND=noninteractive apt-get install -y curl unzip && \
  cd /root && \
    sh rustup.sh --default-toolchain none -y && \
    rm rustup.sh && \
    . "$HOME/.cargo/env" && \
    rustup install 1.79.0-x86_64-unknown-linux-gnu && \
    curl -LO 'https://github.com/verus-lang/verus/releases/download/release%2F0.2024.10.31.141c73e/verus-0.2024.10.31.141c73e-x86-linux.zip' && \
    unzip verus-0.2024.10.31.141c73e-x86-linux.zip && \
    rm verus-0.2024.10.31.141c73e-x86-linux.zip && \
    mv verus-x86-linux /opt/verus && \
    echo 'export PATH="/opt/verus:$PATH"' >> ~/.bashrc && \
    echo 'export PATH="/opt/verus:$PATH"' >> ~/.profile && \
    mkdir /root/cwd

ENV PATH=/opt/verus:/root/.cargo/bin:$PATH

WORKDIR /root/cwd
