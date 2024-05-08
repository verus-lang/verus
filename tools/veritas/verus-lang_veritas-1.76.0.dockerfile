FROM --platform=linux/amd64 ghcr.io/utaal/verus-lang/verus-base:rust-1.76.0

VOLUME /root/veritas

VOLUME /root/repos-cache
VOLUME /root/z3-cache
VOLUME /root/work
VOLUME /root/output
VOLUME /root/.rustup

ENV REPOS_CACHE_PATH=/root/repos-cache/
ENV Z3_CACHE_PATH=/root/z3-cache/
ENV WORKDIR_PATH=/root/work/
ENV OUTPUT_PATH=/root/output/

WORKDIR /root/veritas
ENTRYPOINT ["/bin/bash", "container-entrypoint.sh"]