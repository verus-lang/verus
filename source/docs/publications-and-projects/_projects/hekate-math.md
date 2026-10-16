---
title: "Binary Tower Field Arithmetic for Zero-Knowledge Provers"
date: 2026-09-10
type: project
code: https://github.com/oumuamua-labs/hekate-math
---
GF(2^8) to GF(2^256) tower field arithmetic with NEON carry-less multiply. Tower multiply and inverse, the NEON kernels, and the additive FFT are proven in Verus against a GF(2^k) model, with the trusted base and open obligations in [TRUSTED_AXIOMS.md](https://github.com/oumuamua-labs/hekate-math/blob/main/verus/TRUSTED_AXIOMS.md).