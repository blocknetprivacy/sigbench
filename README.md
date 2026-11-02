# Blocknet Bench 3

A benchmark for Blocknet's Faraday v2 post-quantum private transactions. It runs every part of the
new design live on your computer and saves a results file. Your results help us plan the next
stages of development.

Share your results file in https://uproar.chat/invite/blocknet. Thank you.

## Download and run

Get the file for your system from the [latest release](https://github.com/blocknetprivacy/sigbench/releases/latest).

| System | File | How to start |
|---|---|---|
| macOS, Apple silicon | `blocknet-bench3-arm64-macos.tar.gz` | Unpack, then right-click the file and choose Open (first time only) |
| Linux, x86-64 | `blocknet-bench3-amd64-linux.tar.gz` | Unpack, then run `./blocknet-bench3-amd64-linux` |
| Windows, x86-64 | `blocknet-bench3-amd64-windows.zip` | Unpack, then run the .exe. If SmartScreen asks, choose More info, then Run anyway |

Needs an x86-64 CPU with AVX2, AES-NI and PCLMULQDQ (Intel Haswell 2013 or newer, AMD Zen or newer),
or an Apple silicon Mac. The run takes about 3 minutes. The window shows English or Chinese, based on
your system language; you can switch on the title screen.

## What it measures

Every number is a live measurement on your machine. A step starts only when the window reaches it.

1. Address: makes a new wallet and its 58-character post-quantum address.
2. Anonymity set: builds 1,048,576 real coin commitments.
3. Send transaction: proves and checks 400 private transactions (2, 4, 8 and 16 inputs and outputs),
   one core, every input a new coin from the set.
4. Wallet scan: scans every output and finds the ones sent to this wallet (ML-KEM-768).
5. Block: packs a 2 MB block, checks every proof and nullifier from the bytes, then prunes it.
6. Mining: BLAKE2b-512 proof of work (personalization `blocknet/pow/v1`) on one core, all cores,
   and the GPU on macOS.
7. Report: writes `reports/blocknet-bench3-<date>-<time>.toml` and opens it.

The results file lists your hardware (CPU, cores, RAM, GPU, OS, power source, CPU features) and the
timings, with the spread of each (min, median, p95, max).

## Build from source

The Rust toolchain is pinned in `rust-toolchain.toml`. The prover is C++23 and is built by
`vole/build.rs`.

    cargo build --release -p showcase
    ./target/release/showcase

`make` builds all three release binaries from a Mac (Linux and Windows through
[cargo-zigbuild](https://github.com/rust-cross/cargo-zigbuild)). GitHub Actions builds the
release binaries the same way.

## Layout

| Path | What it is |
|---|---|
| `showcase/` | The benchmark program (window, steps, report) |
| `vole/` | Rust bindings to the prover and the transaction wire format |
| `spend/` | The zk-VOLEitH spend proof in C++ |
| `src/` | The older command-line benchmark (`sig-bench`) |

The previous version, sig-bench 2 with the Faraday V1 STARK, is on the
[`sigbenchv2`](https://github.com/blocknetprivacy/sigbench/tree/sigbenchv2) branch.

## Licenses

See `NOTICE`.
