# sig-bench

Head-to-head benchmark of the **legacy** Blocknet transaction signature against the
**new** Faraday post-quantum spend proof, plus the Faraday **block fold** and the PQC
**transaction / block wire sizes**. It signs/proves and verifies 100 of each (configurable)
and reports **low / average / high** for time, CPU, and memory.

Both sides call the *real* code, not a re-implementation:

| | legacy | new |
|---|---|---|
| what | RingCT CLSAG ring signature | Faraday unified spend STARK proof |
| from | `blocknet_crypto` (the node's consensus crypto) | `pqc_poc::faraday_fold` (the foldable option-B DSL port) |
| curve / field | Ristretto255, ring size 16 | KoalaBear + Poseidon2, Plonky3 |
| security | classical (pre-quantum) | post-quantum (hash-based) |
| one op proves | key ownership + amount linking | membership + key image + balance |
| per-tx proof | 1120 bytes | ~238 KB in this snapshot; about 1.4 MB at the fork's final settings (relay) |
| on-chain cost | ~6 KB/tx (ring inline) | ~2.3 KB/tx metadata + one O(1) folded proof per block |

"sign/prove" and "verify" are timed **separately** for both. The new side is the
**foldable** circuit: after the per-tx measurements it proves two real spends and **folds
them into one block proof** (the O(1) block-storage architecture, `pqc_poc::faraday_fold`),
then measures the Faraday PQC transaction and block wire sizes offline against the real
schema. Nothing touches a live chain.

It also benchmarks the **mining proof-of-work hash**: the current Argon2id 2 GiB
(`crypto-rs/src/pow.rs`) against the candidates for the fork, such as Argon2d 512 MiB. Both use t=1, p=1,
version 0x13 and a 32-byte output. The 2 GiB reproduction is proven byte-identical to the
real `blocknet_pow_hash` before timing.

## What it measures

For each of the four signature operations (legacy sign, legacy verify, new prove, new
verify), over N iterations:

- **time**  -- wall-clock per operation (`std::time::Instant`).
- **cpu**   -- CPU utilization per operation: process CPU time (all threads, via
  `getrusage` on unix / `GetProcessTimes` on Windows) over wall time. 100% = one core
  fully busy; higher means multiple cores.
- **memory** -- resident set size, sampled on a background thread across each suite,
  reported as low / average / high (+ peak). Validated against the OS's own
  `maximum resident set size`.

For the mining hash, each memory level reports low / average / high time and hashrate
(H/s) over N iterations (a warmup hash is discarded first). Levels that would need more
RAM than is safe on the machine are skipped. The memory footprint is the level itself
(the Argon2 memory cost), so it is not separately sampled.

For the **Faraday tx / block** panel (offline, real schema): the bench builds a demo PQC
transaction and block in the on-the-wire format from the spec (`faraday_tx.rs`: 1017-byte
outputs, key images, tree root, inherited block header, sha3-256 ids), serializes them
byte-exact, folds two real spends into one block proof, and reports the relay tx size, the
on-chain per-tx metadata, the folded block-proof size + fold time, and how many txs fit a
2 MB block. There are no PQC tx/block structs in the node yet, so this is the reference
wire model; the proof/ciphertext contents are opaque fixed-width blobs but every length is
exact and the folded proof is real.

Two correctness gates run before any timing, and abort on failure:
1. the Faraday circuit's conformance check (the DSL W32 compression == the standard
   KoalaBear Poseidon2 permutation), and
2. a RingCT sign -> verify round-trip.

## Build

Requires the pinned nightly Rust toolchain in `rust-toolchain.toml` (Plonky3 0.8.0 uses nightly-only
features). From the repo root:

```sh
rustup toolchain install
cargo build --release
```

The repo builds alone. `pqc/` holds the Faraday circuit code the bench runs, and
`patches/p3-recursion` is Plonky3-recursion 485455c with one change: a public accessor for a
child proof's preprocessed commitment targets. `blocknet_crypto` comes from
blocknetprivacy/core at a pinned commit and is statically linked, so
`target/release/sig-bench` is self-contained (only system libraries are loaded at runtime).

## Run

```sh
./target/release/sig-bench
```

No flags: it always runs 100 signature iterations each side and 5 mining-hash iterations
for each PoW. The 2 GiB hash allocates 2 GiB of RAM per hash, so on an 8 GiB machine it
stresses memory. Levels that would need more RAM than is safe are skipped
automatically. After the suites, the bench proves two spends and folds them into one block
proof for the Faraday tx/block panel; that fold is real and adds ~1 minute.

On a unix terminal this runs as a **live full-screen dashboard**: the two suites fill
progress bars as iterations land, an equalizer marks the active suite, a head-to-head
builds live, and a plasma background throbs on every completed signature. Controls:

```
  q   quit         (also Ctrl-C; the terminal is always restored on exit)
  v   toggle the plasma background
```

When it finishes, press `q` to drop back to the shell, where the final numbers are
printed as a colored, box-drawn report (so they persist in your scrollback).

When output is piped/redirected, on Windows, or with `NO_COLOR` set, it skips the live
view and prints only that static report.

## Giving it to a friend

- **Same OS + CPU arch as your build machine:** copy the single file
  `target/release/sig-bench`. No toolchain, no source, no extra files needed.
- **Different OS/arch:** either have them build it natively with the steps above
  (they need nightly Rust), or cross-compile for their target from
  your machine. The code is pure Rust and platform-portable (macOS, Linux, Windows);
  the simplest cross path is [`cargo-zigbuild`](https://github.com/rust-cross/cargo-zigbuild):

  ```sh
  cargo install cargo-zigbuild
  rustup target add x86_64-unknown-linux-gnu     # or x86_64-pc-windows-gnu, aarch64-..., etc.

  # The Ristretto crypto pulls in `clear_on_drop`, which builds a tiny C shim.
  # zigbuild's bundled `ar` fails to create that archive, so point the archiver
  # for the target at a real llvm-ar (any host llvm-ar works; it just archives).
  AR_x86_64_unknown_linux_gnu=$(command -v llvm-ar) \
    cargo zigbuild --release --target x86_64-unknown-linux-gnu
  ```

  For Windows, swap the target and the matching var name (dots/dashes become
  underscores): `AR_x86_64_pc_windows_gnu=$(command -v llvm-ar) cargo
  zigbuild --release --target x86_64-pc-windows-gnu`. The macOS arm64 build is
  native and needs no override: `cargo build --release`.

## Reference numbers (Apple M-series, 8 cores)

100 iterations each. Yours will differ by hardware.

```
                      time (avg)     cpu (avg)     artifact
  LEGACY sign          ~1.9 ms        ~100%        1120 bytes
  LEGACY verify        ~1.8 ms        ~100%
  NEW    prove         ~53 ms         ~100%        ~238.5 KB  (1-in/1-out, foldable)
  NEW    verify        ~8.2 ms        ~100%
  memory: legacy ~18 MB,  new ~19 MB

  FARADAY TX / BLOCK (offline, real schema):
  tx send (relay)   ~241 KB   (2.3 KB metadata + ~238.5 KB proof)
  tx on-chain       ~2.3 KB   metadata only (proof stripped + folded away)
  block             fold two spends -> one ~410 KB proof in ~15 s;  ~736 tx per 2 MB block

  MINING HASH (t=1 p=1), time per hash / hashrate:
  Argon2id 2 GiB (current)    ~1.12 s   0.89 H/s
  Argon2d 512 MiB (candidate) ~0.28 s   3.54 H/s

  Measured 2026-10-07 on Plonky3 0.8.0 + Plonky3-recursion 485455c. The FRI config scores
  ~60-67 provable bits (soundcalc); it is not yet funds-grade.
```

Reading it: the post-quantum proof is slower to produce (~100 ms vs ~3 ms) and to verify
(~18 ms vs ~3 ms) than the legacy ring signature, and ~340x larger per tx, but it is
hash-based (no elliptic curves) so it survives a quantum adversary. The size lands on
**relay**, paid once by the sender. **On-chain** the story flips: the block folds every
tx's proof into one ~constant-size proof (O(1) in tx count), so a Faraday tx costs only its
~2.3 KB metadata -- comparable to or smaller than the ~6 KB a curve tx costs today -- while
buying full-chain anonymity and post-quantum security. Both sides are cheap in compute
(a proof is a fraction of a second, verification is milliseconds); memory stays modest
because the spend circuit is small.
