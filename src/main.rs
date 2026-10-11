mod bench;
mod brand;
mod faraday_tx;
mod legacy;
mod metrics;
mod gpu;
mod miner;
mod mining;
mod ui;

#[cfg(unix)]
mod algo;
#[cfg(unix)]
mod dash;
#[cfg(unix)]
mod fx;
#[cfg(unix)]
mod gfx;
#[cfg(unix)]
mod machine;
#[cfg(unix)]
mod scenes;

use std::io::{IsTerminal, Write};
use std::sync::atomic::AtomicBool;

use bench::{Ev, OpKind};
use metrics::{process_rss_bytes, Stats};
use pqc_poc::faraday5 as ff;

const N_LEGACY: usize = 100;
const N_NEW: usize = 100;
const SEED: u64 = 1000;

fn main() {
    let cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(0);
    let host = format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS);
    let color = std::env::var_os("NO_COLOR").is_none() && std::io::stdout().is_terminal();

    #[cfg(unix)]
    {
        if color {
            dash::run(N_LEGACY, N_NEW, SEED);
            return;
        }
    }

    run_static(host, cores, color);
}

fn run_static(host: String, cores: usize, color: bool) {
    ui::banner(color, &host, cores, N_LEGACY, N_NEW);
    println!();

    let prep = ff::prepare();
    match ff::self_check() {
        Ok(()) => ui::check(color, true, "Faraday circuit conformance -- D1 W32 hash == native Poseidon2"),
        Err(e) => {
            ui::check(color, false, &format!("Faraday circuit conformance FAILED: {e}"));
            std::process::exit(1);
        }
    }
    let wit = legacy::make_witness(50_000, 7);
    let probe = legacy::sign(&wit);
    if legacy::verify(&wit, &probe) {
        ui::check(
            color,
            true,
            &format!("RingCT sign -> verify round-trip (ring {}, sig {} bytes)", legacy::RING_SIZE, probe.len()),
        );
    } else {
        ui::check(color, false, "RingCT round-trip FAILED: verify rejected a fresh signature");
        std::process::exit(1);
    }
    let sig_bytes = probe.len();

    let mut ls = Vec::new();
    let mut lsc = Vec::new();
    let mut lv = Vec::new();
    let mut lvc = Vec::new();
    let mut np = Vec::new();
    let mut npc = Vec::new();
    let mut nv = Vec::new();
    let mut nvc = Vec::new();
    let mut leg_mem = Vec::new();
    let mut new_mem = Vec::new();
    let mut proof_bytes = 0usize;
    let mut hash_rows: Vec<ui::HashRow> = Vec::new();
    let mut gpu_names: Vec<String> = Vec::new();
    let mut gpu_now: Vec<(String, Result<miner::Mined, String>)> = Vec::new();
    let mut faithful: Option<bool> = None;
    let stop = AtomicBool::new(false);

    {
        let mut cb = |ev: Ev| match ev {
            Ev::Totals(_, _) => {}
            Ev::ProofSize(n) => proof_bytes = n,
            Ev::Op(k, t, c) => {
                let rss = process_rss_bytes() as f64 / (1024.0 * 1024.0);
                match k {
                    OpKind::LegSign => {
                        ls.push(t);
                        lsc.push(c);
                        leg_mem.push(rss);
                        progress("legacy sign  ", ls.len(), N_LEGACY);
                    }
                    OpKind::LegVerify => {
                        lv.push(t);
                        lvc.push(c);
                        leg_mem.push(rss);
                        progress("legacy verify", lv.len(), N_LEGACY);
                    }
                    OpKind::NewProve => {
                        np.push(t);
                        npc.push(c);
                        new_mem.push(rss);
                    }
                    OpKind::NewVerify => {
                        nv.push(t);
                        nvc.push(c);
                        new_mem.push(rss);
                        eprint!("\r  [new] proof {}/{}   last prove {:>7.0} ms      ", np.len(), N_NEW, np.last().copied().unwrap_or(0.0));
                        let _ = std::io::stderr().flush();
                    }
                }
            }
            Ev::HashPlan => eprintln!(
                "\n  mining hash: Argon2id 2 GiB, Argon2d 512 MiB, BLAKE2b-512 and SHA3-512 ({} s each)",
                mining::MINE_SECONDS
            ),
            Ev::HashVerify(None) => {
                eprint!("\r  verifying reproduction vs blocknet_pow_hash (2 GiB)...   ");
                let _ = std::io::stderr().flush();
            }
            Ev::HashVerify(Some(ok)) => {
                faithful = Some(ok);
                eprintln!("\r  hash faithfulness (2 GiB == consensus): {}          ", if ok { "OK" } else { "MISMATCH" });
            }
            Ev::HashSkip(pow, _reason) => {
                hash_rows.push(ui::HashRow { pow, mined: miner::Mined::default(), ran: false, gpu: Vec::new() });
            }
            Ev::HashStart(_) => {}
            Ev::Mine(pow, m) => {
                eprint!(
                    "\r  [mine] {}   {:.0}/{:.0} s   {} on {} threads      ",
                    mining::label(pow),
                    m.secs,
                    mining::MINE_SECONDS,
                    ui::fmt_rate(m.rate()),
                    m.threads
                );
                let _ = std::io::stderr().flush();
            }
            Ev::HashDone(pow, m) => {
                let gpu = std::mem::take(&mut gpu_now);
                hash_rows.push(ui::HashRow { pow, mined: m, ran: true, gpu });
            }
            Ev::Gpus(names) => gpu_names = names,
            Ev::GpuMine(..) => {}
            Ev::GpuDone(_, i, r) => gpu_now.push((gpu_names.get(i).cloned().unwrap_or_default(), r)),
            Ev::Done => {}
        };
        bench::run(&prep, &wit, N_LEGACY, N_NEW, SEED, &stop, &mut cb);
    }
    eprintln!();

    let mut ops = Vec::new();
    if !ls.is_empty() {
        ops.push(ui::Op { side: ui::Side::Legacy, verb: "sign", time: Stats::of(&ls), cpu: Stats::of(&lsc) });
    }
    if !lv.is_empty() {
        ops.push(ui::Op { side: ui::Side::Legacy, verb: "verify", time: Stats::of(&lv), cpu: Stats::of(&lvc) });
    }
    if !np.is_empty() {
        ops.push(ui::Op { side: ui::Side::New, verb: "prove", time: Stats::of(&np), cpu: Stats::of(&npc) });
    }
    if !nv.is_empty() {
        ops.push(ui::Op { side: ui::Side::New, verb: "verify", time: Stats::of(&nv), cpu: Stats::of(&nvc) });
    }

    let faraday = if proof_bytes > 0 && !mining::fold_fits() {
        eprintln!("  block fold: skipped (needs {} GiB of RAM; the fold peaks near 9.3 GB)", mining::FOLD_MIN_RAM_GIB);
        None
    } else if proof_bytes > 0 {
        eprintln!("  block fold: proving + folding two spends into one block proof (several minutes)...");
        let fold = ff::fold_two();
        let (tx_meta, tx_relay, block_n, block_bytes) =
            faraday_tx::measure(proof_bytes, fold.folded_bytes);
        Some(ui::FaradayReport {
            tx_meta,
            per_tx_proof: proof_bytes,
            tx_relay,
            folded_bytes: fold.folded_bytes,
            fold_secs: fold.fold_wall.as_secs_f64(),
            block_n,
            block_bytes,
        })
    } else {
        None
    };

    let report = ui::Report {
        sig_bytes,
        proof_bytes,
        ops,
        leg_mem_mb: (!leg_mem.is_empty()).then(|| Stats::of(&leg_mem)),
        new_mem_mb: (!new_mem.is_empty()).then(|| Stats::of(&new_mem)),
        hashes: hash_rows,
        faithful,
        faraday,
    };
    ui::results(color, &report);
}

fn progress(label: &str, i: usize, n: usize) {
    if n == 0 {
        return;
    }
    if i == n || i % 10 == 0 {
        eprint!("\r  [{label}] {i}/{n}      ");
        let _ = std::io::stderr().flush();
    }
}
