#[allow(dead_code)]
mod address;
mod art;
mod bench;
mod brand;
mod legacy;
mod metrics;
mod gpu;
mod miner;
mod mining;
#[allow(dead_code)]
mod pow;
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
use vole::wire;
use metrics::{process_rss_bytes, Stats};

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

    let prep = vole::prepare();
    match vole::self_check(&prep) {
        Ok(()) => ui::check(color, true, "spend proof gate -- honest 2x2 proof verifies; changed fee and flipped byte rejected"),
        Err(e) => {
            ui::check(color, false, &format!("spend proof gate FAILED: {e}"));
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
    let k = vole::SHAPES.len();
    let mut np = vec![Vec::new(); k];
    let mut npc = vec![Vec::new(); k];
    let mut nv = vec![Vec::new(); k];
    let mut nvc = vec![Vec::new(); k];
    let mut leg_mem = Vec::new();
    let mut new_mem = Vec::new();
    let mut proof_bytes = vec![0usize; k];
    let mut hash_rows: Vec<ui::HashRow> = Vec::new();
    let mut gpu_names: Vec<String> = Vec::new();
    let mut gpu_now: Vec<(String, Result<miner::Mined, String>)> = Vec::new();
    let stop = AtomicBool::new(false);

    {
        let mut cb = |ev: Ev| match ev {
            Ev::Totals(_, _) => {}
            Ev::ProofSize(i, n) => proof_bytes[i] = n,
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
                    OpKind::NewProve(i) => {
                        np[i].push(t);
                        npc[i].push(c);
                        new_mem.push(rss);
                    }
                    OpKind::NewVerify(i) => {
                        nv[i].push(t);
                        nvc[i].push(c);
                        new_mem.push(rss);
                        let n = vole::SHAPES[i];
                        eprint!("\r  [new {n}x{n}] proof {}/{}   last prove {:>6.1} ms      ", np[i].len(), N_NEW, np[i].last().copied().unwrap_or(0.0));
                        let _ = std::io::stderr().flush();
                    }
                }
            }
            Ev::HashPlan => eprintln!(
                "\n  mining hash: BLAKE2b-512, personalization blocknet/pow/v1 ({} s)",
                mining::MINE_SECONDS
            ),
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
        ops.push(ui::Op { side: ui::Side::Legacy, shape: 0, verb: "sign", time: Stats::of(&ls), cpu: Stats::of(&lsc) });
    }
    if !lv.is_empty() {
        ops.push(ui::Op { side: ui::Side::Legacy, shape: 0, verb: "verify", time: Stats::of(&lv), cpu: Stats::of(&lvc) });
    }
    for (i, &n) in vole::SHAPES.iter().enumerate() {
        if !np[i].is_empty() {
            ops.push(ui::Op { side: ui::Side::New, shape: n, verb: "prove", time: Stats::of(&np[i]), cpu: Stats::of(&npc[i]) });
        }
        if !nv[i].is_empty() {
            ops.push(ui::Op { side: ui::Side::New, shape: n, verb: "verify", time: Stats::of(&nv[i]), cpu: Stats::of(&nvc[i]) });
        }
    }

    let proofs: Vec<(usize, usize)> =
        vole::SHAPES.iter().zip(&proof_bytes).filter(|(_, b)| **b > 0).map(|(n, b)| (*n, *b)).collect();
    let wire: Vec<wire::WireRow> = proofs.iter().map(|(n, b)| wire::measure(*n, *b)).collect();

    let report = ui::Report {
        sig_bytes,
        proofs,
        ops,
        leg_mem_mb: (!leg_mem.is_empty()).then(|| Stats::of(&leg_mem)),
        new_mem_mb: (!new_mem.is_empty()).then(|| Stats::of(&new_mem)),
        hashes: hash_rows,
        wire,
        set_ms: vole::set_digest_ms(&prep),
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
