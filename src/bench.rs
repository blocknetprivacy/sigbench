use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use crate::legacy;
use crate::metrics::{cpu_pct, process_cpu_time};
use crate::mining;
use crate::gpu;
use crate::miner;
use pqc_poc::faraday5::{self as ff, Prepared};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OpKind {
    LegSign,
    LegVerify,
    NewProve,
    NewVerify,
}

#[allow(dead_code)]
pub enum Ev {
    Totals(usize, usize),
    Op(OpKind, f64, f64),
    ProofSize(usize),
    HashPlan,
    HashVerify(Option<bool>),
    HashSkip(mining::Pow, &'static str),
    HashStart(mining::Pow),
    Gpus(Vec<String>),
    Mine(mining::Pow, miner::Mined),
    GpuMine(mining::Pow, usize, miner::Mined),
    GpuDone(mining::Pow, usize, Result<miner::Mined, String>),
    HashDone(mining::Pow, miner::Mined),
    Done,
}

fn timed<T>(f: impl FnOnce() -> T) -> (T, Duration, Duration) {
    let cpu0 = process_cpu_time();
    let wall0 = Instant::now();
    let out = f();
    let wall = wall0.elapsed();
    let cpu = process_cpu_time().saturating_sub(cpu0);
    (out, wall, cpu)
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

#[allow(clippy::too_many_arguments)]
pub fn run(
    prep: &Prepared,
    wit: &legacy::Witness,
    n_legacy: usize,
    n_new: usize,
    seed: u64,
    stop: &AtomicBool,
    cb: &mut dyn FnMut(Ev),
) {
    let _ = legacy::verify(wit, &legacy::sign(wit));
    let _ = ff::run_one(prep, 1, &process_cpu_time);

    cb(Ev::Totals(n_legacy, n_new));

    let mut sigs = Vec::with_capacity(n_legacy);
    for _ in 0..n_legacy {
        if stop.load(Ordering::Relaxed) {
            cb(Ev::Done);
            return;
        }
        let (sig, wall, cpu) = timed(|| legacy::sign(wit));
        cb(Ev::Op(OpKind::LegSign, ms(wall), cpu_pct(cpu, wall)));
        sigs.push(sig);
    }
    for sig in &sigs {
        if stop.load(Ordering::Relaxed) {
            cb(Ev::Done);
            return;
        }
        let (ok, wall, cpu) = timed(|| legacy::verify(wit, sig));
        assert!(ok, "a signature we just produced failed to verify");
        cb(Ev::Op(OpKind::LegVerify, ms(wall), cpu_pct(cpu, wall)));
    }

    for i in 0..n_new {
        if stop.load(Ordering::Relaxed) {
            cb(Ev::Done);
            return;
        }
        let m = ff::run_one(prep, seed + i as u64, &process_cpu_time);
        cb(Ev::ProofSize(m.proof_bytes));
        cb(Ev::Op(OpKind::NewProve, ms(m.prove_wall), cpu_pct(m.prove_cpu, m.prove_wall)));
        cb(Ev::Op(OpKind::NewVerify, ms(m.verify_wall), cpu_pct(m.verify_cpu, m.verify_wall)));
    }

    if !stop.load(Ordering::Relaxed) {
        cb(Ev::HashPlan);

        if miner::cpu_threads(mining::Pow::Argon2(mining::CURRENT_MIB)) > 0 {
            cb(Ev::HashVerify(None));
            let ok = mining::faithful_2gib();
            cb(Ev::HashVerify(Some(ok)));
        }

        let gpus = gpu::devices();
        cb(Ev::Gpus(gpus.iter().map(|d| d.name.clone()).collect()));
        for &pow in &mining::LEVELS {
            if stop.load(Ordering::Relaxed) {
                break;
            }
            let threads = miner::cpu_threads(pow);
            if threads == 0 && gpus.is_empty() {
                cb(Ev::HashSkip(pow, "needs more RAM than is free here"));
                continue;
            }
            cb(Ev::HashStart(pow));
            let after_cpu = gpu::SHARES_RAM && matches!(pow, mining::Pow::Argon2(_));
            let (tx, rx) = std::sync::mpsc::channel::<Ev>();
            let spawn_gpus = |tx: std::sync::mpsc::Sender<Ev>| -> Vec<std::thread::JoinHandle<()>> {
                gpus.iter()
                    .cloned()
                    .enumerate()
                    .map(|(i, dev)| {
                        let tx = tx.clone();
                        std::thread::spawn(move || {
                            let never = std::sync::atomic::AtomicBool::new(false);
                            let r = gpu::mine(&dev, pow, mining::MINE_SECONDS, &never, &mut |m| {
                                let _ = tx.send(Ev::GpuMine(pow, i, m));
                            });
                            let _ = tx.send(Ev::GpuDone(pow, i, r));
                        })
                    })
                    .collect()
            };
            let mut handles = if after_cpu { Vec::new() } else { spawn_gpus(tx.clone()) };
            let m = if threads > 0 {
                miner::mine_cpu(pow, threads, mining::MINE_SECONDS, stop, &mut |m| {
                    cb(Ev::Mine(pow, m));
                    while let Ok(ev) = rx.try_recv() {
                        cb(ev);
                    }
                })
            } else {
                miner::Mined::default()
            };
            if after_cpu && !stop.load(Ordering::Relaxed) {
                handles = spawn_gpus(tx.clone());
            }
            drop(tx);
            for ev in rx.iter() {
                cb(ev);
            }
            for h in handles {
                let _ = h.join();
            }
            cb(Ev::HashDone(pow, m));
        }
    }

    cb(Ev::Done);
}
