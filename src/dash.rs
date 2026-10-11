use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

use crate::bench::{self, Ev, OpKind};
use crate::gfx::*;
use crate::legacy;
use crate::machine::*;
use crate::metrics::process_rss_bytes;
use crate::mining::{self, Pow};
use crate::scenes::*;
use crate::miner::Mined;
use crate::ui::{fmt_hash_time, fmt_rate};
use pqc_poc::faraday5 as ff;

const FPS: u64 = 20;

static GO: AtomicBool = AtomicBool::new(false);

#[derive(Clone, Copy, PartialEq)]
enum Stage {
    Legacy,
    Spend,
    Hash(Pow),
    Fold,
    Done,
}

#[derive(Default)]
struct HashLive {
    mined: Mined,
    gpu: Vec<Option<Result<Mined, String>>>,
    started: Option<Instant>,
    done: bool,
    skipped: bool,
}

enum FoldState {
    Waiting,
    Running(Instant),
    Done { bytes: usize, secs: f64, block_n: usize },
    Skipped,
}

struct Live {
    ready: bool,
    error: Option<String>,
    stage: Option<Stage>,
    n_legacy: usize,
    n_new: usize,
    leg_sign: Vec<f64>,
    leg_verify: Vec<f64>,
    new_prove: Vec<f64>,
    new_prove_cpu: Vec<f64>,
    new_verify: Vec<f64>,
    sig_bytes: usize,
    proof_bytes: usize,
    hashes: Vec<(Pow, HashLive)>,
    faithful: Option<bool>,
    checking_pow: bool,
    gpus: Vec<String>,
    fold: FoldState,
    peak_rss: u64,
}

impl Live {
    fn hash(&mut self, pow: Pow) -> &mut HashLive {
        let i = self.hashes.iter().position(|(p, _)| *p == pow).unwrap();
        &mut self.hashes[i].1
    }
    fn hash_ref(&self, pow: Pow) -> &HashLive {
        &self.hashes.iter().find(|(p, _)| *p == pow).unwrap().1
    }
}

fn avg(v: &[f64]) -> f64 {
    if v.is_empty() { 0.0 } else { v.iter().sum::<f64>() / v.len() as f64 }
}

fn low_high(v: &[f64]) -> (f64, f64) {
    v.iter().fold((f64::MAX, 0.0f64), |(l, h), x| (l.min(*x), h.max(*x)))
}

fn fmt_ms(ms: f64) -> String {
    if ms >= 1000.0 { format!("{:.2} s", ms / 1000.0) } else if ms >= 10.0 { format!("{ms:.0} ms") } else { format!("{ms:.2} ms") }
}

fn fmt_bytes(b: usize) -> String {
    let f = b as f64;
    if b >= 1 << 30 {
        format!("{:.1} GB", f / (1u64 << 30) as f64)
    } else if b >= 1 << 20 {
        format!("{:.1} MB", f / (1 << 20) as f64)
    } else if b >= 10 * 1024 {
        format!("{:.0} KB", f / 1024.0)
    } else if b >= 1000 {
        format!("{},{:03} B", b / 1000, b % 1000)
    } else {
        format!("{b} B")
    }
}

fn fmt_secs(s: f64) -> String {
    if s >= 60.0 { format!("{} m {:02} s", (s / 60.0) as u64, (s % 60.0) as u64) } else { format!("{s:.1} s") }
}

fn spread(v: &[f64]) -> String {
    let (l, h) = low_high(v);
    format!("{}  (low {}, high {})", fmt_ms(avg(v)), fmt_ms(l), fmt_ms(h))
}

fn scene_of(stage: Stage) -> Scene {
    match stage {
        Stage::Legacy => Scene::Ring,
        Stage::Spend => Scene::Lattice,
        Stage::Hash(Pow::Argon2(mining::CURRENT_MIB)) => Scene::Argon2id,
        Stage::Hash(Pow::Argon2(_)) => Scene::Argon2d,
        Stage::Hash(Pow::Blake2b512) => Scene::Blake2b,
        Stage::Hash(Pow::Sha3_512) => Scene::Sha3,
        Stage::Fold => Scene::Fold,
        Stage::Done => Scene::Report,
    }
}

fn pow_name(pow: Pow) -> &'static str {
    match pow {
        Pow::Argon2(mining::CURRENT_MIB) => "Argon2id 2 GiB",
        Pow::Argon2(_) => "Argon2d 512 MiB",
        Pow::Blake2b512 => "BLAKE2b-512",
        Pow::Sha3_512 => "SHA3-512",
    }
}

fn report_pow_name(pow: Pow) -> &'static str {
    match pow {
        Pow::Argon2(mining::CURRENT_MIB) => "Argon2id 2 GiB (current)",
        Pow::Argon2(_) => "Argon2d 512 MiB (A)",
        Pow::Blake2b512 => "BLAKE2b-512 (B)",
        Pow::Sha3_512 => "SHA3-512 (C)",
    }
}

pub fn run(n_legacy: usize, n_new: usize, seed: u64) {
    let m = machine();
    let live = Arc::new(Mutex::new(Live {
        ready: false,
        error: None,
        stage: None,
        n_legacy,
        n_new,
        leg_sign: vec![],
        leg_verify: vec![],
        new_prove: vec![],
        new_prove_cpu: vec![],
        new_verify: vec![],
        sig_bytes: 0,
        proof_bytes: 0,
        hashes: mining::LEVELS.iter().map(|p| (*p, HashLive::default())).collect(),
        faithful: None,
        gpus: Vec::new(),
        checking_pow: false,
        fold: FoldState::Waiting,
        peak_rss: 0,
    }));
    let worker = {
        let live = live.clone();
        thread::spawn(move || work(live, n_legacy, n_new, seed))
    };

    let mut cx = SceneCtx::new(start_info(&m));
    cx.fold_period = 12.0;
    let mut screen = Screen::open();
    let start = Instant::now();
    let mut stage = Stager::new(Scene::Boot);
    let mut run: Option<(Instant, bool)> = None;
    let mut report: Option<Report> = None;
    let mut info_open = false;
    while !QUIT.load(Ordering::Relaxed) {
        let (w, h) = screen.begin(&mut cx);
        let global = start.elapsed().as_secs_f32();
        let mut l = live.lock().unwrap();
        l.peak_rss = l.peak_rss.max(process_rss_bytes());
        if l.error.is_some() {
            break;
        }
        let Some((run_start, visuals)) = run else {
            let ready = l.ready;
            drop(l);
            let g = start_screen(w, h, global, &mut cx, ready, "preparing the spend circuit");
            screen.show(&g, FPS);
            if let Some(v) = start_key() {
                if ready {
                    run = Some((Instant::now(), v));
                    GO.store(true, Ordering::SeqCst);
                }
            }
            continue;
        };
        let cur = l.stage.unwrap_or(Stage::Legacy);
        stage.set(scene_of(cur));
        for (pow, secs) in [(Pow::Argon2(mining::CURRENT_MIB), &mut cx.argon_id_secs), (Pow::Argon2(mining::FARADAY_MIB), &mut cx.argon_d_secs)] {
            let m = l.hash_ref(pow).mined;
            if m.hashes > 0 {
                *secs = (m.ms_per_hash() / 1000.0) as f32;
            }
        }
        let done = cur == Stage::Done;
        let suites = suites(&l, cur);
        let (panel, headline, lines, progress) = readout(&l, cur, &m);
        let run_frac = suites.iter().filter(|s| matches!(s.state, SuiteState::Done | SuiteState::Skipped)).count() as f32 / suites.len() as f32
            + progress.unwrap_or(0.0) / suites.len() as f32;
        let hud = Hud {
            suites: &suites,
            panel,
            headline,
            lines,
            progress,
            run_frac: if done { 1.0 } else { run_frac },
            run_secs: run_start.elapsed().as_secs_f32(),
            right: format!("{} threads  ·  {}{}", m.threads, m.ram(), if visuals { "" } else { "  ·  visuals off" }),
            intro: run_start.elapsed().as_secs_f32() / 0.8,
            report: done,
        };
        if done && report.is_none() {
            let secs = run_start.elapsed().as_secs_f64();
            report = Some(save_report(report_sections(&l, &m, visuals, secs), "", 3));
        }
        drop(l);
        let mut g = stage.draw(w, h, &mut cx, visuals, global);
        interface(&mut g, &hud, screen.frame);
        if let Some(rep) = &report {
            report_card(&mut g, rep, (stage.local() - TWEEN * 0.5) / 0.6);
        }
        info_keys(&mut info_open);
        if info_open {
            info_card(&mut g, stage.scene);
        }
        screen.show(&g, FPS);
    }
    screen.close();
    QUIT.store(true, Ordering::SeqCst);
    GO.store(true, Ordering::SeqCst);
    let err = live.lock().unwrap().error.clone();
    if let Some(e) = err {
        eprintln!("{e}");
        std::process::exit(1);
    }
    match report {
        Some(r) => {
            println!("{}", r.txt);
            println!("{}", r.saved);
        }
        None => println!("Bench 2 stopped before the end; no report was saved."),
    }
    drop(worker);
}

fn work(live: Arc<Mutex<Live>>, n_legacy: usize, n_new: usize, seed: u64) {
    let prep = ff::prepare();
    if let Err(e) = ff::self_check() {
        live.lock().unwrap().error = Some(format!("Faraday circuit conformance FAILED: {e}"));
        return;
    }
    let wit = legacy::make_witness(50_000, 7);
    let probe = legacy::sign(&wit);
    if !legacy::verify(&wit, &probe) {
        live.lock().unwrap().error = Some("RingCT round-trip FAILED: verify rejected a fresh signature".into());
        return;
    }
    {
        let mut l = live.lock().unwrap();
        l.sig_bytes = probe.len();
        l.ready = true;
    }
    while !GO.load(Ordering::SeqCst) {
        thread::sleep(std::time::Duration::from_millis(20));
    }
    if QUIT.load(Ordering::Relaxed) {
        return;
    }
    live.lock().unwrap().stage = Some(Stage::Legacy);
    let mut cb = |ev: Ev| {
        let mut l = live.lock().unwrap();
        match ev {
            Ev::Totals(a, b) => {
                l.n_legacy = a;
                l.n_new = b;
            }
            Ev::ProofSize(n) => l.proof_bytes = n,
            Ev::Op(k, t, c) => {
                match k {
                    OpKind::LegSign => l.leg_sign.push(t),
                    OpKind::LegVerify => l.leg_verify.push(t),
                    OpKind::NewProve => {
                        l.new_prove.push(t);
                        l.new_prove_cpu.push(c);
                    }
                    OpKind::NewVerify => l.new_verify.push(t),
                }
                l.stage = Some(if matches!(k, OpKind::LegSign | OpKind::LegVerify) { Stage::Legacy } else { Stage::Spend });
            }
            Ev::HashPlan => {}
            Ev::Gpus(names) => {
                for (_, h) in l.hashes.iter_mut() {
                    h.gpu = vec![None; names.len()];
                }
                l.gpus = names;
            }
            Ev::GpuMine(pow, i, m) => {
                if let Some(g) = l.hash(pow).gpu.get_mut(i) {
                    *g = Some(Ok(m));
                }
            }
            Ev::GpuDone(pow, i, r) => {
                if let Some(g) = l.hash(pow).gpu.get_mut(i) {
                    *g = Some(r);
                }
            }
            Ev::HashVerify(None) => {
                l.checking_pow = true;
                l.stage = Some(Stage::Hash(Pow::Argon2(mining::CURRENT_MIB)));
            }
            Ev::HashVerify(Some(ok)) => {
                l.checking_pow = false;
                l.faithful = Some(ok);
            }
            Ev::HashSkip(pow, _) => {
                let h = l.hash(pow);
                h.skipped = true;
                h.done = true;
            }
            Ev::HashStart(pow) => {
                l.hash(pow).started = Some(Instant::now());
                l.stage = Some(Stage::Hash(pow));
            }
            Ev::Mine(pow, m) => l.hash(pow).mined = m,
            Ev::HashDone(pow, m) => {
                let h = l.hash(pow);
                h.mined = m;
                h.done = true;
            }
            Ev::Done => {}
        }
    };
    bench::run(&prep, &wit, n_legacy, n_new, seed, &QUIT, &mut cb);
    if QUIT.load(Ordering::Relaxed) {
        return;
    }
    let proof_bytes = live.lock().unwrap().proof_bytes;
    if proof_bytes > 0 && mining::fold_fits() {
        {
            let mut l = live.lock().unwrap();
            l.fold = FoldState::Running(Instant::now());
            l.stage = Some(Stage::Fold);
        }
        let fold = ff::fold_two();
        let (_meta, _relay, block_n, _bb) = crate::faraday_tx::measure(proof_bytes, fold.folded_bytes);
        let mut l = live.lock().unwrap();
        l.fold = FoldState::Done { bytes: fold.folded_bytes, secs: fold.fold_wall.as_secs_f64(), block_n };
    } else {
        live.lock().unwrap().fold = FoldState::Skipped;
    }
    live.lock().unwrap().stage = Some(Stage::Done);
}

fn mined(h: &HashLive) -> f32 {
    if h.done {
        return 1.0;
    }
    h.started.map(|t| (t.elapsed().as_secs_f64() / mining::MINE_SECONDS) as f32).unwrap_or(0.0).min(1.0)
}

fn gpu_line(name: &str, g: Option<&Result<Mined, String>>) -> String {
    match g {
        None => format!("GPU  starting  ·  {name}"),
        Some(Ok(m)) if m.hashes == 0 => format!("GPU  checking against the CPU  ·  {name}"),
        Some(Ok(m)) => format!("GPU  {}  ·  {name}  ·  {} in flight", fmt_rate(m.rate()), m.threads),
        Some(Err(e)) => format!("GPU  not used ({e})  ·  {name}"),
    }
}

fn total_rate(h: &HashLive) -> f64 {
    h.mined.rate() + h.gpu.iter().filter_map(|g| g.as_ref()?.as_ref().ok()).map(|m| m.rate()).sum::<f64>()
}

fn order(s: Stage) -> usize {
    match s {
        Stage::Legacy => 0,
        Stage::Spend => 1,
        Stage::Hash(p) => 2 + mining::LEVELS.iter().position(|x| *x == p).unwrap_or(0),
        Stage::Fold => 6,
        Stage::Done => 7,
    }
}

fn suites(l: &Live, cur: Stage) -> Vec<Suite> {
    let state = |s: Stage, skipped: bool| {
        if skipped {
            SuiteState::Skipped
        } else if order(s) < order(cur) {
            SuiteState::Done
        } else if s == cur {
            SuiteState::Active
        } else {
            SuiteState::Pending
        }
    };
    let pct = |p: f32| format!("{:>3.0}%", 100.0 * p.clamp(0.0, 1.0));
    let mut v = vec![];
    let ls = state(Stage::Legacy, false);
    v.push(Suite {
        name: "Legacy RingCT",
        state: ls,
        result: match ls {
            SuiteState::Done => fmt_ms(avg(&l.leg_sign)),
            SuiteState::Active => pct((l.leg_sign.len() + l.leg_verify.len()) as f32 / (2 * l.n_legacy.max(1)) as f32),
            _ => String::new(),
        },
    });
    let ss = state(Stage::Spend, false);
    v.push(Suite {
        name: "Faraday spend",
        state: ss,
        result: match ss {
            SuiteState::Done => fmt_ms(avg(&l.new_prove)),
            SuiteState::Active => pct(l.new_verify.len() as f32 / l.n_new.max(1) as f32),
            _ => String::new(),
        },
    });
    for (pow, h) in &l.hashes {
        let st = state(Stage::Hash(*pow), h.skipped);
        v.push(Suite {
            name: pow_name(*pow),
            state: st,
            result: match st {
                SuiteState::Done if h.mined.hashes > 0 || h.gpu.iter().any(|g| matches!(g, Some(Ok(_)))) => fmt_rate(total_rate(h)),
                SuiteState::Active => pct(mined(h)),
                SuiteState::Skipped => "skipped".into(),
                _ => String::new(),
            },
        });
    }
    let fs = state(Stage::Fold, matches!(l.fold, FoldState::Skipped));
    v.push(Suite {
        name: "Block fold",
        state: fs,
        result: match &l.fold {
            FoldState::Done { bytes, .. } => fmt_bytes(*bytes),
            FoldState::Skipped => "skipped".into(),
            FoldState::Running(t) => fmt_secs(t.elapsed().as_secs_f64()),
            FoldState::Waiting => String::new(),
        },
    });
    v
}

fn readout(l: &Live, cur: Stage, m: &Machine) -> (&'static str, String, Vec<String>, Option<f32>) {
    match cur {
        Stage::Legacy => {
            let (s, v, n) = (l.leg_sign.len(), l.leg_verify.len(), l.n_legacy);
            let avg_or = |x: &[f64]| if x.is_empty() { "…".to_string() } else { fmt_ms(avg(x)) };
            (
                "Legacy RingCT",
                format!("{s}/{n} signed  ·  {v}/{n} verified"),
                vec![
                    format!("sign {}  ·  verify {}  ·  {}", avg_or(&l.leg_sign), avg_or(&l.leg_verify), fmt_bytes(l.sig_bytes)),
                    "anonymity set: 16 outputs (a ring of 16)".into(),
                ],
                Some((s + v) as f32 / (2 * n.max(1)) as f32),
            )
        }
        Stage::Spend => {
            let (p, v, n) = (l.new_prove.len(), l.new_verify.len(), l.n_new);
            let avg_or = |x: &[f64]| if x.is_empty() { "…".to_string() } else { fmt_ms(avg(x)) };
            (
                "Faraday spend",
                format!("{p}/{n} proved  ·  {v}/{n} verified"),
                vec![
                    format!("prove {}  ·  verify {}  ·  {}", avg_or(&l.new_prove), avg_or(&l.new_verify), fmt_bytes(l.proof_bytes)),
                    "anonymity set: every Faraday output (full chain)".into(),
                ],
                Some(v as f32 / n.max(1) as f32),
            )
        }
        Stage::Hash(pow) => {
            let h = l.hash_ref(pow);
            let mm = h.mined;
            let rate = if mm.hashes == 0 {
                format!("CPU  starting {} threads…", mm.threads.max(crate::miner::cpu_threads(pow)))
            } else {
                format!("CPU  {} on {} threads  ·  {} per hash per thread", fmt_rate(mm.rate()), mm.threads, fmt_hash_time(mm.ms_per_hash()))
            };
            let mut gpu_lines: Vec<String> = l.gpus.iter().zip(&h.gpu).map(|(name, g)| gpu_line(name, g.as_ref())).collect();
            if l.gpus.is_empty() {
                gpu_lines.push("GPU  none found".into());
            }
            let (headline, extra) = match pow {
                Pow::Argon2(mib) => {
                    let what = if mib == mining::CURRENT_MIB { "current PoW" } else { "PoW candidate A" };
                    let check = match l.faithful {
                        _ if mib != mining::CURRENT_MIB => "512 MiB of memory per hash".to_string(),
                        Some(true) => "2 GiB per hash  ·  matches the node's PoW hash ✓".into(),
                        Some(false) => "2 GiB per hash  ·  does NOT match the node's PoW hash".into(),
                        None => "2 GiB per hash".into(),
                    };
                    let head = if l.checking_pow {
                        "checking the hash against the node's code…".into()
                    } else {
                        format!("{what}  ·  mining {:.0} / {:.0} s  ·  {} hashes", mined(h) * mining::MINE_SECONDS as f32, mining::MINE_SECONDS, h.mined.hashes)
                    };
                    (head, check)
                }
                _ => {
                    let what = if pow == Pow::Blake2b512 { "PoW candidate B" } else { "PoW candidate C" };
                    (format!("{what}  ·  mining {:.0} / {:.0} s", mined(h) * mining::MINE_SECONDS as f32, mining::MINE_SECONDS), "no memory per hash".into())
                }
            };
            let mut lines = vec![rate];
            lines.extend(gpu_lines);
            lines.push(extra);
            (pow_name(pow), headline, lines, Some(mined(h)))
        }
        Stage::Fold => {
            let secs = match &l.fold {
                FoldState::Running(t) => t.elapsed().as_secs_f64(),
                _ => 0.0,
            };
            (
                "Block fold",
                "proving two spends and folding them into one proof".into(),
                vec![
                    format!("{} elapsed  ·  peak RAM {}", fmt_secs(secs), fmt_bytes(l.peak_rss as usize)),
                    format!("the heaviest step: about 11 GB of RAM  ·  this machine has {}", m.ram()),
                ],
                None,
            )
        }
        Stage::Done => ("", String::new(), vec![], None),
    }
}

fn report_sections(l: &Live, m: &Machine, visuals: bool, secs: f64) -> Vec<(&'static str, Vec<(&'static str, String)>)> {
    let mut v = machine_sections(m);
    v[0].1.push(("gpu", if l.gpus.is_empty() { "none found (NVIDIA and Apple GPUs are supported)".into() } else { l.gpus.join(", ") }));
    v.push((
        "Run",
        vec![
            ("bench", format!("sig-bench {}", env!("CARGO_PKG_VERSION"))),
            ("animations", if visuals { "on (drawing uses some CPU)".into() } else { "off".into() }),
            ("total time", fmt_secs(secs)),
            ("peak RAM", fmt_bytes(l.peak_rss as usize)),
        ],
    ));
    v.push((
        "Legacy RingCT (ring of 16)",
        vec![
            ("sign", spread(&l.leg_sign)),
            ("verify", spread(&l.leg_verify)),
            ("size", fmt_bytes(l.sig_bytes)),
            ("samples", l.leg_sign.len().to_string()),
        ],
    ));
    v.push((
        "Faraday spend",
        vec![
            ("prove", spread(&l.new_prove)),
            ("prove CPU", format!("{:.0}% (about {:.1} cores busy)", avg(&l.new_prove_cpu), avg(&l.new_prove_cpu) / 100.0)),
            ("verify", spread(&l.new_verify)),
            ("size", fmt_bytes(l.proof_bytes)),
            ("samples", l.new_prove.len().to_string()),
        ],
    ));
    v.push((
        "Block fold (2 spends)",
        match &l.fold {
            FoldState::Done { bytes, secs, block_n } => vec![
                ("fold time", fmt_secs(*secs)),
                ("size", fmt_bytes(*bytes)),
                ("txs per block", format!("~{block_n} per 2 MB block")),
            ],
            _ => vec![("status", format!("skipped: the fold needs 16 GB of RAM (this machine has {})", m.ram()))],
        },
    ));
    let mut pow_rows: Vec<(&'static str, String)> = l
        .hashes
        .iter()
        .map(|(pow, h)| {
            let val = if h.skipped {
                "skipped: not enough RAM".to_string()
            } else if h.mined.hashes == 0 {
                "CPU not run".to_string()
            } else {
                format!("CPU {:<11}{} threads  ·  {} per hash per thread", fmt_rate(h.mined.rate()), h.mined.threads, fmt_hash_time(h.mined.ms_per_hash()))
            };
            let mut rows = vec![(report_pow_name(*pow), val)];
            for (name, g) in l.gpus.iter().zip(&h.gpu) {
                rows.push(("", gpu_line(name, g.as_ref())));
            }
            rows
        })
        .flatten()
        .collect();
    if let Some(ok) = l.faithful {
        pow_rows.push(("matches node PoW", if ok { "yes".into() } else { "NO".into() }));
    }
    v.push(("Proof of work", pow_rows));
    v
}
