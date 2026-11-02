
use std::collections::{HashSet, VecDeque};
use std::io::Read;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Instant;

use sha3::{Digest, Sha3_256};
use vole::wire::{self, Note, Scan, Tx};

use crate::address;
use crate::mine;
use crate::pow;

pub const SHAPES: [usize; 4] = [2, 4, 8, 16];
pub const RUNS_PER_SHAPE: usize = 100;
pub const SEND_RUNS: usize = RUNS_PER_SHAPE * SHAPES.len();
pub const POOL: usize = RUNS_PER_SHAPE * (2 + 4 + 8 + 16);
pub const NSET: usize = 1 << 20;
pub const FIELD_W: usize = 1036;
pub const FIELD_H: usize = 1013;
pub const ETA: usize = 45;

pub const ADDRESS: usize = 0;
pub const SET: usize = 1;
pub const SEND: usize = 2;
pub const SCAN: usize = 3;
pub const BLOCK: usize = 4;
pub const MINING: usize = 5;
pub const MINE_SECS: f64 = 3.0;
pub const REPORT: usize = 6;
pub const STEPS: [&str; 7] = ["Address", "Anonymity set", "Send transaction", "Wallet scan", "Block", "Mining", "Report"];
pub const LIVE_STEPS: usize = 7;

pub struct AddrRes {
    pub wallet: address::Wallet,
    pub key_bits: Vec<bool>,
    pub trace: Vec<[u64; 25]>,
    pub groups: Vec<u8>,
}

pub struct SetRes {
    pub ms: f64,
    pub field: Vec<u8>,
    pub real: usize,
    pub commit: Vec<u8>,
    pub left: [bool; ETA],
    pub right: [bool; ETA],
}

#[derive(Default, Clone)]
pub struct ShapeStat {
    pub proof_bytes: usize,
    pub runs: u32,
    pub prove_sum: f64,
    pub verify_sum: f64,
    pub prove: Vec<f64>,
    pub verify: Vec<f64>,
}

impl ShapeStat {
    pub fn prove_ms(&self) -> f64 {
        self.prove_sum / self.runs.max(1) as f64
    }
    pub fn verify_ms(&self) -> f64 {
        self.verify_sum / self.runs.max(1) as f64
    }
}

pub struct ScanRes {
    pub ms: f64,
    pub marks: Vec<Scan>,
    pub mine: usize,
    pub expected: usize,
    pub tag_only: usize,
    pub ok: bool,
}

impl ScanRes {
    pub fn rate(&self) -> f64 {
        self.marks.len() as f64 / (self.ms / 1000.0).max(1e-9)
    }
}

pub const CELL: usize = 1024;

pub struct BlockRes {
    pub txs: Vec<(usize, usize)>,
    pub cells: Vec<Vec<u8>>,
    pub bytes: usize,
    pub checked: usize,
    pub check_ms: Option<f64>,
    pub pruned: usize,
    pub pruned_cells: Vec<u8>,
    pub ok: bool,
}

pub const FARADAY_V1_BLOCK_MIN: f64 = 10.0;
pub const FARADAY_V1_ONE_BUILDER_PER_BLOCK: usize = 15;
pub const FARADAY_V1_CAP_PER_BLOCK: usize = 64;

pub struct MineRun {
    pub place: &'static str,
    pub threads: usize,
    pub hashes: u64,
    pub secs: f64,
    pub best: [u8; 64],
    pub ok: bool,
    pub done: bool,
}

impl MineRun {
    pub fn rate(&self) -> f64 {
        self.hashes as f64 / self.secs.max(1e-9)
    }
}

pub struct Live {
    pub go: usize,
    pub addr: Option<Arc<AddrRes>>,
    pub set: Option<Arc<SetRes>>,
    pub stats: Vec<ShapeStat>,
    pub sends: usize,
    pub last: usize,
    pub scan: Option<Arc<ScanRes>>,
    pub block: Option<BlockRes>,
    pub mine_input: Option<[u8; pow::PREFIX_LEN]>,
    pub mine: Vec<MineRun>,
    pub mine_total: usize,
    pub mine_nonce: u64,
    pub rain: VecDeque<[u8; 32]>,
    pub gpu: Option<String>,
    pub report: Option<ReportRes>,
}

pub struct ReportRes {
    pub path: String,
}

impl Live {
    pub fn done(&self, step: usize) -> bool {
        match step {
            ADDRESS => self.addr.is_some(),
            SET => self.set.is_some(),
            SEND => self.sends >= SEND_RUNS,
            SCAN => self.scan.is_some(),
            BLOCK => self.block.as_ref().is_some_and(|b| b.check_ms.is_some()),
            MINING => self.mine_total > 0 && self.mine.len() == self.mine_total && self.mine.iter().all(|r| r.done),
            REPORT => self.report.is_some(),
            _ => false,
        }
    }

    pub fn send_rate(&self) -> f64 {
        let busy: f64 = self.stats.iter().map(|s| s.prove_sum + s.verify_sum).sum();
        self.sends as f64 / (busy / 1000.0).max(1e-9)
    }
}

pub struct Shared {
    pub live: Mutex<Live>,
    pub wake: Condvar,
    pub set_built: AtomicUsize,
}

fn new_shared() -> Arc<Shared> {
    let live = Live { go: ADDRESS, addr: None, set: None, stats: vec![ShapeStat::default(); SHAPES.len()], sends: 0, last: 0, scan: None, block: None, mine_input: None, mine: Vec::new(), mine_total: 0, mine_nonce: 0, rain: VecDeque::new(), gpu: None, report: None };
    Arc::new(Shared { live: Mutex::new(live), wake: Condvar::new(), set_built: AtomicUsize::new(0) })
}

pub fn start() -> Arc<Shared> {
    let sh = new_shared();
    let worker = sh.clone();
    std::thread::spawn(move || run(&worker));
    sh
}

pub fn allow(sh: &Shared, step: usize) {
    let mut g = sh.live.lock().unwrap();
    g.go = g.go.max(step + 1);
    sh.wake.notify_all();
}

fn wait_for(sh: &Shared, step: usize) {
    let mut g = sh.live.lock().unwrap();
    while g.go <= step {
        g = sh.wake.wait(g).unwrap();
    }
}

fn ms_since(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1000.0
}

fn zero_cpu() -> std::time::Duration {
    std::time::Duration::ZERO
}

struct Drbg {
    seed: [u8; 32],
    ctr: u64,
}

impl Drbg {
    fn os() -> Drbg {
        let mut seed = [0u8; 32];
        std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut seed)).expect("OS randomness");
        Drbg { seed, ctr: 0 }
    }
    fn bytes(&mut self) -> [u8; 32] {
        self.ctr += 1;
        Sha3_256::new().chain_update(self.seed).chain_update(self.ctr.to_le_bytes()).finalize().into()
    }
    fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.bytes()[..8].try_into().unwrap())
    }
    fn bit(&mut self) -> bool {
        self.bytes()[0] & 1 == 1
    }
}

fn run(sh: &Shared) {
    let mut rng = Drbg::os();

    wait_for(sh, ADDRESS);
    let addr = Arc::new(address_step(&mut rng));
    sh.live.lock().unwrap().addr = Some(addr.clone());

    wait_for(sh, SET);
    let (prep, set) = set_step(sh, &mut rng);
    sh.live.lock().unwrap().set = Some(Arc::new(set));

    wait_for(sh, SEND);
    let (outputs, expected, two) = send_step(sh, &mut rng, &prep, &addr.wallet);

    wait_for(sh, SCAN);
    let scan = scan_step(&addr.wallet, &outputs, &expected);
    sh.live.lock().unwrap().scan = Some(Arc::new(scan));

    wait_for(sh, BLOCK);
    let root = block_step(sh, &prep, &two);

    wait_for(sh, MINING);
    mining_step(sh, root);

    wait_for(sh, REPORT);
    let report = crate::report::write(&sh.live.lock().unwrap());
    sh.live.lock().unwrap().report = Some(report);
}

fn mining_step(sh: &Shared, root: [u8; 32]) {
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs() as i64);
    let prefix = pow::Header { version: 1, height: 1, prev_hash: [0u8; 32], merkle_root: root, timestamp: now, difficulty: 1 }.serialize_for_pow();
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let gpu = mine::gpu_name();
    let mut plan: Vec<(&'static str, usize)> = vec![("one core", 1), ("all cores", cores)];
    if gpu.is_some() {
        plan.push(("GPU", 0));
    }
    {
        let mut g = sh.live.lock().unwrap();
        g.mine_input = Some(prefix);
        g.mine_total = plan.len();
        g.gpu = gpu;
    }
    for (place, threads) in plan {
        let idx = {
            let mut g = sh.live.lock().unwrap();
            g.mine.push(mine::new_run(place, threads));
            g.rain.clear();
            g.mine.len() - 1
        };
        if threads == 0 {
            if let Err(e) = mine::gpu(sh, idx, &prefix, MINE_SECS) {
                eprintln!("{e}");
                sh.live.lock().unwrap().mine[idx].ok = false;
            }
        } else {
            mine::cpu(sh, idx, &prefix, threads, MINE_SECS);
        }
        sh.live.lock().unwrap().mine[idx].done = true;
    }
}

fn address_step(rng: &mut Drbg) -> AddrRes {
    let wallet = address::wallet(&rng.bytes());
    let mut msg = b"blocknet-address-v1".to_vec();
    msg.extend(&wallet.kem_key);
    msg.extend(&wallet.owner_key);
    let (hash, trace) = crate::sha3_trace(&msg);
    assert_eq!(hash, wallet.hash, "traced SHA3 must equal the real address hash");
    let key_bits = wallet.kem_key.iter().chain(wallet.owner_key.iter()).flat_map(|b| (0..8).map(move |i| (b >> (7 - i)) & 1 == 1)).collect();
    let groups = wallet.address.bytes().map(|c| address::CHARSET.iter().position(|&x| x == c).unwrap() as u8).collect();
    AddrRes { wallet, key_bits, trace, groups }
}

fn set_step(sh: &Shared, rng: &mut Drbg) -> (vole::Prepared, SetRes) {
    let prep = vole::prepare_seeded(&rng.bytes(), POOL, Some(&sh.set_built));
    sh.set_built.store(NSET, Ordering::Relaxed);
    let ms = vole::set_build_ms(&prep);
    let data = vole::set_data(&prep);
    let mut field = vec![0u8; FIELD_W * FIELD_H];
    for (i, px) in field.iter_mut().take(NSET).enumerate() {
        *px = data[i * 80];
    }
    let real = vole::real_index(&prep, 0);
    let commit = data[real * 80..real * 80 + 80].to_vec();
    let (left, right) = (crate::ball(real / FIELD_W), crate::ball(real % FIELD_W));
    (prep, SetRes { ms, field, real, commit, left, right })
}

fn send_step(sh: &Shared, rng: &mut Drbg, prep: &vole::Prepared, me: &address::Wallet) -> (Vec<wire::Output>, Vec<Option<u64>>, Vec<Vec<u8>>) {
    let other = address::wallet(&rng.bytes());
    let recipients = [(me.dk.encapsulation_key().clone(), me.owner_key), (other.dk.encapsulation_key().clone(), other.owner_key)];
    let (mut outputs, mut expected, mut two) = (Vec::new(), Vec::new(), Vec::new());
    let mut coin = 0;
    for _ in 0..RUNS_PER_SHAPE {
        for (i, &n) in SHAPES.iter().enumerate() {
            let (mut to, mut seeds, mut notes, mut mine) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
            for _ in 0..n {
                let ours = rng.bit();
                let (ek, pk) = &recipients[if ours { 0 } else { 1 }];
                let note = Note::to(ek, rng.bytes());
                to.push(*pk);
                seeds.push(note.coin_seed());
                notes.push(note);
                mine.push(ours);
            }
            let sent = vole::send(prep, n, rng.u64(), coin, &to, &seeds, zero_cpu);
            coin += n;
            let bytes = wire::build_tx(&sent.public, sent.proof, &notes).serialize();
            let (tx, _) = Tx::parse(&bytes).expect("a sent transaction parses");
            for (k, o) in tx.outputs.into_iter().enumerate() {
                outputs.push(o);
                expected.push(mine[k].then_some(sent.public.amounts[k]));
            }
            if n == 2 {
                two.push(bytes);
            }
            let m = &sent.measure;
            let mut g = sh.live.lock().unwrap();
            g.last = i;
            g.sends += 1;
            let st = &mut g.stats[i];
            st.proof_bytes = m.proof_bytes;
            st.runs += 1;
            st.prove_sum += m.prove_wall.as_secs_f64() * 1e3;
            st.verify_sum += m.verify_wall.as_secs_f64() * 1e3;
            st.prove.push(m.prove_wall.as_secs_f64() * 1e3);
            st.verify.push(m.verify_wall.as_secs_f64() * 1e3);
        }
    }
    (outputs, expected, two)
}

fn scan_step(me: &address::Wallet, outputs: &[wire::Output], expected: &[Option<u64>]) -> ScanRes {
    let t = Instant::now();
    let marks: Vec<Scan> = outputs.iter().map(|o| wire::scan(&me.dk, &me.owner_key, o)).collect();
    let ms = ms_since(t);
    let ok = marks.iter().zip(expected).all(|(m, e)| match (m, e) {
        (Scan::Mine(a), Some(b)) => a == b,
        (Scan::Mine(_), None) | (_, Some(_)) => false,
        _ => true,
    });
    let mine = marks.iter().filter(|m| matches!(m, Scan::Mine(_))).count();
    let tag_only = marks.iter().filter(|m| **m == Scan::TagOnly).count();
    ScanRes { ms, marks, mine, expected: expected.iter().flatten().count(), tag_only, ok }
}

fn block_step(sh: &Shared, prep: &vole::Prepared, two: &[Vec<u8>]) -> [u8; 32] {
    let proof_part = 4 + vole::proof_bytes(2);
    let room = wire::MAX_BLOCK - wire::HEADER_LEN - 4;
    let mut body = Vec::new();
    let mut txs = Vec::new();
    let mut cells = Vec::new();
    let mut root = Sha3_256::new();
    for b in two {
        if body.len() + b.len() > room {
            break;
        }
        body.extend_from_slice(b);
        txs.push((b.len() - proof_part, proof_part));
        cells.push(b.chunks(CELL).map(|c| c[0]).collect());
        root.update(Sha3_256::digest(b));
    }
    let digest = Tx::parse(&two[0]).unwrap().0.set_digest;
    let mut block = Vec::with_capacity(wire::MAX_BLOCK);
    block.extend_from_slice(&4u32.to_le_bytes());
    block.extend_from_slice(&1u64.to_le_bytes());
    block.extend_from_slice(&[0u8; 32]);
    block.extend_from_slice(&root.finalize());
    block.extend_from_slice(&digest);
    block.extend_from_slice(&[0u8; 24]);
    assert_eq!(block.len(), wire::HEADER_LEN);
    block.extend_from_slice(&(txs.len() as u32).to_le_bytes());
    block.extend_from_slice(&body);
    let count = txs.len();
    sh.live.lock().unwrap().block = Some(BlockRes { txs, cells, bytes: block.len(), checked: 0, check_ms: None, pruned: 0, pruned_cells: Vec::new(), ok: false });

    let t = Instant::now();
    let header = &block[..wire::HEADER_LEN];
    let mut at = wire::HEADER_LEN;
    let n = u32::from_le_bytes(block[at..at + 4].try_into().unwrap()) as usize;
    at += 4;
    let mut ok = n == count;
    let mut seen = HashSet::new();
    let mut root = Sha3_256::new();
    let mut pruned = header.to_vec();
    pruned.extend_from_slice(&(n as u32).to_le_bytes());
    for _ in 0..n {
        let Some((tx, used)) = Tx::parse(&block[at..]) else {
            ok = false;
            break;
        };
        root.update(Sha3_256::digest(&block[at..at + used]));
        at += used;
        ok &= tx.set_digest[..] == header[76..108];
        ok &= tx.nullifiers.iter().all(|nf| seen.insert(*nf));
        ok &= vole::verify_tx(prep, &tx);
        pruned.extend_from_slice(&tx.metadata());
        sh.live.lock().unwrap().block.as_mut().unwrap().checked += 1;
    }
    ok &= at == block.len() && root.finalize().as_slice() == &header[44..76];
    let check_ms = ms_since(t);
    let mut g = sh.live.lock().unwrap();
    let b = g.block.as_mut().unwrap();
    b.ok = ok;
    b.pruned = pruned.len();
    b.pruned_cells = pruned.chunks(CELL).map(|c| c[0]).collect();
    b.check_ms = Some(check_ms);
    header[44..76].try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "about 20 s: run with --ignored"]
    fn mining_runs_and_the_gpu_matches_the_cpu() {
        let sh = new_shared();
        mining_step(&sh, [7u8; 32]);
        let g = sh.live.lock().unwrap();
        assert!(g.done(MINING));
        for r in &g.mine {
            println!("BLAKE2b-512 {} x{}: {:.2} MH/s, best {} zero bits, ok {}", r.place, r.threads, r.rate() / 1e6, pow::zero_bits(&r.best), r.ok);
            assert!(r.ok && r.hashes > 0);
        }
    }

    #[test]
    #[ignore = "about 90 s: run with --ignored"]
    fn every_step_runs_and_checks_out() {
        let sh = start();
        allow(&sh, MINING);
        loop {
            std::thread::sleep(std::time::Duration::from_millis(200));
            let g = sh.live.lock().unwrap();
            if g.done(MINING) {
                println!("{}", crate::report::text(&g));
                let s = g.scan.as_ref().unwrap();
                let b = g.block.as_ref().unwrap();
                println!("set {:.0} ms; sends {}; scan {} outputs, {} mine of {}, {} tag-only, {:.0}/s; block {} tx, {} B, checked in {:.0} ms, pruned {} B",
                    g.set.as_ref().unwrap().ms, g.sends, s.marks.len(), s.mine, s.expected, s.tag_only, s.rate(), b.txs.len(), b.bytes, b.check_ms.unwrap(), b.pruned);
                assert!(s.ok && b.ok);
                assert_eq!(g.set.as_ref().unwrap().field.len(), FIELD_W * FIELD_H, "the field texture is the full grid");
                assert_eq!(g.sends, SEND_RUNS);
                assert_eq!(b.checked, b.txs.len());
                return;
            }
        }
    }
}
