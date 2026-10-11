use ml_kem::{DecapsulationKey, Decapsulate, MlKem512, MlKem768, Seed, B32};
use sha3::{Digest, Sha3_512};
use std::hint::black_box;
use std::time::{Duration, Instant};

const CTS: usize = 512;
const MIN_TIME: Duration = Duration::from_secs(3);

const BLOCKS_PER_YEAR: f64 = 365.0 * 24.0 * 6.0;
const OUTPUTS_PER_FULL_BLOCK: f64 = 900.0 * 2.0;

fn sha3_512(parts: &[&[u8]]) -> [u8; 64] {
    let mut h = Sha3_512::new();
    for p in parts {
        h.update(p);
    }
    h.finalize().into()
}

fn cpu_secs() -> Option<f64> {
    let stat = std::fs::read_to_string("/proc/self/stat").ok()?;
    let f: Vec<&str> = stat.rsplit_once(')')?.1.split_whitespace().collect();
    Some((f.get(11)?.parse::<f64>().ok()? + f.get(12)?.parse::<f64>().ok()?) / 100.0)
}

struct Rates {
    decaps: f64,
    scan: f64,
    matched: f64,
    cpu_share: Option<f64>,
    all_cores: f64,
    threads: usize,
    ct_bytes: usize,
}

fn time_per_call(mut f: impl FnMut(usize)) -> (f64, Option<f64>) {
    let (t, c) = (Instant::now(), cpu_secs());
    let mut n = 0usize;
    while t.elapsed() < MIN_TIME {
        for i in 0..CTS {
            f(i);
        }
        n += CTS;
    }
    let wall = t.elapsed().as_secs_f64();
    let share = c.zip(cpu_secs()).map(|(a, b)| (b - a) / wall);
    (wall / n as f64, share)
}

macro_rules! measure_kem {
    ($kem:ty) => {{
        let dk = DecapsulationKey::<$kem>::from_seed(Seed::from([7u8; 64]));
        let ek = dk.encapsulation_key().clone();
        let cts: Vec<_> = (0..CTS)
            .map(|i| {
                let m = B32::from(core::array::from_fn::<u8, 32, _>(|j| (i * 31 + j) as u8));
                ek.encapsulate_deterministic(&m).0
            })
            .collect();
        let ct_bytes = cts[0].len();
        let (decaps, _) = time_per_call(|i| {
            black_box(dk.decapsulate(black_box(&cts[i])));
        });
        let scan_one = |i: usize| {
            let ss = dk.decapsulate(black_box(&cts[i]));
            black_box(sha3_512(&[b"blocknet_vtag", ss.as_slice()])[0]);
        };
        let (scan, cpu_share) = time_per_call(scan_one);
        let ss = dk.decapsulate(&cts[0]);
        let (matched, _) = time_per_call(|i| {
            let r = sha3_512(&[b"blocknet_r", ss.as_slice()]);
            let enc = sha3_512(&[b"blocknet_enc", ss.as_slice()]);
            let nonce = sha3_512(&[b"blocknet_nonce", ss.as_slice()]);
            let lane = |x: &[u8; 64]| -> [u32; 16] {
                core::array::from_fn(|j| u32::from_le_bytes(x[4 * j..4 * j + 4].try_into().unwrap()) % 0x7f00_0001)
            };
            black_box((enc, nonce));
            black_box(pqc_poc::faraday_fold::scan_match_leaf(&lane(&r), &lane(&r), i as u64, &lane(&r)));
        });
        let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
        let per_thread: Vec<f64> = std::thread::scope(|s| {
            let hs: Vec<_> = (0..threads).map(|_| s.spawn(|| time_per_call(scan_one).0)).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let all_cores = per_thread.iter().map(|t| 1.0 / t).sum();
        Rates { decaps, scan, matched, cpu_share, all_cores, threads, ct_bytes }
    }};
}

fn report(name: &str, r: &Rates) {
    let per_output = r.scan + r.matched / 256.0;
    let one_core = 1.0 / per_output;
    let year = BLOCKS_PER_YEAR * OUTPUTS_PER_FULL_BLOCK;
    let hours = |rate: f64| year / rate / 3600.0;
    println!(
        "{name}: ciphertext {} B; decaps {:.1} us; decaps + view tag {:.1} us; match path {:.1} us; \
         1 core {:.0} outputs/s (CPU share {}); {} threads {:.0} outputs/s",
        r.ct_bytes,
        r.decaps * 1e6,
        r.scan * 1e6,
        r.matched * 1e6,
        one_core,
        r.cpu_share.map(|s| format!("{s:.2}")).unwrap_or("n/a".into()),
        r.threads,
        r.all_cores,
    );
    println!(
        "  one year of full blocks ({:.1} M outputs): {:.1} h on 1 core, {:.2} h on {} threads; \
         at 10% of capacity: {:.1} h on 1 core",
        year / 1e6,
        hours(one_core),
        hours(r.all_cores),
        r.threads,
        hours(one_core) / 10.0,
    );
}

fn main() {
    println!(
        "wallet scan (step 13), {} blocks/year x {} outputs per full block",
        BLOCKS_PER_YEAR, OUTPUTS_PER_FULL_BLOCK
    );
    let r512 = measure_kem!(MlKem512);
    report("ML-KEM-512", &r512);
    let r768 = measure_kem!(MlKem768);
    report("ML-KEM-768", &r768);
    println!(
        "ML-KEM-768 vs 512: scan time x{:.2}, ciphertext +{} B per output",
        (r768.scan + r768.matched / 256.0) / (r512.scan + r512.matched / 256.0),
        r768.ct_bytes - r512.ct_bytes
    );
}
