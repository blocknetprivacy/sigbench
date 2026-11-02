use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::mining::{self, Pow};

#[derive(Clone, Copy, Debug, Default)]
pub struct Mined {
    pub threads: usize,
    pub hashes: u64,
    pub secs: f64,
}

impl Mined {
    pub fn rate(&self) -> f64 {
        if self.secs > 0.0 { self.hashes as f64 / self.secs } else { 0.0 }
    }
    pub fn ms_per_hash(&self) -> f64 {
        if self.hashes > 0 { self.secs * 1e3 * self.threads as f64 / self.hashes as f64 } else { 0.0 }
    }
}

pub fn cpu_threads(pow: Pow) -> usize {
    let cpus = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let _ = pow;
    cpus
}

pub fn mine_cpu(pow: Pow, threads: usize, seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Mined {
    let header = mining::header();
    let count = Arc::new(AtomicU64::new(0));
    let done = Arc::new(AtomicBool::new(false));
    let start = Instant::now();
    let workers: Vec<_> = (0..threads)
        .map(|t| {
            let (count, done, header) = (count.clone(), done.clone(), header.clone());
            std::thread::spawn(move || {
                let mut nonce = (t as u64) << 40;
                while !done.load(Ordering::Relaxed) {
                    for _ in 0..4096 {
                        std::hint::black_box(mining::fast_hash(pow, &header, nonce));
                        nonce += 1;
                    }
                    count.fetch_add(4096, Ordering::Relaxed);
                }
            })
        })
        .collect();
    let snapshot = || Mined { threads, hashes: count.load(Ordering::Relaxed), secs: start.elapsed().as_secs_f64() };
    while start.elapsed().as_secs_f64() < seconds && !stop.load(Ordering::Relaxed) {
        std::thread::sleep(Duration::from_millis(250));
        progress(snapshot());
    }
    done.store(true, Ordering::Relaxed);
    let result = snapshot();
    for w in workers {
        let _ = w.join();
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_hashes_mine_on_all_threads() {
        let stop = AtomicBool::new(false);
        for pow in crate::mining::LEVELS {
            let t = cpu_threads(pow);
            let m = mine_cpu(pow, t, 0.3, &stop, &mut |_| {});
            assert_eq!(m.threads, t);
            assert!(m.hashes >= 4096 * t as u64, "{pow:?}: {} hashes on {t} threads", m.hashes);
        }
    }
}
