use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use argon2::{Argon2, Block, Params, Version};

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

pub fn lane_bytes(pow: Pow) -> u64 {
    match pow {
        Pow::Argon2(mib) => mib as u64 * 1024 * 1024,
        _ => 0,
    }
}

#[cfg(target_os = "linux")]
pub fn available_ram() -> u64 {
    std::fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("MemAvailable:")).and_then(|l| l.split_whitespace().nth(1)?.parse::<u64>().ok()))
        .map(|kib| kib * 1024)
        .unwrap_or(0)
}

#[cfg(target_os = "macos")]
pub fn available_ram() -> u64 {
    let Ok(out) = std::process::Command::new("vm_stat").output() else { return 0 };
    let s = String::from_utf8_lossy(&out.stdout);
    let page = s
        .lines()
        .next()
        .and_then(|l| l.split("page size of ").nth(1))
        .and_then(|r| r.split_whitespace().next())
        .and_then(|n| n.parse::<u64>().ok())
        .unwrap_or(16384);
    let pages = |key: &str| -> u64 {
        s.lines()
            .find(|l| l.starts_with(key))
            .and_then(|l| l.split(':').nth(1))
            .and_then(|v| v.trim().trim_end_matches('.').parse::<u64>().ok())
            .unwrap_or(0)
    };
    (pages("Pages free") + pages("Pages inactive") + pages("Pages speculative") + pages("Pages purgeable")) * page
}

#[cfg(windows)]
pub fn available_ram() -> u64 {
    use windows_sys::Win32::System::SystemInformation::{GlobalMemoryStatusEx, MEMORYSTATUSEX};
    let mut m: MEMORYSTATUSEX = unsafe { std::mem::zeroed() };
    m.dwLength = std::mem::size_of::<MEMORYSTATUSEX>() as u32;
    if unsafe { GlobalMemoryStatusEx(&mut m) } != 0 { m.ullAvailPhys } else { 0 }
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
pub fn available_ram() -> u64 {
    0
}

pub fn cpu_threads(pow: Pow) -> usize {
    let cpus = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let lane = lane_bytes(pow);
    if lane == 0 {
        return cpus;
    }
    let avail = available_ram();
    if avail == 0 {
        return 1;
    }
    let by_ram = cpus.min((avail as f64 * 0.9 / lane as f64) as usize);
    let total = mining::total_ram();
    if by_ram == 0 && total > 0 && lane as f64 <= total as f64 * 0.45 {
        return 1;
    }
    by_ram
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
                match pow {
                    Pow::Argon2(mib) => {
                        let mem_kib = mib * 1024;
                        let params = Params::new(mem_kib, 1, 1, Some(32)).expect("argon2 params");
                        let a = Argon2::new(mining::algorithm(mib), Version::V0x13, params);
                        let mut blocks = vec![Block::default(); mem_kib as usize];
                        let mut out = [0u8; 32];
                        while !done.load(Ordering::Relaxed) {
                            if a.hash_password_into_with_memory(&nonce.to_le_bytes(), &header, &mut out, &mut blocks).is_err() {
                                break;
                            }
                            std::hint::black_box(&out);
                            nonce += 1;
                            count.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                    fast => {
                        while !done.load(Ordering::Relaxed) {
                            for _ in 0..4096 {
                                std::hint::black_box(mining::fast_hash(fast, &header, nonce));
                                nonce += 1;
                            }
                            count.fetch_add(4096, Ordering::Relaxed);
                        }
                    }
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
        for pow in [Pow::Blake2b512, Pow::Sha3_512] {
            let t = cpu_threads(pow);
            let m = mine_cpu(pow, t, 0.3, &stop, &mut |_| {});
            assert_eq!(m.threads, t);
            assert!(m.hashes >= 4096 * t as u64, "{pow:?}: {} hashes on {t} threads", m.hashes);
        }
    }

    #[test]
    fn argon2_mines_on_threads_that_fit() {
        let pow = Pow::Argon2(mining::FARADAY_MIB);
        let t = cpu_threads(pow).min(2);
        if t == 0 {
            return;
        }
        let m = mine_cpu(pow, t, 2.0, &AtomicBool::new(false), &mut |_| {});
        assert!(m.hashes >= t as u64, "{} hashes on {t} threads", m.hashes);
        assert!(m.ms_per_hash() > 1.0);
    }
}
