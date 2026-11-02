use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use crate::pipeline::{MineRun, Shared};
use crate::pow::{self, PREFIX_LEN};

const RAIN: usize = 48;

fn publish(sh: &Shared, idx: usize, hashes: u64, secs: f64, best: (u64, u64), prefix: &[u8; PREFIX_LEN], sample: Option<u64>) {
    let best_hash = pow::hash(prefix, best.1);
    let sample_hash = sample.map(|n| pow::hash(prefix, n));
    let mut g = sh.live.lock().unwrap();
    let run = &mut g.mine[idx];
    run.hashes = hashes;
    run.secs = secs;
    if pow::score(&words(&best_hash)) == best.0 {
        run.best = best_hash;
    } else {
        run.ok = false;
    }
    if let Some(h) = sample_hash {
        g.mine_nonce = sample.unwrap();
        g.rain.push_front(h[..32].try_into().unwrap());
        g.rain.truncate(RAIN);
    }
}

fn words(h: &[u8; 64]) -> [u64; 8] {
    core::array::from_fn(|i| u64::from_le_bytes(h[i * 8..i * 8 + 8].try_into().unwrap()))
}

pub fn cpu(sh: &Shared, idx: usize, prefix: &[u8; PREFIX_LEN], threads: usize, secs: f64) {
    let count = AtomicU64::new(0);
    let last = AtomicU64::new(0);
    let best = Mutex::new((u64::MAX, 0u64));
    let stop = AtomicBool::new(false);
    let start = Instant::now();
    std::thread::scope(|s| {
        for t in 0..threads {
            let (count, last, best, stop) = (&count, &last, &best, &stop);
            s.spawn(move || {
                let b = pow::Blake2bMiner::new(prefix);
                let mut nonce = (t as u64) << 40;
                let mut mine = (u64::MAX, 0u64);
                while !stop.load(Ordering::Relaxed) {
                    for _ in 0..4096 {
                        let w = b.hash(nonce);
                        let sc = pow::score(&w);
                        if sc < mine.0 {
                            mine = (sc, nonce);
                        }
                        nonce += 1;
                    }
                    count.fetch_add(4096, Ordering::Relaxed);
                    if t == 0 {
                        last.store(nonce - 1, Ordering::Relaxed);
                    }
                    let mut g = best.lock().unwrap();
                    if mine.0 < g.0 {
                        *g = mine;
                    }
                }
            });
        }
        while start.elapsed().as_secs_f64() < secs {
            std::thread::sleep(Duration::from_millis(40));
            let b = *best.lock().unwrap();
            let n = last.load(Ordering::Relaxed);
            if b.0 != u64::MAX {
                publish(sh, idx, count.load(Ordering::Relaxed), start.elapsed().as_secs_f64(), b, prefix, (n > 0).then_some(n));
            }
        }
        stop.store(true, Ordering::Relaxed);
    });
    let b = *best.lock().unwrap();
    publish(sh, idx, count.load(Ordering::Relaxed), start.elapsed().as_secs_f64(), b, prefix, None);
}

#[cfg(target_os = "macos")]
pub fn gpu_name() -> Option<String> {
    metal::Device::system_default().map(|d| d.name().to_string())
}

#[cfg(not(target_os = "macos"))]
pub fn gpu_name() -> Option<String> {
    None
}

#[cfg(not(target_os = "macos"))]
pub fn gpu(_sh: &Shared, _idx: usize, _prefix: &[u8; PREFIX_LEN], _secs: f64) -> Result<(), String> {
    Err("no GPU path on this system".into())
}

#[cfg(target_os = "macos")]
pub fn gpu(sh: &Shared, idx: usize, prefix: &[u8; PREFIX_LEN], secs: f64) -> Result<(), String> {
    use metal::{CompileOptions, MTLResourceOptions, MTLSize};
    let device = metal::Device::system_default().ok_or("no Metal device")?;
    let opts = CompileOptions::new();
    opts.set_language_version(metal::MTLLanguageVersion::V2_4);
    let lib = device.new_library_with_source(include_str!("../../src/gpu/kernels.metal"), &opts).map_err(|e| format!("Metal compile: {e}"))?;
    let name = "blake2b512_pow_best";
    let f = lib.get_function(name, None).map_err(|e| format!("{name}: {e}"))?;
    let pipe = device.new_compute_pipeline_state_with_function(&f).map_err(|e| format!("{name}: {e}"))?;
    let queue = device.new_command_queue();
    let buf = |words: &[u64]| {
        let b = device.new_buffer((words.len() * 8) as u64, MTLResourceOptions::StorageModeShared);
        unsafe { std::ptr::copy_nonoverlapping(words.as_ptr(), b.contents() as *mut u64, words.len()) };
        b
    };
    let mut block = [0u8; 128];
    block[..PREFIX_LEN].copy_from_slice(prefix);
    let words: Vec<u64> = (0..16).map(|i| u64::from_le_bytes(block[i * 8..i * 8 + 8].try_into().unwrap())).collect();
    let inputs = [buf(&words)];
    let total: u64 = 256 * 1024;
    let best = device.new_buffer(total * 16, MTLResourceOptions::StorageModeShared);
    let launch = |base: u64, per_thread: u32| -> (u64, u64) {
        let cmd = queue.new_command_buffer();
        let e = cmd.new_compute_command_encoder();
        e.set_compute_pipeline_state(&pipe);
        let mut slot = 0u64;
        for b in &inputs {
            e.set_buffer(slot, Some(b), 0);
            slot += 1;
        }
        e.set_buffer(slot, Some(&best), 0);
        e.set_bytes(slot + 1, 8, &base as *const u64 as *const _);
        e.set_bytes(slot + 2, 4, &per_thread as *const u32 as *const _);
        e.dispatch_threads(MTLSize::new(total, 1, 1), MTLSize::new(256, 1, 1));
        e.end_encoding();
        cmd.commit();
        cmd.wait_until_completed();
        let r = unsafe { std::slice::from_raw_parts(best.contents() as *const u64, (total * 2) as usize) };
        r.chunks(2).map(|c| (c[0], c[1])).min().unwrap()
    };
    let mut per_thread = 1u32;
    let mut nonce = 1u64 << 56;
    loop {
        let t = Instant::now();
        launch(nonce, per_thread);
        let ms = t.elapsed().as_secs_f64() * 1e3;
        if ms > 30.0 || per_thread >= 1 << 14 {
            per_thread = ((per_thread as f64 * 120.0 / ms.max(1.0)) as u32).clamp(1, 1 << 14);
            break;
        }
        per_thread *= 4;
    }
    nonce += 1 << 40;
    let start = Instant::now();
    let mut hashes = 0u64;
    let mut top = (u64::MAX, 0u64);
    while start.elapsed().as_secs_f64() < secs {
        let b = launch(nonce, per_thread);
        let n = total * per_thread as u64;
        let sample = nonce + n / 2;
        nonce += n;
        hashes += n;
        if b < top {
            top = b;
        }
        publish(sh, idx, hashes, start.elapsed().as_secs_f64(), top, prefix, Some(sample));
    }
    Ok(())
}

pub fn new_run(place: &'static str, threads: usize) -> MineRun {
    MineRun { place, threads, hashes: 0, secs: 0.0, best: [0xff; 64], ok: true, done: false }
}
