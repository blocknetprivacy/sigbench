use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

use cudarc::driver::{CudaContext, CudaFunction, CudaStream, LaunchConfig, PushKernelArg};
use cudarc::nvrtc::{compile_ptx_with_opts, CompileOptions};

use super::{reference, Device};
use crate::miner::Mined;
use crate::mining::{self, Pow};

const KERNELS: &str = include_str!("kernels.cu");
const PTX: &str = include_str!("kernels.ptx");
const PTX_SRC: &str = include_str!("kernels.ptx.src");

fn kernels_sha() -> String {
    use sha3::Digest as _;
    sha3::Sha3_256::digest(KERNELS.as_bytes()).iter().map(|b| format!("{b:02x}")).collect()
}

fn nvrtc(arch: &'static str) -> Option<cudarc::nvrtc::Ptx> {
    let opts = CompileOptions {
        arch: Some(arch),
        options: vec!["--std=c++14".into(), "--restrict".into()],
        name: Some("faraday_bench_kernels.cu".into()),
        ..Default::default()
    };
    quiet(move || compile_ptx_with_opts(KERNELS, opts)).and_then(|r| r.ok())
}

fn quiet<T>(f: impl FnOnce() -> T + std::panic::UnwindSafe) -> Option<T> {
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(f).ok();
    std::panic::set_hook(hook);
    r
}

pub fn devices() -> Vec<Device> {
    let Some(Ok(n)) = quiet(CudaContext::device_count) else { return Vec::new() };
    (0..n.max(0) as usize)
        .filter_map(|i| {
            let ctx = quiet(move || CudaContext::new(i))?.ok()?;
            let name = ctx.name().unwrap_or_else(|_| format!("CUDA device {i}"));
            let (_, total) = cudarc::driver::result::mem_get_info().ok()?;
            Some(Device { index: i, name, mem_bytes: total as u64 })
        })
        .collect()
}

struct Gpu {
    stream: Arc<CudaStream>,
    module: Arc<cudarc::driver::CudaModule>,
}

impl Gpu {
    fn open(dev: &Device) -> Result<Gpu, String> {
        let ctx = quiet(|| CudaContext::new(dev.index)).ok_or("CUDA library not found")?.map_err(|e| format!("{e:?}"))?;
        let (major, minor) = ctx.compute_capability().map_err(|e| format!("{e:?}"))?;
        let arch: &'static str = Box::leak(format!("compute_{major}{minor}").into_boxed_str());
        let ptx = match nvrtc(arch) {
            Some(p) => p,
            None if PTX.trim().is_empty() || PTX_SRC.trim() != kernels_sha() => {
                return Err("no NVRTC on this machine and no built-in PTX for these kernels".into())
            }
            None => cudarc::nvrtc::Ptx::from_src(PTX),
        };
        let module = ctx.load_module(ptx).map_err(|e| format!("load module: {e:?}"))?;
        Ok(Gpu { stream: ctx.default_stream(), module })
    }

    fn func(&self, name: &str) -> Result<CudaFunction, String> {
        self.module.load_function(name).map_err(|e| format!("{name}: {e:?}"))
    }
}

pub fn mine(dev: &Device, pow: Pow, seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    let gpu = Gpu::open(dev)?;
    let header = mining::header();
    let mined = match pow {
        Pow::Argon2(mib) => mine_argon2(&gpu, mib, &header, seconds, stop, progress)?,
        fast => mine_fast(&gpu, fast, &header, seconds, stop, progress)?,
    };
    Ok(mined)
}

fn mine_argon2(gpu: &Gpu, mib: u32, header: &[u8], seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    let e = |x: cudarc::driver::DriverError| format!("{x:?}");
    let s = &gpu.stream;
    let (seed_k, fill_k, final_k) = (gpu.func("build_seed_blocks_kernel")?, gpu.func("argon2id_fill_kernel")?, gpu.func("final_hashes_kernel")?);
    let argon2_type: u32 = if mib == mining::FARADAY_MIB { 0 } else { 2 };
    let m_cost_kib: u32 = mib * 1024;
    let m_blocks: u32 = m_cost_kib;
    let t_cost: u32 = 1;
    let lane_words = m_blocks as usize * 128;
    let (free, _) = cudarc::driver::result::mem_get_info().map_err(e)?;
    let lanes = ((free as f64 * 0.85) as usize / (lane_words * 8)).min(256);
    if lanes == 0 {
        return Err(format!("one {mib} MiB lane does not fit in free GPU memory ({} MiB free)", free >> 20));
    }
    let mut lane_memory = unsafe { s.alloc::<u64>(lanes * lane_words) }.map_err(e)?;
    let mut seed_blocks = s.alloc_zeros::<u64>(lanes * 256).map_err(e)?;
    let mut last_blocks = s.alloc_zeros::<u64>(lanes * 128).map_err(e)?;
    let mut hashes_out = s.alloc_zeros::<u8>(lanes * 32).map_err(e)?;
    let header_dev = s.clone_htod(header).map_err(e)?;
    let cancel = s.alloc_zeros::<u32>(1).map_err(e)?;
    let mut completed = s.alloc_zeros::<u32>(1).map_err(e)?;
    let lanes_u32 = lanes as u32;
    let header_len = header.len() as u32;
    let one: u32 = 1;

    let mut run_batch = |base: u64, check: bool| -> Result<Option<Vec<u8>>, String> {
        let nonces: Vec<u64> = (0..lanes as u64).map(|i| base + i).collect();
        let nonce_dev = s.clone_htod(&nonces).map_err(e)?;
        unsafe {
            let mut l = s.launch_builder(&seed_k);
            l.arg(&header_dev).arg(&header_len).arg(&nonce_dev).arg(&lanes_u32).arg(&m_cost_kib).arg(&t_cost).arg(&mut seed_blocks).arg(&argon2_type);
            l.launch(LaunchConfig { grid_dim: (lanes_u32.div_ceil(64), 1, 1), block_dim: (64, 1, 1), shared_mem_bytes: 0 }).map_err(e)?;
            let mut l = s.launch_builder(&fill_k);
            l.arg(&seed_blocks)
                .arg(&lanes_u32)
                .arg(&lanes_u32)
                .arg(&one)
                .arg(&m_blocks)
                .arg(&t_cost)
                .arg(&mut lane_memory)
                .arg(&mut last_blocks)
                .arg(&cancel)
                .arg(&mut completed)
                .arg(&argon2_type);
            l.launch(LaunchConfig { grid_dim: (lanes_u32, 1, 1), block_dim: (32, 1, 1), shared_mem_bytes: 0 }).map_err(e)?;
            if check {
                let mut l = s.launch_builder(&final_k);
                l.arg(&last_blocks).arg(&lanes_u32).arg(&mut hashes_out);
                l.launch(LaunchConfig { grid_dim: (lanes_u32.div_ceil(64), 1, 1), block_dim: (64, 1, 1), shared_mem_bytes: 0 }).map_err(e)?;
            }
        }
        s.synchronize().map_err(e)?;
        if check {
            Ok(Some(s.clone_dtoh(&hashes_out).map_err(e)?))
        } else {
            Ok(None)
        }
    };

    let base = 0xC0FF_EE00u64;
    let got = run_batch(base, true)?.unwrap_or_default();
    if got.get(..32) != Some(&reference(Pow::Argon2(mib), header, base)[..]) {
        return Err("GPU Argon2 hash differs from the CPU hash".into());
    }
    let start = Instant::now();
    let mut hashes = 0u64;
    let mut nonce = base + lanes as u64;
    while start.elapsed().as_secs_f64() < seconds && !stop.load(Ordering::Relaxed) {
        run_batch(nonce, false)?;
        nonce += lanes as u64;
        hashes += lanes as u64;
        progress(Mined { threads: lanes, hashes, secs: start.elapsed().as_secs_f64() });
    }
    Ok(Mined { threads: lanes, hashes, secs: start.elapsed().as_secs_f64() })
}

fn mine_fast(gpu: &Gpu, pow: Pow, header: &[u8], seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    let e = |x: cudarc::driver::DriverError| format!("{x:?}");
    let s = &gpu.stream;
    let k = gpu.func(if pow == Pow::Blake2b512 { "blake2b512_mine_kernel" } else { "sha3_512_mine_kernel" })?;
    let (blocks, threads): (u32, u32) = (2048, 256);
    let total = blocks as u64 * threads as u64;
    let mut sink = s.alloc_zeros::<u64>(total as usize).map_err(e)?;
    let mut first = s.alloc_zeros::<u8>(64).map_err(e)?;
    let header_dev = s.clone_htod(header).map_err(e)?;
    let header_len = header.len() as u32;
    let mut launch = |base: u64, per_thread: u32, digest: bool| -> Result<Vec<u8>, String> {
        unsafe {
            let mut l = s.launch_builder(&k);
            l.arg(&header_dev).arg(&header_len).arg(&base).arg(&per_thread).arg(&mut sink).arg(&mut first);
            l.launch(LaunchConfig { grid_dim: (blocks, 1, 1), block_dim: (threads, 1, 1), shared_mem_bytes: 0 }).map_err(e)?;
        }
        s.synchronize().map_err(e)?;
        if digest {
            s.clone_dtoh(&first).map_err(e)
        } else {
            Ok(Vec::new())
        }
    };
    let base = 0xC0FF_EE00u64;
    let got = launch(base, 1, true)?;
    if got != reference(pow, header, base) {
        return Err("GPU digest differs from the CPU digest".into());
    }
    let mut per_thread = 1u32;
    loop {
        let t = Instant::now();
        launch(base, per_thread, false)?;
        let ms = t.elapsed().as_secs_f64() * 1e3;
        if ms > 100.0 || per_thread >= 1 << 16 {
            per_thread = ((per_thread as f64 * 200.0 / ms.max(1.0)) as u32).clamp(1, 1 << 16);
            break;
        }
        per_thread *= 4;
    }
    let start = Instant::now();
    let mut hashes = 0u64;
    let mut nonce = base;
    while start.elapsed().as_secs_f64() < seconds && !stop.load(Ordering::Relaxed) {
        launch(nonce, per_thread, false)?;
        let n = total * per_thread as u64;
        nonce += n;
        hashes += n;
        progress(Mined { threads: total as usize, hashes, secs: start.elapsed().as_secs_f64() });
    }
    Ok(Mined { threads: total as usize, hashes, secs: start.elapsed().as_secs_f64() })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ptx_matches_the_kernel_source() {
        assert_eq!(PTX_SRC.trim(), kernels_sha(), "kernels.cu changed: run `cargo test --release write_ptx -- --ignored` where NVRTC is available");
        assert!(PTX.contains(".entry argon2id_fill_kernel"));
    }

    #[test]
    #[ignore]
    fn write_ptx() {
        let ptx = nvrtc("compute_75").expect("NVRTC not available");
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src/gpu");
        std::fs::write(format!("{dir}/kernels.ptx"), ptx.to_src()).unwrap();
        std::fs::write(format!("{dir}/kernels.ptx.src"), kernels_sha() + "\n").unwrap();
    }

    #[test]
    fn cuda_mines_every_pow_and_matches_the_cpu() {
        let devs = devices();
        let Some(dev) = devs.first() else {
            eprintln!("no CUDA device; skipped");
            return;
        };
        for pow in mining::LEVELS {
            let r = mine(dev, pow, 3.0, &AtomicBool::new(false), &mut |_| {});
            match r {
                Ok(g) => eprintln!("{}: {pow:?}: {:.3} H/s with {} in flight", dev.name, g.rate(), g.threads),
                Err(err) if err.contains("does not fit") => eprintln!("{pow:?}: {err}"),
                Err(err) => panic!("{pow:?}: {err}"),
            }
        }
    }
}
