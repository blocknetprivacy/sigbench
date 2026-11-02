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
    mine_fast(&gpu, pow, &header, seconds, stop, progress)
}

fn mine_fast(gpu: &Gpu, pow: Pow, header: &[u8], seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    let e = |x: cudarc::driver::DriverError| format!("{x:?}");
    let s = &gpu.stream;
    let k = gpu.func(match pow { Pow::Blake2b512 => "blake2b512_mine_kernel" })?;
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
        assert!(PTX.contains(".entry blake2b512_mine_kernel") && !PTX.contains("argon2"));
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
