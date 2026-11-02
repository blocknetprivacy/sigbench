use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use metal::{
    Buffer, CommandQueue, CompileOptions, ComputePipelineState, Device as MtlDevice, FunctionConstantValues, MTLDataType,
    MTLResourceOptions, MTLSize,
};

use super::{reference, Device};
use crate::miner::Mined;
use crate::mining::{self, Pow};

const KERNELS: &str = include_str!("kernels.metal");

pub fn devices() -> Vec<Device> {
    MtlDevice::all()
        .into_iter()
        .enumerate()
        .map(|(index, d)| Device { index, name: d.name().to_string(), mem_bytes: d.recommended_max_working_set_size() })
        .collect()
}

struct Gpu {
    device: MtlDevice,
    queue: CommandQueue,
    library: metal::Library,
}

fn u32_constants(values: &[u32]) -> FunctionConstantValues {
    let fc = FunctionConstantValues::new();
    for (i, v) in values.iter().enumerate() {
        fc.set_constant_value_at_index(v as *const u32 as *const _, MTLDataType::UInt, i as u64);
    }
    fc
}

impl Gpu {
    fn open(dev: &Device) -> Result<Gpu, String> {
        let device = MtlDevice::all().into_iter().nth(dev.index).ok_or("Metal device gone")?;
        let opts = CompileOptions::new();
        opts.set_language_version(metal::MTLLanguageVersion::V2_4);
        let library = device.new_library_with_source(KERNELS, &opts).map_err(|e| format!("Metal compile: {e}"))?;
        let queue = device.new_command_queue();
        Ok(Gpu { device, queue, library })
    }

    fn pipeline(&self, name: &str, constants: &[u32]) -> Result<ComputePipelineState, String> {
        let f = self.library.get_function(name, Some(u32_constants(constants))).map_err(|e| format!("{name}: {e}"))?;
        self.device.new_compute_pipeline_state_with_function(&f).map_err(|e| format!("{name}: {e}"))
    }

    fn buffer(&self, bytes: u64) -> Buffer {
        self.device.new_buffer(bytes.max(4), MTLResourceOptions::StorageModeShared)
    }

    fn buffer_from(&self, data: &[u8]) -> Buffer {
        let b = self.buffer(data.len() as u64);
        unsafe { std::ptr::copy_nonoverlapping(data.as_ptr(), b.contents() as *mut u8, data.len()) };
        b
    }
}

fn read(b: &Buffer, len: usize) -> Vec<u8> {
    unsafe { std::slice::from_raw_parts(b.contents() as *const u8, len).to_vec() }
}

pub fn mine(dev: &Device, pow: Pow, seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    let gpu = Gpu::open(dev)?;
    let header = mining::header();
    let _ = dev;
    mine_fast(&gpu, pow, &header, seconds, stop, progress)
}

fn mine_fast(gpu: &Gpu, pow: Pow, header: &[u8], seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    let p = gpu.pipeline(match pow { Pow::Blake2b512 => "blake2b512_mine_kernel" }, &[])?;
    let total: u64 = 256 * 1024;
    let sink = gpu.buffer(total * 8);
    let first = gpu.buffer(64);
    let header_buf = gpu.buffer_from(header);
    let header_len = header.len() as u32;
    let launch = |base: u64, per_thread: u32| {
        let cmd = gpu.queue.new_command_buffer();
        let e = cmd.new_compute_command_encoder();
        e.set_compute_pipeline_state(&p);
        e.set_buffer(0, Some(&header_buf), 0);
        e.set_buffer(1, Some(&sink), 0);
        e.set_buffer(2, Some(&first), 0);
        e.set_bytes(3, 4, &header_len as *const u32 as *const _);
        e.set_bytes(4, 8, &base as *const u64 as *const _);
        e.set_bytes(5, 4, &per_thread as *const u32 as *const _);
        e.dispatch_threads(MTLSize::new(total, 1, 1), MTLSize::new(256, 1, 1));
        e.end_encoding();
        cmd.commit();
        cmd.wait_until_completed();
    };
    let base = 0xC0FF_EE00u64;
    launch(base, 1);
    if read(&first, 64) != reference(pow, header, base) {
        return Err("GPU digest differs from the CPU digest".into());
    }
    let mut per_thread = 1u32;
    loop {
        let t = Instant::now();
        launch(base, per_thread);
        let ms = t.elapsed().as_secs_f64() * 1e3;
        if ms > 100.0 || per_thread >= 1 << 16 {
            per_thread = ((per_thread as f64 * 200.0 / ms.max(1.0)) as u32).clamp(1, 1 << 16);
            break;
        }
        per_thread *= 4;
    }
    let start = Instant::now();
    let (mut hashes, mut nonce) = (0u64, base);
    while start.elapsed().as_secs_f64() < seconds && !stop.load(Ordering::Relaxed) {
        launch(nonce, per_thread);
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
    fn metal_mines_every_pow_and_matches_the_cpu() {
        let devs = devices();
        let Some(dev) = devs.first() else {
            eprintln!("no Metal device; skipped");
            return;
        };
        for pow in mining::LEVELS {
            match mine(dev, pow, 3.0, &AtomicBool::new(false), &mut |_| {}) {
                Ok(g) => eprintln!("{}: {pow:?}: {:.3} H/s with {} in flight", dev.name, g.rate(), g.threads),
                Err(err) if err.contains("no room") => eprintln!("{pow:?}: {err}"),
                Err(err) => panic!("{pow:?}: {err}"),
            }
        }
    }
}
