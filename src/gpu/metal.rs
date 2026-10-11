use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use metal::{
    Buffer, CommandQueue, CompileOptions, ComputePipelineState, Device as MtlDevice, FunctionConstantValues, MTLDataType,
    MTLResourceOptions, MTLSize,
};

use super::{reference, Device};
use crate::miner::{self, Mined};
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
    let mined = match pow {
        Pow::Argon2(mib) => mine_argon2(&gpu, dev, mib, &header, seconds, stop, progress, None)?,
        fast => mine_fast(&gpu, fast, &header, seconds, stop, progress)?,
    };
    Ok(mined)
}

#[allow(clippy::too_many_arguments)]
fn mine_argon2(
    gpu: &Gpu,
    dev: &Device,
    mib: u32,
    header: &[u8],
    seconds: f64,
    stop: &AtomicBool,
    progress: &mut dyn FnMut(Mined),
    force_lanes: Option<usize>,
) -> Result<Mined, String> {
    let argon2_type: u32 = if mib == mining::FARADAY_MIB { 0 } else { 2 };
    let m_blocks: u32 = mib * 1024;
    let t_cost: u32 = 1;
    let constants = [m_blocks, t_cost, argon2_type];
    let (seed_p, fill_p, final_p) = (gpu.pipeline("build_seed_blocks_kernel", &constants)?, gpu.pipeline("argon2id_fill_kernel", &constants)?, gpu.pipeline("final_hashes_kernel", &constants)?);
    let lane_bytes = m_blocks as u64 * 1024;
    let by_ram = miner::cpu_threads(Pow::Argon2(mib)) as u64;
    let lanes = force_lanes.unwrap_or((dev.mem_bytes * 9 / 10 / lane_bytes).min(by_ram).min(64) as usize);
    if lanes == 0 {
        return Err(format!("no room for a {mib} MiB lane in free RAM"));
    }
    let lane_memory = gpu.buffer(lanes as u64 * lane_bytes);
    let seed_blocks = gpu.buffer(lanes as u64 * 256 * 8);
    let last_blocks = gpu.buffer(lanes as u64 * 128 * 8);
    let hashes_out = gpu.buffer(lanes as u64 * 32);
    let header_buf = gpu.buffer_from(header);
    let nonce_buf = gpu.buffer(lanes as u64 * 8);
    let (cancel, completed, target, found) = (gpu.buffer(4), gpu.buffer(4), gpu.buffer(32), gpu.buffer(4));
    let lanes_u32 = lanes as u32;
    let header_len = header.len() as u32;
    let m_cost_kib = m_blocks;
    let (one, zero) = (1u32, 0u32);
    let scalar = |e: &metal::ComputeCommandEncoderRef, i: u64, v: &u32| e.set_bytes(i, 4, v as *const u32 as *const _);

    let run_batch = |base: u64, check: bool| -> Vec<u8> {
        let nonces: Vec<u8> = (0..lanes as u64).flat_map(|i| (base + i).to_le_bytes()).collect();
        unsafe { std::ptr::copy_nonoverlapping(nonces.as_ptr(), nonce_buf.contents() as *mut u8, nonces.len()) };
        let cmd = gpu.queue.new_command_buffer();
        let e = cmd.new_compute_command_encoder();
        e.set_compute_pipeline_state(&seed_p);
        e.set_buffer(0, Some(&header_buf), 0);
        e.set_buffer(1, Some(&nonce_buf), 0);
        e.set_buffer(2, Some(&seed_blocks), 0);
        scalar(e, 3, &header_len);
        scalar(e, 4, &lanes_u32);
        scalar(e, 5, &m_cost_kib);
        scalar(e, 6, &t_cost);
        e.dispatch_threads(MTLSize::new(lanes_u32.div_ceil(64) as u64 * 64, 1, 1), MTLSize::new(64, 1, 1));
        e.end_encoding();
        let e = cmd.new_compute_command_encoder();
        e.set_compute_pipeline_state(&fill_p);
        e.set_buffer(0, Some(&seed_blocks), 0);
        e.set_buffer(1, Some(&lane_memory), 0);
        e.set_buffer(2, Some(&last_blocks), 0);
        e.set_buffer(3, Some(&cancel), 0);
        e.set_buffer(4, Some(&completed), 0);
        e.set_buffer(5, Some(&target), 0);
        e.set_buffer(6, Some(&found), 0);
        scalar(e, 7, &lanes_u32);
        scalar(e, 8, &lanes_u32);
        scalar(e, 9, &one);
        scalar(e, 10, &zero);
        e.dispatch_thread_groups(MTLSize::new(lanes as u64, 1, 1), MTLSize::new(32, 1, 1));
        e.end_encoding();
        if check {
            let e = cmd.new_compute_command_encoder();
            e.set_compute_pipeline_state(&final_p);
            e.set_buffer(0, Some(&last_blocks), 0);
            e.set_buffer(1, Some(&hashes_out), 0);
            scalar(e, 2, &lanes_u32);
            e.dispatch_threads(MTLSize::new(lanes_u32.div_ceil(64) as u64 * 64, 1, 1), MTLSize::new(64, 1, 1));
            e.end_encoding();
        }
        cmd.commit();
        cmd.wait_until_completed();
        if check { read(&hashes_out, lanes * 32) } else { Vec::new() }
    };

    let base = 0xC0FF_EE00u64;
    let got = run_batch(base, true);
    if got.get(..32) != Some(&reference(Pow::Argon2(mib), header, base)[..]) {
        return Err("GPU Argon2 hash differs from the CPU hash".into());
    }
    let start = Instant::now();
    let (mut hashes, mut nonce) = (0u64, base + lanes as u64);
    while start.elapsed().as_secs_f64() < seconds && !stop.load(Ordering::Relaxed) {
        run_batch(nonce, false);
        nonce += lanes as u64;
        hashes += lanes as u64;
        progress(Mined { threads: lanes, hashes, secs: start.elapsed().as_secs_f64() });
    }
    Ok(Mined { threads: lanes, hashes, secs: start.elapsed().as_secs_f64() })
}

fn mine_fast(gpu: &Gpu, pow: Pow, header: &[u8], seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    let p = gpu.pipeline(if pow == Pow::Blake2b512 { "blake2b512_mine_kernel" } else { "sha3_512_mine_kernel" }, &[1024, 1, 2])?;
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
        let gpu = Gpu::open(dev).unwrap();
        let m = mine_argon2(&gpu, dev, mining::FARADAY_MIB, &mining::header(), 2.0, &AtomicBool::new(false), &mut |_| {}, Some(1)).unwrap();
        eprintln!("{}: Argon2d 512 MiB on 1 lane: {:.3} H/s", dev.name, m.rate());
    }
}
