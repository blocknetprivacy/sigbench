use std::os::raw::{c_int, c_void};
use std::time::Duration;

pub mod params;
pub mod wire;

pub const SHAPES: [usize; 4] = [2, 4, 8, 16];

#[repr(C)]
#[derive(Default, Clone, Copy)]
struct RawMeasure {
    proof_bytes: usize,
    prove_ms: f64,
    verify_ms: f64,
    prove_cpu_ms: f64,
    verify_cpu_ms: f64,
}

extern "C" {
    fn fpq_prepare() -> *mut c_void;
    fn fpq_free(p: *mut c_void);
    fn fpq_set_digest_ms(p: *const c_void) -> f64;
    fn fpq_set_size() -> usize;
    fn fpq_set_bytes() -> usize;
    fn fpq_proof_bytes(n: usize) -> usize;
    fn fpq_run(p: *const c_void, n: usize, seed: u64, m: *mut RawMeasure, cpu_ms: extern "C" fn() -> f64) -> c_int;
    fn fpq_self_check(p: *const c_void) -> c_int;
    fn fpq_commit_check(r: *const u8, pk: *const u8, amount: u64, c: *const u8) -> c_int;
    fn fpq_owner_key(seed: *const u8, seed_len: usize, pk_out: *mut u8) -> c_int;
    fn fpq_set_data(p: *const c_void) -> *const u8;
    fn fpq_real_index(p: *const c_void, j: usize) -> usize;
    fn fpq_run_full(p: *const c_void, n: usize, seed: u64, m: *mut RawMeasure, cpu_ms: extern "C" fn() -> f64, proof_out: *mut u8, witness_out: *mut u8, public_out: *mut u8) -> c_int;
    fn fpq_layout(n: usize, out: *mut usize) -> c_int;
    fn fpq_prepare_seeded(seed: *const u8, seed_len: usize, pool: usize, progress: *mut usize) -> *mut c_void;
    fn fpq_set_build_ms(p: *const c_void) -> f64;
    fn fpq_pool_size(p: *const c_void) -> usize;
    fn fpq_send(p: *const c_void, n: usize, seed: u64, first_coin: usize, out_pk: *const u8, out_seed: *const u8, m: *mut RawMeasure, cpu_ms: extern "C" fn() -> f64, proof_out: *mut u8, public_out: *mut u8) -> c_int;
    fn fpq_verify_tx(p: *const c_void, n: usize, proof: *const u8, nullifiers: *const u8, commitments: *const u8, fee: u64, set_digest: *const u8) -> c_int;
    fn fpq_coin_matches(seed: *const u8, seed_len: usize, pk: *const u8, amount: u64, c: *const u8) -> c_int;
}

fn measurement(n: usize, m: &RawMeasure) -> Measurement {
    let d = |ms: f64| Duration::from_secs_f64(ms.max(0.0) / 1000.0);
    Measurement {
        inputs: n,
        outputs: n,
        proof_bytes: m.proof_bytes,
        prove_wall: d(m.prove_ms),
        prove_cpu: d(m.prove_cpu_ms),
        verify_wall: d(m.verify_ms),
        verify_cpu: d(m.verify_cpu_ms),
    }
}

pub struct Prepared {
    raw: *mut c_void,
}

unsafe impl Send for Prepared {}
unsafe impl Sync for Prepared {}

impl Drop for Prepared {
    fn drop(&mut self) {
        unsafe { fpq_free(self.raw) }
    }
}

pub struct Measurement {
    pub inputs: usize,
    pub outputs: usize,
    pub proof_bytes: usize,
    pub prove_wall: Duration,
    pub prove_cpu: Duration,
    pub verify_wall: Duration,
    pub verify_cpu: Duration,
}

static mut CPU_NOW: Option<fn() -> Duration> = None;

extern "C" fn cpu_ms() -> f64 {
    #[allow(static_mut_refs)]
    let f = unsafe { CPU_NOW };
    f.map(|f| f().as_secs_f64() * 1000.0).unwrap_or(0.0)
}

pub fn prepare() -> Prepared {
    let raw = unsafe { fpq_prepare() };
    assert!(!raw.is_null(), "spend proof setup failed");
    Prepared { raw }
}

pub fn self_check(prep: &Prepared) -> Result<(), String> {
    if unsafe { fpq_self_check(prep.raw) } == 1 {
        Ok(())
    } else {
        Err("an honest 2-in/2-out proof failed, or a changed fee or proof byte was accepted".into())
    }
}

pub fn set_digest_ms(prep: &Prepared) -> f64 {
    unsafe { fpq_set_digest_ms(prep.raw) }
}

pub fn set_size() -> usize {
    unsafe { fpq_set_size() }
}

pub fn set_bytes() -> usize {
    unsafe { fpq_set_bytes() }
}

pub fn proof_bytes(n: usize) -> usize {
    unsafe { fpq_proof_bytes(n) }
}

pub fn run_one(prep: &Prepared, n: usize, seed: u64, cpu_now: fn() -> Duration) -> Measurement {
    unsafe { CPU_NOW = Some(cpu_now) };
    let mut m = RawMeasure::default();
    let ok = unsafe { fpq_run(prep.raw, n, seed, &mut m, cpu_ms) };
    assert!(ok == 1, "{n}-in/{n}-out spend failed to prove or verify (seed {seed})");
    let d = |ms: f64| Duration::from_secs_f64(ms.max(0.0) / 1000.0);
    Measurement {
        inputs: n,
        outputs: n,
        proof_bytes: m.proof_bytes,
        prove_wall: d(m.prove_ms),
        prove_cpu: d(m.prove_cpu_ms),
        verify_wall: d(m.verify_ms),
        verify_cpu: d(m.verify_cpu_ms),
    }
}

pub fn commit_check(r: &[u8; 16], pk: &[u8; 32], amount: u64, c: &[u8; params::OUT_COMMITMENT_BYTES]) -> bool {
    unsafe { fpq_commit_check(r.as_ptr(), pk.as_ptr(), amount, c.as_ptr()) == 1 }
}

pub fn owner_key(seed: &[u8]) -> [u8; 32] {
    let mut pk = [0u8; 32];
    let ok = unsafe { fpq_owner_key(seed.as_ptr(), seed.len(), pk.as_mut_ptr()) };
    assert!(ok == 1, "owner key derivation failed");
    pk
}

pub fn set_data(prep: &Prepared) -> &[u8] {
    unsafe { std::slice::from_raw_parts(fpq_set_data(prep.raw), set_bytes()) }
}

pub fn real_index(prep: &Prepared, j: usize) -> usize {
    unsafe { fpq_real_index(prep.raw, j) }
}

pub struct Full {
    pub measure: Measurement,
    pub proof: Vec<u8>,
    pub witness: Vec<u8>,
    pub layout: [usize; 6],
    pub public: wire::Public,
}

pub fn layout(n: usize) -> [usize; 6] {
    let mut out = [0usize; 6];
    unsafe { fpq_layout(n, out.as_mut_ptr()) };
    out
}

pub fn run_full(prep: &Prepared, n: usize, seed: u64, cpu_now: fn() -> Duration) -> Full {
    unsafe { CPU_NOW = Some(cpu_now) };
    let layout = layout(n);
    let mut proof = vec![0u8; proof_bytes(n)];
    let mut witness = vec![0u8; layout[5]];
    let mut m = RawMeasure::default();
    let mut public = vec![0u8; wire::Public::bytes(n)];
    let ok = unsafe { fpq_run_full(prep.raw, n, seed, &mut m, cpu_ms, proof.as_mut_ptr(), witness.as_mut_ptr(), public.as_mut_ptr()) };
    assert!(ok == 1, "{n}-in/{n}-out spend failed (seed {seed})");
    let d = |ms: f64| Duration::from_secs_f64(ms.max(0.0) / 1000.0);
    let measure = Measurement {
        inputs: n,
        outputs: n,
        proof_bytes: m.proof_bytes,
        prove_wall: d(m.prove_ms),
        prove_cpu: d(m.prove_cpu_ms),
        verify_wall: d(m.verify_ms),
        verify_cpu: d(m.verify_cpu_ms),
    };
    Full { measure, proof, witness, layout, public: wire::Public::parse(n, &public) }
}

pub fn prepare_seeded(seed: &[u8; 32], pool: usize, progress: Option<&std::sync::atomic::AtomicUsize>) -> Prepared {
    let ptr = progress.map_or(std::ptr::null_mut(), |p| p.as_ptr());
    let raw = unsafe { fpq_prepare_seeded(seed.as_ptr(), seed.len(), pool, ptr) };
    assert!(!raw.is_null(), "anonymity set build failed");
    Prepared { raw }
}

pub fn set_build_ms(prep: &Prepared) -> f64 {
    unsafe { fpq_set_build_ms(prep.raw) }
}

pub fn pool_size(prep: &Prepared) -> usize {
    unsafe { fpq_pool_size(prep.raw) }
}

pub struct Sent {
    pub measure: Measurement,
    pub proof: Vec<u8>,
    pub public: wire::Public,
}

pub fn send(prep: &Prepared, n: usize, seed: u64, first_coin: usize, to: &[[u8; 32]], coin_seed: &[[u8; 16]], cpu_now: fn() -> Duration) -> Sent {
    assert!(to.len() == n && coin_seed.len() == n);
    unsafe { CPU_NOW = Some(cpu_now) };
    let mut proof = vec![0u8; proof_bytes(n)];
    let mut public = vec![0u8; wire::Public::bytes(n)];
    let mut m = RawMeasure::default();
    let ok = unsafe { fpq_send(prep.raw, n, seed, first_coin, to.as_ptr().cast(), coin_seed.as_ptr().cast(), &mut m, cpu_ms, proof.as_mut_ptr(), public.as_mut_ptr()) };
    assert!(ok == 1, "{n}-in/{n}-out send failed to prove or verify (coins {first_coin}..)");
    Sent { measure: measurement(n, &m), proof, public: wire::Public::parse(n, &public) }
}

pub fn verify_tx(prep: &Prepared, tx: &wire::Tx) -> bool {
    let n = tx.nullifiers.len();
    if tx.outputs.len() != n || tx.proof.len() != proof_bytes(n) {
        return false;
    }
    let commitments: Vec<u8> = tx.outputs.iter().flat_map(|o| o.commitment).collect();
    unsafe { fpq_verify_tx(prep.raw, n, tx.proof.as_ptr(), tx.nullifiers.as_ptr().cast(), commitments.as_ptr(), tx.fee, tx.set_digest.as_ptr()) == 1 }
}

pub fn coin_matches(coin_seed: &[u8; 16], pk: &[u8; 32], amount: u64, c: &[u8; params::OUT_COMMITMENT_BYTES]) -> bool {
    unsafe { fpq_coin_matches(coin_seed.as_ptr(), 16, pk.as_ptr(), amount, c.as_ptr()) == 1 }
}
