use argon2::{Algorithm, Argon2, Params, Version};

pub const CURRENT_MIB: u32 = 2048;
pub const FARADAY_MIB: u32 = 512;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pow {
    Argon2(u32),
    Blake2b512,
    Sha3_512,
}

pub const LEVELS: [Pow; 4] = [Pow::Argon2(CURRENT_MIB), Pow::Argon2(FARADAY_MIB), Pow::Blake2b512, Pow::Sha3_512];

pub const MINE_SECONDS: f64 = 30.0;

pub fn algorithm(mem_mib: u32) -> Algorithm {
    if mem_mib == FARADAY_MIB {
        Algorithm::Argon2d
    } else {
        Algorithm::Argon2id
    }
}

pub fn label(pow: Pow) -> &'static str {
    match pow {
        Pow::Argon2(FARADAY_MIB) => "Argon2d 512 MiB (Faraday)",
        Pow::Argon2(_) => "Argon2id 2 GiB (current)",
        Pow::Blake2b512 => "BLAKE2b-512",
        Pow::Sha3_512 => "SHA3-512",
    }
}

pub fn fast_hash(pow: Pow, header: &[u8], nonce: u64) -> [u8; 64] {
    use blake2::Digest as _;
    let mut out = [0u8; 64];
    match pow {
        Pow::Blake2b512 => {
            let mut h = blake2::Blake2b512::new();
            h.update(header);
            h.update(nonce.to_le_bytes());
            out.copy_from_slice(&h.finalize());
        }
        Pow::Sha3_512 => {
            let mut h = sha3::Sha3_512::new();
            sha3::Digest::update(&mut h, header);
            sha3::Digest::update(&mut h, nonce.to_le_bytes());
            out.copy_from_slice(&sha3::Digest::finalize(h));
        }
        Pow::Argon2(_) => unreachable!("Argon2 is not a fast hash"),
    }
    out
}

pub fn header() -> Vec<u8> {
    (0u8..76).map(|i| i.wrapping_mul(37).wrapping_add(11)).collect()
}

pub fn pow_hash(mem_kib: u32, header: &[u8], nonce: u64) -> Result<[u8; 32], argon2::Error> {
    let params = Params::new(mem_kib, 1, 1, Some(32))?;
    let argon2 = Argon2::new(algorithm(mem_kib / 1024), Version::V0x13, params);
    let mut out = [0u8; 32];
    argon2.hash_password_into(&nonce.to_le_bytes(), header, &mut out)?;
    Ok(out)
}

pub fn faithful_2gib() -> bool {
    let h = header();
    let nonce = 0x1234_5678_9abc_def0u64;
    let mine = match pow_hash(2 * 1024 * 1024, &h, nonce) {
        Ok(m) => m,
        Err(_) => return false,
    };
    let mut theirs = [0u8; 32];
    let rc = blocknet_crypto::blocknet_pow_hash(h.as_ptr(), h.len(), nonce, theirs.as_mut_ptr());
    rc == 0 && mine == theirs
}

#[cfg(target_os = "macos")]
pub fn total_ram() -> u64 {
    let mut val: u64 = 0;
    let mut len = std::mem::size_of::<u64>();
    let name = b"hw.memsize\0";
    let rc = unsafe {
        libc::sysctlbyname(
            name.as_ptr() as *const libc::c_char,
            &mut val as *mut u64 as *mut libc::c_void,
            &mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if rc == 0 {
        val
    } else {
        0
    }
}
#[cfg(target_os = "linux")]
pub fn total_ram() -> u64 {
    std::fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("MemTotal:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|k| k.parse::<u64>().ok())
        })
        .map(|kib| kib * 1024)
        .unwrap_or(0)
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn total_ram() -> u64 {
    0
}

pub const FOLD_MIN_RAM_GIB: u64 = 16;

pub fn fold_fits() -> bool {
    let total = total_ram();
    total == 0 || total >= FOLD_MIN_RAM_GIB * 1024 * 1024 * 1024
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fast_hashes() {
        let h = header();
        for pow in [Pow::Blake2b512, Pow::Sha3_512] {
            assert_eq!(fast_hash(pow, &h, 7), fast_hash(pow, &h, 7));
            assert_ne!(fast_hash(pow, &h, 7), fast_hash(pow, &h, 8));
        }
        assert_ne!(fast_hash(Pow::Blake2b512, &h, 7), fast_hash(Pow::Sha3_512, &h, 7));
        use blake2::Digest as _;
        let empty = blake2::Blake2b512::digest(b"");
        assert_eq!(&empty[..4], &[0x78, 0x6a, 0x02, 0xf7]);
    }
}
