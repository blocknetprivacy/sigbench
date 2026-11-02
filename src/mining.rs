#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pow {
    Blake2b512,
}

pub const LEVELS: [Pow; 1] = [Pow::Blake2b512];

pub const MINE_SECONDS: f64 = 30.0;

pub fn label(pow: Pow) -> &'static str {
    match pow {
        Pow::Blake2b512 => "BLAKE2b-512",
    }
}

pub fn fast_hash(pow: Pow, header: &[u8], nonce: u64) -> [u8; 64] {
    let prefix: [u8; crate::pow::PREFIX_LEN] = header.try_into().expect("a 92-byte SerializeForPoW header");
    match pow {
        Pow::Blake2b512 => crate::pow::hash(&prefix, nonce),
    }
}

pub fn header() -> Vec<u8> {
    crate::pow::Header { version: 1, height: 71_247, prev_hash: [0x5a; 32], merkle_root: [0xa5; 32], timestamp: 1_793_580_126, difficulty: 37_894_520 }
        .serialize_for_pow()
        .to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fast_hashes() {
        let h = header();
        for pow in LEVELS {
            assert_eq!(fast_hash(pow, &h, 7), fast_hash(pow, &h, 7));
            assert_ne!(fast_hash(pow, &h, 7), fast_hash(pow, &h, 8));
        }
        use blake2::Digest as _;
        let empty = blake2::Blake2b512::digest(b"");
        assert_eq!(&empty[..4], &[0x78, 0x6a, 0x02, 0xf7]);
    }
}
