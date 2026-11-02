pub const PERSONAL: [u8; 16] = *b"blocknet/pow/v1\0";
pub const PREFIX_LEN: usize = 92;
pub const INPUT_LEN: usize = PREFIX_LEN + 8;

#[derive(Clone, Copy, Debug)]
pub struct Header {
    pub version: u32,
    pub height: u64,
    pub prev_hash: [u8; 32],
    pub merkle_root: [u8; 32],
    pub timestamp: i64,
    pub difficulty: u64,
}

impl Header {
    pub fn serialize_for_pow(&self) -> [u8; PREFIX_LEN] {
        let mut b = [0u8; PREFIX_LEN];
        b[0..4].copy_from_slice(&self.version.to_le_bytes());
        b[4..12].copy_from_slice(&self.height.to_le_bytes());
        b[12..44].copy_from_slice(&self.prev_hash);
        b[44..76].copy_from_slice(&self.merkle_root);
        b[76..84].copy_from_slice(&self.timestamp.to_le_bytes());
        b[84..92].copy_from_slice(&self.difficulty.to_le_bytes());
        b
    }
}

const IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

const SIGMA: [[usize; 16]; 12] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
];

pub fn blake2b_h0() -> [u64; 8] {
    let mut h = IV;
    h[0] ^= 0x0101_0040;
    h[6] ^= u64::from_le_bytes(PERSONAL[0..8].try_into().unwrap());
    h[7] ^= u64::from_le_bytes(PERSONAL[8..16].try_into().unwrap());
    h
}

#[inline(always)]
fn g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

#[inline(always)]
fn compress(h: &mut [u64; 8], m: &[u64; 16], t: u64, last: bool) {
    let mut v = [0u64; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t;
    if last {
        v[14] = !v[14];
    }
    for s in &SIGMA {
        g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

pub struct Blake2bMiner {
    h0: [u64; 8],
    m: [u64; 16],
}

impl Blake2bMiner {
    pub fn new(prefix: &[u8; PREFIX_LEN]) -> Blake2bMiner {
        let mut block = [0u8; 128];
        block[..PREFIX_LEN].copy_from_slice(prefix);
        let mut m = [0u64; 16];
        for (i, w) in m.iter_mut().enumerate() {
            *w = u64::from_le_bytes(block[i * 8..i * 8 + 8].try_into().unwrap());
        }
        Blake2bMiner { h0: blake2b_h0(), m }
    }

    #[inline(always)]
    pub fn hash(&self, nonce: u64) -> [u64; 8] {
        let mut m = self.m;
        m[11] = (m[11] & 0xffff_ffff) | (nonce << 32);
        m[12] = nonce >> 32;
        let mut h = self.h0;
        compress(&mut h, &m, INPUT_LEN as u64, true);
        h
    }
}

pub fn words_to_bytes(w: &[u64; 8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    for i in 0..8 {
        out[i * 8..i * 8 + 8].copy_from_slice(&w[i].to_le_bytes());
    }
    out
}

pub fn score(w: &[u64; 8]) -> u64 {
    w[0].swap_bytes()
}

pub fn hash(prefix: &[u8; PREFIX_LEN], nonce: u64) -> [u8; 64] {
    words_to_bytes(&Blake2bMiner::new(prefix).hash(nonce))
}

pub fn target(difficulty: u64) -> [u8; 32] {
    let d = difficulty.max(1) as u128;
    let mut out = [0u8; 32];
    let mut rem: u128 = 0;
    for i in 0..4 {
        let cur = (rem << 64) | u64::MAX as u128;
        out[i * 8..i * 8 + 8].copy_from_slice(&((cur / d) as u64).to_be_bytes());
        rem = cur % d;
    }
    out
}

pub fn meets(hash: &[u8; 64], target: &[u8; 32]) -> bool {
    hash[..32] < target[..]
}

pub fn zero_bits(hash: &[u8; 64]) -> u32 {
    let mut n = 0;
    for &b in &hash[..32] {
        if b == 0 {
            n += 8;
        } else {
            return n + b.leading_zeros();
        }
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    fn prefix() -> [u8; PREFIX_LEN] {
        core::array::from_fn(|i| i as u8)
    }

    #[test]
    fn blake2b_matches_python_hashlib_with_the_personalization() {
        assert_eq!(
            hex(&hash(&prefix(), 0xC0FFEE)),
            "d161381d90bd4ab2936d355d30282084df8561e91d1e7ac026e9d907727ca806dc1dff969c1141c746a557fa8d33e8c956da938eab7b5521666f870f026440ea"
        );
    }

    #[test]
    fn the_personalization_changes_the_hash() {
        use blake2::Digest;
        let mut input = prefix().to_vec();
        input.extend_from_slice(&0xC0FFEEu64.to_le_bytes());
        assert_ne!(blake2::Blake2b512::digest(&input).as_slice(), &hash(&prefix(), 0xC0FFEE)[..]);
    }

    #[test]
    fn target_is_max_over_difficulty() {
        assert_eq!(target(1), [0xff; 32]);
        let t = target(2);
        assert_eq!(t[0], 0x7f);
        assert!(t[1..].iter().all(|&b| b == 0xff));
        let t = target(1 << 32);
        assert_eq!(&t[..4], &[0, 0, 0, 0]);
        assert_eq!(t[4], 0xff);
    }

    #[test]
    fn meets_is_strictly_below_the_target() {
        let t = target(1 << 8);
        let mut h = [0u8; 64];
        h[..32].copy_from_slice(&t);
        assert!(!meets(&h, &t));
        h[31] -= 1;
        assert!(meets(&h, &t));
    }

    #[test]
    fn score_is_the_first_eight_bytes_big_endian() {
        let w = Blake2bMiner::new(&prefix()).hash(9);
        let b = words_to_bytes(&w);
        assert_eq!(score(&w), u64::from_be_bytes(b[..8].try_into().unwrap()));
    }
}
