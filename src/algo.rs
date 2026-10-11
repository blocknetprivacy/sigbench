#![allow(dead_code)]

const B2_IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

pub const SIGMA: [[usize; 16]; 10] = [
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
];

pub const G_LANES: [[usize; 4]; 8] =
    [[0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15], [0, 5, 10, 15], [1, 6, 11, 12], [2, 7, 8, 13], [3, 4, 9, 14]];

#[derive(Clone, Copy, PartialEq)]
pub enum Arx {
    Add,
    Xor,
    Rot(u32),
}

#[derive(Clone, Copy)]
pub struct B2Op {
    pub round: usize,
    pub g: usize,
    pub lane: usize,
    pub kind: Arx,
    pub msg: Option<usize>,
}

pub struct B2Trace {
    pub m: [u64; 16],
    pub states: Vec<[u64; 16]>,
    pub ops: Vec<B2Op>,
    pub digest: [u8; 64],
}

impl B2Trace {
    pub fn after_g(&self, k: usize) -> &[u64; 16] {
        &self.states[(k * 12).min(self.states.len() - 1)]
    }
}

pub fn blake2b_trace(msg: &[u8]) -> B2Trace {
    assert!(msg.len() <= 128);
    let mut h = B2_IV;
    h[0] ^= 0x0101_0040;
    let mut block = [0u8; 128];
    block[..msg.len()].copy_from_slice(msg);
    let mut m = [0u64; 16];
    for (i, w) in m.iter_mut().enumerate() {
        *w = u64::from_le_bytes(block[i * 8..i * 8 + 8].try_into().unwrap());
    }
    let mut v = [0u64; 16];
    v[..8].copy_from_slice(&h);
    v[8..].copy_from_slice(&B2_IV);
    v[12] ^= msg.len() as u64;
    v[14] = !v[14];
    let mut states = vec![v];
    let mut ops = Vec::new();
    for round in 0..12 {
        let s = &SIGMA[round % 10];
        for (g, l) in G_LANES.iter().enumerate() {
            let [a, b, c, d] = *l;
            let (x, y) = (s[2 * g], s[2 * g + 1]);
            let steps: [(usize, Arx, Option<usize>); 12] = [
                (a, Arx::Add, Some(x)),
                (d, Arx::Xor, None),
                (d, Arx::Rot(32), None),
                (c, Arx::Add, None),
                (b, Arx::Xor, None),
                (b, Arx::Rot(24), None),
                (a, Arx::Add, Some(y)),
                (d, Arx::Xor, None),
                (d, Arx::Rot(16), None),
                (c, Arx::Add, None),
                (b, Arx::Xor, None),
                (b, Arx::Rot(63), None),
            ];
            for (lane, kind, mi) in steps {
                match (lane, kind) {
                    (l, Arx::Add) if l == a => v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[mi.unwrap()]),
                    (l, Arx::Add) if l == c => v[c] = v[c].wrapping_add(v[d]),
                    (l, Arx::Xor) if l == d => v[d] ^= v[a],
                    (l, Arx::Xor) if l == b => v[b] ^= v[c],
                    (l, Arx::Rot(r)) => v[l] = v[l].rotate_right(r),
                    _ => unreachable!(),
                }
                states.push(v);
                ops.push(B2Op { round, g, lane, kind, msg: mi });
            }
        }
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
    let mut digest = [0u8; 64];
    for (i, w) in h.iter().enumerate() {
        digest[i * 8..i * 8 + 8].copy_from_slice(&w.to_le_bytes());
    }
    B2Trace { m, states, ops, digest }
}

const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

pub const RHO: [u32; 25] = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];

pub const RATE_LANES: usize = 9;

#[derive(Clone, Copy, PartialEq)]
pub enum KStep {
    Theta,
    Rho,
    Pi,
    Chi,
    Iota,
}

pub const KSTEPS: [KStep; 5] = [KStep::Theta, KStep::Rho, KStep::Pi, KStep::Chi, KStep::Iota];

impl KStep {
    pub fn name(self) -> &'static str {
        match self {
            KStep::Theta => "θ  column parity",
            KStep::Rho => "ρ  lane rotations",
            KStep::Pi => "π  (x, y) → (y, 2x+3y)",
            KStep::Chi => "χ  a ⊕ (¬b ∧ c) along rows",
            KStep::Iota => "ι  round constant",
        }
    }
}

pub fn pi_dest(i: usize) -> usize {
    let (x, y) = (i % 5, i / 5);
    y + 5 * ((2 * x + 3 * y) % 5)
}

pub struct KTrace {
    pub block: [u64; RATE_LANES],
    pub states: Vec<[u64; 25]>,
    pub digest: [u8; 64],
}

pub fn sha3_512_trace(msg: &[u8]) -> KTrace {
    assert!(msg.len() < 72);
    let mut pad = [0u8; 72];
    pad[..msg.len()].copy_from_slice(msg);
    pad[msg.len()] ^= 0x06;
    pad[71] ^= 0x80;
    let mut block = [0u64; RATE_LANES];
    let mut a = [0u64; 25];
    for i in 0..RATE_LANES {
        block[i] = u64::from_le_bytes(pad[i * 8..i * 8 + 8].try_into().unwrap());
        a[i] ^= block[i];
    }
    let mut states = vec![a];
    for rc in RC {
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        }
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                a[x + 5 * y] ^= d;
            }
        }
        states.push(a);
        for i in 0..25 {
            a[i] = a[i].rotate_left(RHO[i]);
        }
        states.push(a);
        let mut b = [0u64; 25];
        for i in 0..25 {
            b[pi_dest(i)] = a[i];
        }
        a = b;
        states.push(a);
        let mut n = [0u64; 25];
        for y in 0..5 {
            for x in 0..5 {
                n[x + 5 * y] = a[x + 5 * y] ^ (!a[(x + 1) % 5 + 5 * y] & a[(x + 2) % 5 + 5 * y]);
            }
        }
        a = n;
        states.push(a);
        a[0] ^= rc;
        states.push(a);
    }
    let mut digest = [0u8; 64];
    for i in 0..8 {
        digest[i * 8..i * 8 + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    KTrace { block, states, digest }
}

pub fn mining_input(nonce: u64) -> Vec<u8> {
    let mut v = b"blocknet faraday bench2 header".to_vec();
    v.extend_from_slice(&nonce.to_le_bytes());
    v
}

pub fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blake2b_known_answers() {
        assert_eq!(
            hex_bytes(&blake2b_trace(b"").digest),
            "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"
        );
        assert_eq!(
            hex_bytes(&blake2b_trace(b"abc").digest),
            "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"
        );
    }

    #[test]
    fn sha3_512_known_answers() {
        assert_eq!(
            hex_bytes(&sha3_512_trace(b"").digest),
            "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"
        );
        assert_eq!(
            hex_bytes(&sha3_512_trace(b"abc").digest),
            "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
        );
    }
}
