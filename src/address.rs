use ml_kem::{DecapsulationKey, KeyExport, MlKem768, Seed};
use sha3::{Digest, Sha3_256};

pub const NETWORK: &str = "blocknet";
pub const LEN: usize = 58;
pub const CHARSET: &[u8; 32] = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";
const BECH32M: u32 = 0x2bc8_30a3;

pub struct Wallet {
    pub dk: DecapsulationKey<MlKem768>,
    pub kem_key: Vec<u8>,
    pub owner_key: [u8; 32],
    pub hash: [u8; 32],
    pub address: String,
}

fn polymod(values: &[u8]) -> u32 {
    const GEN: [u32; 5] = [0x3b6a_57b2, 0x2650_8e6d, 0x1ea1_19fa, 0x3d42_33dd, 0x2a14_62b3];
    let mut chk: u32 = 1;
    for &v in values {
        let top = chk >> 25;
        chk = ((chk & 0x01ff_ffff) << 5) ^ v as u32;
        for (i, g) in GEN.iter().enumerate() {
            if (top >> i) & 1 == 1 {
                chk ^= g;
            }
        }
    }
    chk
}

fn hrp_expand(hrp: &str) -> Vec<u8> {
    let b = hrp.as_bytes();
    let mut v: Vec<u8> = b.iter().map(|c| c >> 5).collect();
    v.push(0);
    v.extend(b.iter().map(|c| c & 31));
    v
}

fn to_5bit(bytes: &[u8]) -> Vec<u8> {
    let (mut acc, mut bits, mut out) = (0u32, 0u32, Vec::new());
    for &b in bytes {
        acc = (acc << 8) | b as u32;
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(((acc >> bits) & 31) as u8);
        }
    }
    if bits > 0 {
        out.push(((acc << (5 - bits)) & 31) as u8);
    }
    out
}

fn from_5bit(data: &[u8]) -> Option<Vec<u8>> {
    let (mut acc, mut bits, mut out) = (0u32, 0u32, Vec::new());
    for &d in data {
        acc = (acc << 5) | d as u32;
        bits += 5;
        if bits >= 8 {
            bits -= 8;
            out.push(((acc >> bits) & 0xff) as u8);
        }
    }
    if bits >= 5 || (acc & ((1 << bits) - 1)) != 0 {
        return None;
    }
    Some(out)
}

pub fn encode(hash: &[u8; 32]) -> String {
    let data = to_5bit(hash);
    let mut pm = hrp_expand(NETWORK);
    pm.extend(&data);
    pm.extend([0u8; 6]);
    let m = polymod(&pm) ^ BECH32M;
    let mut s = String::with_capacity(LEN);
    for d in data {
        s.push(CHARSET[d as usize] as char);
    }
    for i in 0..6 {
        s.push(CHARSET[((m >> (5 * (5 - i))) & 31) as usize] as char);
    }
    s
}

pub fn decode(addr: &str) -> Option<[u8; 32]> {
    if addr.len() != LEN {
        return None;
    }
    let data: Vec<u8> = addr
        .bytes()
        .map(|c| CHARSET.iter().position(|&x| x == c).map(|p| p as u8))
        .collect::<Option<_>>()?;
    let mut pm = hrp_expand(NETWORK);
    pm.extend(&data);
    if polymod(&pm) != BECH32M {
        return None;
    }
    from_5bit(&data[..LEN - 6])?.try_into().ok()
}

pub fn key_hash(kem_key: &[u8], owner_key: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(b"blocknet-address-v1");
    h.update(kem_key);
    h.update(owner_key);
    h.finalize().into()
}

pub fn wallet(seed: &[u8; 32]) -> Wallet {
    let mut kem_seed = [0u8; 64];
    kem_seed[..32].copy_from_slice(&Sha3_256::digest([b"kem".as_slice(), seed].concat()));
    kem_seed[32..].copy_from_slice(&Sha3_256::digest([b"kem2".as_slice(), seed].concat()));
    let dk = DecapsulationKey::<MlKem768>::from_seed(Seed::from(kem_seed));
    let kem_key = dk.encapsulation_key().to_bytes().to_vec();
    let owner_key = vole::owner_key(&Sha3_256::digest([b"owner".as_slice(), seed].concat()));
    let hash = key_hash(&kem_key, &owner_key);
    Wallet { address: encode(&hash), dk, kem_key, owner_key, hash }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_address_is_58_chars_and_round_trips() {
        let w = wallet(&[7u8; 32]);
        assert_eq!(w.kem_key.len(), 1184);
        assert_eq!(w.address.len(), LEN, "{}", w.address);
        assert_eq!(decode(&w.address), Some(w.hash));
        assert_eq!(key_hash(&w.kem_key, &w.owner_key), w.hash);
        println!("{}", w.address);
    }

    #[test]
    fn every_single_typo_is_caught() {
        let w = wallet(&[9u8; 32]);
        let a = w.address.as_bytes();
        for i in 0..a.len() {
            for &c in CHARSET.iter() {
                if c == a[i] {
                    continue;
                }
                let mut b = a.to_vec();
                b[i] = c;
                assert!(decode(std::str::from_utf8(&b).unwrap()).is_none(), "typo at {i} slipped through");
            }
        }
    }

    #[test]
    fn swapped_neighbours_are_caught() {
        let w = wallet(&[3u8; 32]);
        let a = w.address.as_bytes();
        for i in 0..a.len() - 1 {
            if a[i] == a[i + 1] {
                continue;
            }
            let mut b = a.to_vec();
            b.swap(i, i + 1);
            assert!(decode(std::str::from_utf8(&b).unwrap()).is_none(), "swap at {i} slipped through");
        }
    }

    #[test]
    fn other_network_is_rejected() {
        let w = wallet(&[4u8; 32]);
        let data = to_5bit(&w.hash);
        let mut pm = hrp_expand("testnet");
        pm.extend(&data);
        pm.extend([0u8; 6]);
        let m = polymod(&pm) ^ BECH32M;
        let mut s: String = data.iter().map(|&d| CHARSET[d as usize] as char).collect();
        for i in 0..6 {
            s.push(CHARSET[((m >> (5 * (5 - i))) & 31) as usize] as char);
        }
        assert_eq!(s.len(), LEN);
        assert!(decode(&s).is_none());
    }

    #[test]
    fn bip350_vector() {
        let mut pm = hrp_expand("a");
        pm.extend([0u8; 0]);
        let s = "a1lqfn3a";
        let data: Vec<u8> = s[2..].bytes().map(|c| CHARSET.iter().position(|&x| x == c).unwrap() as u8).collect();
        pm.extend(data);
        assert_eq!(polymod(&pm), BECH32M);
    }
}
