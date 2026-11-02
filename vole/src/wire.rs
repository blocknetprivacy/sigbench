use crate::params::*;
use ml_kem::{array::Array, Decapsulate, DecapsulationKey, EncapsulationKey, MlKem768};
use sha3::{Digest, Sha3_256, Sha3_512};

pub struct Output {
    pub commitment: [u8; OUT_COMMITMENT_BYTES],
    pub ciphertext: [u8; OUT_CIPHERTEXT_BYTES],
    pub view_tag: u8,
    pub masked_amount: [u8; OUT_AMOUNT_BYTES],
    pub encrypted_memo: [u8; OUT_MEMO_BYTES],
}

impl Output {
    pub const SERIALIZED_LEN: usize = OUT_TOTAL_BYTES;

    pub fn seal(note: &Note, commitment: [u8; OUT_COMMITMENT_BYTES], amount: u64, memo: &[u8]) -> Output {
        let amask = note.mask(b"blocknet_amount", 0);
        let masked_amount: [u8; OUT_AMOUNT_BYTES] = core::array::from_fn(|i| amount.to_le_bytes()[i] ^ amask[i]);
        let mut encrypted_memo = [0u8; OUT_MEMO_BYTES];
        for (b, chunk) in encrypted_memo.chunks_mut(64).enumerate() {
            let k = note.mask(b"blocknet_memo", b as u8);
            for (i, c) in chunk.iter_mut().enumerate() {
                *c = memo.get(b * 64 + i).copied().unwrap_or(0) ^ k[i];
            }
        }
        Output { commitment, ciphertext: note.ciphertext, view_tag: note.view_tag(), masked_amount, encrypted_memo }
    }

    fn read(b: &[u8]) -> Output {
        let (commitment, b) = b.split_at(OUT_COMMITMENT_BYTES);
        let (ciphertext, b) = b.split_at(OUT_CIPHERTEXT_BYTES);
        let (view_tag, b) = b.split_at(1);
        let (masked_amount, encrypted_memo) = b.split_at(OUT_AMOUNT_BYTES);
        Output {
            commitment: commitment.try_into().unwrap(),
            ciphertext: ciphertext.try_into().unwrap(),
            view_tag: view_tag[0],
            masked_amount: masked_amount.try_into().unwrap(),
            encrypted_memo: encrypted_memo.try_into().unwrap(),
        }
    }

    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.commitment);
        buf.extend_from_slice(&self.ciphertext);
        buf.push(self.view_tag);
        buf.extend_from_slice(&self.masked_amount);
        buf.extend_from_slice(&self.encrypted_memo);
    }
}

pub struct Tx {
    pub version: u8,
    pub nullifiers: Vec<[u8; NULLIFIER_BYTES]>,
    pub outputs: Vec<Output>,
    pub fee: u64,
    pub set_digest: [u8; SET_DIGEST_BYTES],
    pub valid_from: u32,
    pub valid_until: u32,
    pub proof: Vec<u8>,
}

impl Tx {
    pub fn metadata(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.metadata_len());
        buf.push(self.version);
        buf.extend_from_slice(&(self.nullifiers.len() as u32).to_le_bytes());
        for n in &self.nullifiers {
            buf.extend_from_slice(n);
        }
        buf.extend_from_slice(&(self.outputs.len() as u32).to_le_bytes());
        for o in &self.outputs {
            o.write(&mut buf);
        }
        buf.extend_from_slice(&self.fee.to_le_bytes());
        buf.extend_from_slice(&self.set_digest);
        buf.extend_from_slice(&self.valid_from.to_le_bytes());
        buf.extend_from_slice(&self.valid_until.to_le_bytes());
        buf
    }

    pub fn metadata_len(&self) -> usize {
        1 + 4 + self.nullifiers.len() * NULLIFIER_BYTES + 4 + self.outputs.len() * Output::SERIALIZED_LEN + 8
            + SET_DIGEST_BYTES + 4 + 4
    }

    pub fn serialize(&self) -> Vec<u8> {
        let mut buf = self.metadata();
        buf.extend_from_slice(&(self.proof.len() as u32).to_le_bytes());
        buf.extend_from_slice(&self.proof);
        buf
    }

    pub fn parse(b: &[u8]) -> Option<(Tx, usize)> {
        let mut o = 0usize;
        let mut take = |len: usize| -> Option<&[u8]> {
            let s = b.get(o..o + len)?;
            o += len;
            Some(s)
        };
        let u32_at = |s: &[u8]| u32::from_le_bytes(s.try_into().unwrap());
        let version = take(1)?[0];
        let nn = u32_at(take(4)?) as usize;
        if nn > 64 {
            return None;
        }
        let nullifiers = (0..nn).map(|_| take(NULLIFIER_BYTES).map(|s| s.try_into().unwrap())).collect::<Option<Vec<_>>>()?;
        let no = u32_at(take(4)?) as usize;
        if no > 64 {
            return None;
        }
        let outputs = (0..no).map(|_| take(Output::SERIALIZED_LEN).map(Output::read)).collect::<Option<Vec<_>>>()?;
        let fee = u64::from_le_bytes(take(8)?.try_into().unwrap());
        let set_digest = take(SET_DIGEST_BYTES)?.try_into().unwrap();
        let valid_from = u32_at(take(4)?);
        let valid_until = u32_at(take(4)?);
        let plen = u32_at(take(4)?) as usize;
        let proof = take(plen)?.to_vec();
        Some((Tx { version, nullifiers, outputs, fee, set_digest, valid_from, valid_until, proof }, o))
    }

    pub fn txid(&self) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(self.serialize());
        h.finalize().into()
    }
}

pub const HEADER_LEN: usize = 4 + 8 + 32 + 32 + SET_DIGEST_BYTES + 8 + 8 + 8;
pub const MAX_BLOCK: usize = 2 * 1024 * 1024;

#[derive(Clone)]
pub struct Public {
    pub nullifiers: Vec<[u8; NULLIFIER_BYTES]>,
    pub commitments: Vec<[u8; OUT_COMMITMENT_BYTES]>,
    pub amounts: Vec<u64>,
    pub fee: u64,
    pub set_digest: [u8; SET_DIGEST_BYTES],
}

impl Public {
    pub fn bytes(n: usize) -> usize {
        n * (NULLIFIER_BYTES + OUT_COMMITMENT_BYTES + 8) + 8 + SET_DIGEST_BYTES
    }

    pub fn parse(n: usize, b: &[u8]) -> Public {
        assert_eq!(b.len(), Self::bytes(n));
        let mut o = 0;
        let mut take = |len: usize| {
            let s = &b[o..o + len];
            o += len;
            s
        };
        let nullifiers = (0..n).map(|_| take(NULLIFIER_BYTES).try_into().unwrap()).collect();
        let commitments = (0..n).map(|_| take(OUT_COMMITMENT_BYTES).try_into().unwrap()).collect();
        let amounts = (0..n).map(|_| u64::from_le_bytes(take(8).try_into().unwrap())).collect();
        let fee = u64::from_le_bytes(take(8).try_into().unwrap());
        let set_digest = take(SET_DIGEST_BYTES).try_into().unwrap();
        Public { nullifiers, commitments, amounts, fee, set_digest }
    }
}

pub struct Note {
    pub ciphertext: [u8; OUT_CIPHERTEXT_BYTES],
    pub secret: [u8; 32],
}

impl Note {
    pub fn to(ek: &EncapsulationKey<MlKem768>, m: [u8; 32]) -> Note {
        let (ct, ss) = ek.encapsulate_deterministic(&Array::from(m));
        Note { ciphertext: ct.as_slice().try_into().unwrap(), secret: ss.as_slice().try_into().unwrap() }
    }

    pub fn open(dk: &DecapsulationKey<MlKem768>, ciphertext: &[u8; OUT_CIPHERTEXT_BYTES]) -> Note {
        let ss = dk.decapsulate(&Array::try_from(ciphertext.as_slice()).unwrap());
        Note { ciphertext: *ciphertext, secret: ss.as_slice().try_into().unwrap() }
    }

    pub fn view_tag(&self) -> u8 {
        Sha3_512::new().chain_update(b"blocknet_vtag").chain_update(self.secret).finalize()[0]
    }

    pub fn coin_seed(&self) -> [u8; 16] {
        Sha3_256::new().chain_update(b"blocknet_coin").chain_update(self.secret).finalize()[..16].try_into().unwrap()
    }

    fn mask(&self, label: &[u8], i: u8) -> [u8; 64] {
        Sha3_512::new().chain_update(label).chain_update(self.secret).chain_update([i]).finalize().into()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Scan {
    Skip,
    TagOnly,
    Mine(u64),
}

pub fn scan(dk: &DecapsulationKey<MlKem768>, owner_key: &[u8; 32], o: &Output) -> Scan {
    let note = Note::open(dk, &o.ciphertext);
    if note.view_tag() != o.view_tag {
        return Scan::Skip;
    }
    let amask = note.mask(b"blocknet_amount", 0);
    let amount = u64::from_le_bytes(core::array::from_fn(|i| o.masked_amount[i] ^ amask[i]));
    if crate::coin_matches(&note.coin_seed(), owner_key, amount, &o.commitment) {
        Scan::Mine(amount)
    } else {
        Scan::TagOnly
    }
}

pub fn build_tx(public: &Public, proof: Vec<u8>, notes: &[Note]) -> Tx {
    let outputs = public
        .commitments
        .iter()
        .zip(&public.amounts)
        .zip(notes)
        .map(|((c, &amount), note)| Output::seal(note, *c, amount, b""))
        .collect();
    Tx {
        version: 3,
        nullifiers: public.nullifiers.clone(),
        outputs,
        fee: public.fee,
        set_digest: public.set_digest,
        valid_from: 0,
        valid_until: u32::MAX,
        proof,
    }
}

fn fill<const N: usize>(seed: u8) -> [u8; N] {
    core::array::from_fn(|i| seed.wrapping_add(i as u8))
}

pub fn demo_tx(n: usize, proof_len: usize) -> Tx {
    Tx {
        version: 3,
        nullifiers: (0..n).map(|i| fill(i as u8)).collect(),
        outputs: (0..n)
            .map(|i| {
                let s = 0x40 + i as u8;
                Output {
                    commitment: fill(s),
                    ciphertext: fill(s.wrapping_add(1)),
                    view_tag: s,
                    masked_amount: fill(s.wrapping_add(2)),
                    encrypted_memo: fill(s.wrapping_add(3)),
                }
            })
            .collect(),
        fee: 10_000,
        set_digest: fill(0xAA),
        valid_from: 999_990,
        valid_until: 1_000_020,
        proof: vec![0u8; proof_len],
    }
}

pub struct WireRow {
    pub n: usize,
    pub metadata: usize,
    pub relay: usize,
    pub per_block: usize,
    pub per_block_pruned: usize,
}

pub fn measure(n: usize, proof_len: usize) -> WireRow {
    row(&demo_tx(n, proof_len))
}

pub fn row(tx: &Tx) -> WireRow {
    let n = tx.nullifiers.len();
    let relay = tx.serialize().len();
    let metadata = tx.metadata().len();
    let _ = tx.txid();
    let room = MAX_BLOCK - HEADER_LEN - 4;
    WireRow {
        n,
        metadata,
        relay,
        per_block: room / (4 + relay),
        per_block_pruned: room / (4 + metadata),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ml_kem::Seed;

    #[test]
    fn real_send_serializes_parses_and_only_the_recipient_finds_it() {
        let prep = crate::prepare_seeded(&[3u8; 32], 4, None);
        let me = DecapsulationKey::<MlKem768>::from_seed(Seed::from([5u8; 64]));
        let other = DecapsulationKey::<MlKem768>::from_seed(Seed::from([6u8; 64]));
        let (my_pk, other_pk) = (crate::owner_key(b"me"), crate::owner_key(b"other"));
        let notes = [Note::to(me.encapsulation_key(), [1u8; 32]), Note::to(other.encapsulation_key(), [2u8; 32])];
        let seeds = [notes[0].coin_seed(), notes[1].coin_seed()];
        let sent = crate::send(&prep, 2, 42, 0, &[my_pk, other_pk], &seeds, || std::time::Duration::ZERO);
        let tx = build_tx(&sent.public, sent.proof.clone(), &notes);
        let bytes = tx.serialize();
        let (back, used) = Tx::parse(&bytes).unwrap();
        assert_eq!(used, bytes.len());
        assert_eq!(back.serialize(), bytes);
        assert!(crate::verify_tx(&prep, &back));
        let mut bad = Tx::parse(&bytes).unwrap().0;
        bad.fee += 1;
        assert!(!crate::verify_tx(&prep, &bad));
        assert_eq!(scan(&me, &my_pk, &back.outputs[0]), Scan::Mine(sent.public.amounts[0]));
        assert_ne!(scan(&me, &my_pk, &back.outputs[1]), Scan::Mine(sent.public.amounts[1]));
        assert_eq!(scan(&other, &other_pk, &back.outputs[1]), Scan::Mine(sent.public.amounts[1]));
        assert_eq!(sent.public.amounts.iter().sum::<u64>() + sent.public.fee, 2 * 5_000_000);
    }
}
