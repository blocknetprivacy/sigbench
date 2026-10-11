use std::io::Write;

use sha3::{Digest, Sha3_256};

pub const COMMIT_LEN: usize = 64;
pub const KEYIMAGE_LEN: usize = 64;
pub const ROOT_LEN: usize = 64;
pub const KYBER_CT_LEN: usize = pqc_poc::params::OUT_CIPHERTEXT_BYTES;
pub const AMOUNT_LEN: usize = pqc_poc::params::OUT_AMOUNT_BYTES;
pub const MEMO_LEN: usize = 128;

pub struct PqcOutput {
    pub commitment: [u8; COMMIT_LEN],
    pub ciphertext: [u8; KYBER_CT_LEN],
    pub view_tag: u8,
    pub masked_amount: [u8; AMOUNT_LEN],
    pub encrypted_memo: [u8; MEMO_LEN],
}

impl PqcOutput {
    pub const SERIALIZED_LEN: usize =
        COMMIT_LEN + KYBER_CT_LEN + 1 + AMOUNT_LEN + MEMO_LEN;

    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.commitment);
        buf.extend_from_slice(&self.ciphertext);
        buf.push(self.view_tag);
        buf.extend_from_slice(&self.masked_amount);
        buf.extend_from_slice(&self.encrypted_memo);
    }
}

pub struct PqcInput {
    pub key_image: [u8; KEYIMAGE_LEN],
}

pub struct PqcTx {
    pub version: u8,
    pub inputs: Vec<PqcInput>,
    pub outputs: Vec<PqcOutput>,
    pub fee: u64,
    pub tree_root: [u8; ROOT_LEN],
    pub valid_from: u32,
    pub valid_until: u32,
}

impl PqcTx {
    pub fn serialize(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.on_chain_len());
        buf.push(self.version);
        buf.extend_from_slice(&(self.inputs.len() as u32).to_le_bytes());
        for i in &self.inputs {
            buf.extend_from_slice(&i.key_image);
        }
        buf.extend_from_slice(&(self.outputs.len() as u32).to_le_bytes());
        for o in &self.outputs {
            o.write(&mut buf);
        }
        buf.extend_from_slice(&self.fee.to_le_bytes());
        buf.extend_from_slice(&self.tree_root);
        buf.extend_from_slice(&self.valid_from.to_le_bytes());
        buf.extend_from_slice(&self.valid_until.to_le_bytes());
        buf
    }

    pub fn txid(&self) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(self.serialize());
        h.finalize().into()
    }

    pub fn on_chain_len(&self) -> usize {
        1 + 4
            + self.inputs.len() * KEYIMAGE_LEN
            + 4
            + self.outputs.len() * PqcOutput::SERIALIZED_LEN
            + 8
            + ROOT_LEN
            + 4
            + 4
    }

    pub fn serialize_relay(&self, proof: &[u8]) -> Vec<u8> {
        let mut buf = self.serialize();
        buf.extend_from_slice(&(proof.len() as u32).to_le_bytes());
        buf.extend_from_slice(proof);
        buf
    }
}

pub struct PqcBlockHeader {
    pub version: u32,
    pub height: u64,
    pub prev_hash: [u8; 32],
    pub merkle_root: [u8; 32],
    pub tree_root: [u8; ROOT_LEN],
    pub timestamp: i64,
    pub difficulty: u64,
    pub nonce: u64,
}

impl PqcBlockHeader {
    pub const SERIALIZED_LEN: usize = 4 + 8 + 32 + 32 + ROOT_LEN + 8 + 8 + 8;

    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.version.to_le_bytes());
        buf.extend_from_slice(&self.height.to_le_bytes());
        buf.extend_from_slice(&self.prev_hash);
        buf.extend_from_slice(&self.merkle_root);
        buf.extend_from_slice(&self.tree_root);
        buf.extend_from_slice(&self.timestamp.to_le_bytes());
        buf.extend_from_slice(&self.difficulty.to_le_bytes());
        buf.extend_from_slice(&self.nonce.to_le_bytes());
    }
}

pub struct PqcBlock {
    pub header: PqcBlockHeader,
    pub folded_proof: Vec<u8>,
    pub txs: Vec<PqcTx>,
}

impl PqcBlock {
    pub fn serialize(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_len());
        self.header.write(&mut buf);
        buf.extend_from_slice(&(self.folded_proof.len() as u32).to_le_bytes());
        buf.extend_from_slice(&self.folded_proof);
        buf.extend_from_slice(&(self.txs.len() as u32).to_le_bytes());
        for tx in &self.txs {
            let m = tx.serialize();
            buf.extend_from_slice(&(m.len() as u32).to_le_bytes());
            let _ = buf.write_all(&m);
        }
        buf
    }

    pub fn serialized_len(&self) -> usize {
        PqcBlockHeader::SERIALIZED_LEN
            + 4
            + self.folded_proof.len()
            + 4
            + self.txs.iter().map(|t| 4 + t.on_chain_len()).sum::<usize>()
    }

    pub fn hash(&self) -> [u8; 32] {
        let mut buf = Vec::new();
        self.header.write(&mut buf);
        let mut h = Sha3_256::new();
        h.update(buf);
        h.finalize().into()
    }
}

fn fill<const N: usize>(seed: u8) -> [u8; N] {
    core::array::from_fn(|i| seed.wrapping_add(i as u8))
}

pub fn demo_output(seed: u8) -> PqcOutput {
    PqcOutput {
        commitment: fill(seed),
        ciphertext: fill(seed.wrapping_add(1)),
        view_tag: seed,
        masked_amount: fill(seed.wrapping_add(2)),
        encrypted_memo: fill(seed.wrapping_add(3)),
    }
}

pub fn demo_tx(n_in: usize, n_out: usize) -> PqcTx {
    PqcTx {
        version: 2,
        inputs: (0..n_in)
            .map(|i| PqcInput { key_image: fill(i as u8) })
            .collect(),
        outputs: (0..n_out).map(|i| demo_output(0x40 + i as u8)).collect(),
        fee: 10_000,
        tree_root: fill(0xAA),
        valid_from: 999_990,
        valid_until: 1_000_020,
    }
}

const MAX_BLOCK: usize = 2 * 1024 * 1024;

pub fn measure(per_tx_proof_len: usize, folded_bytes: usize) -> (usize, usize, usize, usize) {
    let tx = demo_tx(2, 2);
    let meta = tx.on_chain_len();
    let relay = tx.serialize_relay(&vec![0u8; per_tx_proof_len]).len();

    let n = (MAX_BLOCK - PqcBlockHeader::SERIALIZED_LEN - 4 - folded_bytes - 4) / (4 + meta);
    let block = demo_block(n, vec![0u8; folded_bytes]);
    let block_bytes = block.serialize().len();
    let _ = (tx.txid(), block.hash());
    (meta, relay, n, block_bytes)
}

pub fn demo_block(n_tx: usize, folded_proof: Vec<u8>) -> PqcBlock {
    PqcBlock {
        header: PqcBlockHeader {
            version: 1,
            height: 1_000_000,
            prev_hash: fill(0x11),
            merkle_root: fill(0x22),
            tree_root: fill(0x33),
            timestamp: 1_800_000_000,
            difficulty: 1 << 40,
            nonce: 0xDEADBEEF,
        },
        folded_proof,
        txs: (0..n_tx).map(|_| demo_tx(2, 2)).collect(),
    }
}
