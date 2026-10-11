pub const TREE_DEPTH: usize = 32;

pub const HASH_TRUNC_BYTES: usize = 32;

pub const KEM_PUBKEY_BYTES: usize = 1184;
pub const KEM_SECKEY_BYTES: usize = 2400;
pub const KEM_CIPHERTEXT_BYTES: usize = 1088;
pub const KEM_SHARED_SECRET_BYTES: usize = 32;

pub const DIGEST_BYTES: usize = 64;

pub const OUT_COMMITMENT_BYTES: usize = DIGEST_BYTES;
pub const OUT_CIPHERTEXT_BYTES: usize = KEM_CIPHERTEXT_BYTES;
pub const OUT_VIEW_TAG_BYTES: usize = 1;
pub const OUT_AMOUNT_BYTES: usize = 8;
pub const OUT_MEMO_BYTES: usize = 128;
pub const OUT_TOTAL_BYTES: usize =
    OUT_COMMITMENT_BYTES + OUT_CIPHERTEXT_BYTES + OUT_VIEW_TAG_BYTES + OUT_AMOUNT_BYTES + OUT_MEMO_BYTES;

const _: () = assert!(OUT_TOTAL_BYTES == 1289);

pub const TX_VERSION_PQ: u8 = 2;
pub const TX_HEIGHT_BITS: u32 = 28;

pub const AMOUNT_BITS: usize = 64;

pub mod domain {
    pub const SPEND_KEY: &[u8] = b"blocknet_spend_key";
    pub const PUBKEY: &[u8] = b"blocknet_pubkey";
    pub const KEM_SEED: &[u8] = b"blocknet_kem_seed";
    pub const IMAGE: &[u8] = b"blocknet_image";
    pub const COMMIT: &[u8] = b"blocknet_commit";

    pub const ONETIME: &[u8] = b"blocknet_onetime";
    pub const BLIND: &[u8] = b"blocknet_blind";
    pub const ENC: &[u8] = b"blocknet_enc";
    pub const NONCE: &[u8] = b"blocknet_nonce";
    pub const VTAG: &[u8] = b"blocknet_vtag";

    pub const AMOUNT: &[u8] = b"blocknet_amount";
    pub const MEMO: &[u8] = b"blocknet_memo";
    pub const TX_MSG: &[u8] = b"blocknet_tx_msg";
    pub const BLIND_ELEMS: &[u8] = b"blocknet_blind_elems";
    pub const ONETIME_ELEMS: &[u8] = b"blocknet_onetime_elems";

    pub const PQ_ROOT: &[u8] = b"blocknet_pqc_root";
    pub const PQ_KEM: &[u8] = b"blocknet_pqc_kem";
    pub const PQ_SPEND: &[u8] = b"blocknet_pqc_spend";
}
