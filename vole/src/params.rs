pub const KEM_CIPHERTEXT_BYTES: usize = 1088;

pub const OUT_COMMITMENT_BYTES: usize = 80;
pub const OUT_CIPHERTEXT_BYTES: usize = KEM_CIPHERTEXT_BYTES;
pub const OUT_VIEW_TAG_BYTES: usize = 1;
pub const OUT_AMOUNT_BYTES: usize = 8;
pub const OUT_MEMO_BYTES: usize = 128;
pub const OUT_TOTAL_BYTES: usize =
    OUT_COMMITMENT_BYTES + OUT_CIPHERTEXT_BYTES + OUT_VIEW_TAG_BYTES + OUT_AMOUNT_BYTES + OUT_MEMO_BYTES;

pub const NULLIFIER_BYTES: usize = 16;
pub const SET_DIGEST_BYTES: usize = 32;
pub const SET_LOG2: u32 = 20;

pub const SECURITY: &str = "128-bit (FAEST v2 AES-128, NIST category 1)";

const _: () = assert!(OUT_TOTAL_BYTES == 1305);
