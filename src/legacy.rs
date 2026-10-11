use blocknet_crypto as bc;

pub const RING_SIZE: usize = 16;
pub const SIG_LEN: usize = 96 + 64 * RING_SIZE;

pub struct Witness {
    ring_keys: [u8; RING_SIZE * 32],
    ring_commitments: [u8; RING_SIZE * 32],
    secret_index: usize,
    private_key: [u8; 32],
    input_blinding: [u8; 32],
    pseudo_output: [u8; 32],
    pseudo_blinding: [u8; 32],
    message: [u8; 32],
}

fn keygen() -> ([u8; 32], [u8; 32]) {
    let mut buf = [0u8; 64];
    let rc = bc::blocknet_ristretto_keygen(buf.as_mut_ptr());
    assert_eq!(rc, 0, "blocknet_ristretto_keygen failed (rc={rc})");
    let mut sk = [0u8; 32];
    let mut pk = [0u8; 32];
    sk.copy_from_slice(&buf[0..32]);
    pk.copy_from_slice(&buf[32..64]);
    (sk, pk)
}

fn commit(value: u64) -> ([u8; 32], [u8; 32]) {
    let mut blinding = [0u8; 32];
    let mut commitment = [0u8; 32];
    let rc = bc::blocknet_pedersen_commit(value, blinding.as_mut_ptr(), commitment.as_mut_ptr());
    assert_eq!(rc, 0, "blocknet_pedersen_commit failed (rc={rc})");
    (blinding, commitment)
}

pub fn make_witness(amount: u64, secret_index: usize) -> Witness {
    assert!(secret_index < RING_SIZE);
    let (sk, pk) = keygen();
    let (b_in, c_in) = commit(amount);
    let (b_pseudo, c_pseudo) = commit(amount);

    let mut ring_keys = [0u8; RING_SIZE * 32];
    let mut ring_commitments = [0u8; RING_SIZE * 32];
    for i in 0..RING_SIZE {
        let (k, c) = if i == secret_index {
            (pk, c_in)
        } else {
            let (_dsk, dpk) = keygen();
            let (_db, dc) = commit(1_000 + i as u64);
            (dpk, dc)
        };
        ring_keys[i * 32..i * 32 + 32].copy_from_slice(&k);
        ring_commitments[i * 32..i * 32 + 32].copy_from_slice(&c);
    }

    let (message, _) = keygen();

    Witness {
        ring_keys,
        ring_commitments,
        secret_index,
        private_key: sk,
        input_blinding: b_in,
        pseudo_output: c_pseudo,
        pseudo_blinding: b_pseudo,
        message,
    }
}

pub fn sign(w: &Witness) -> Vec<u8> {
    let mut sig = vec![0u8; SIG_LEN];
    let mut sig_len: usize = 0;
    let rc = bc::blocknet_ringct_sign(
        w.ring_keys.as_ptr(),
        w.ring_commitments.as_ptr(),
        RING_SIZE,
        w.secret_index,
        w.private_key.as_ptr(),
        w.input_blinding.as_ptr(),
        w.pseudo_output.as_ptr(),
        w.pseudo_blinding.as_ptr(),
        w.message.as_ptr(),
        w.message.len(),
        sig.as_mut_ptr(),
        &mut sig_len as *mut usize,
    );
    assert_eq!(rc, 0, "blocknet_ringct_sign failed (rc={rc})");
    sig.truncate(sig_len);
    sig
}

pub fn verify(w: &Witness, sig: &[u8]) -> bool {
    let rc = bc::blocknet_ringct_verify(
        w.ring_keys.as_ptr(),
        w.ring_commitments.as_ptr(),
        RING_SIZE,
        w.message.as_ptr(),
        w.message.len(),
        sig.as_ptr(),
        sig.len(),
    );
    rc == 0
}
