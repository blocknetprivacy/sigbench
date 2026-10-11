use crate::faraday_fold::rec::{FriShape, QUERY_POW_BITS};
use crate::faraday_fold::{
    compress, dom16, fold_native, oracle_commit_cond, oracle_image3, oracle_onetime, oracle_pubkey, v_block, Val,
    CARRY_BITS, CARRY_OFF, DEPTH, DIGEST, LIMB_BITS, NLIMBS,
};
use p3_batch_stark::ProverData;
use p3_circuit::ops::{generate_poseidon2_trace, generate_recompose_trace, Poseidon2Config, Poseidon2PermCall};
use p3_circuit::{CircuitBuilder, CircuitRunner, ExprId, NonPrimitiveOpId, StatementExport, StatementField, StatementSchema};
use p3_circuit_prover::batch_stark_prover::{
    poseidon2_air_builders_d5, poseidon2_table_provers_d5, recompose_air_builders, BatchStarkProof,
    TableProver,
};
use p3_circuit_prover::common::{get_airs_and_degrees_with_prep, CircuitTableAir, NpoPreprocessor};
use p3_circuit_prover::{
    BatchStarkProver, CircuitProverData, ConstraintProfile, Poseidon2Preprocessor, RecomposePreprocessor,
    TablePacking,
};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_koala_bear::{default_koalabear_poseidon2_16, default_koalabear_poseidon2_32};
use p3_lookup::logup::LogUpGadget;
use p3_poseidon2_circuit_air::{KoalaBearD1Width16, KoalaBearD1Width32};
use p3_recursion::pcs::fri::{FriVerifierParams, InputProofTargets, MerkleCapTargets};
use p3_recursion::pcs::{restore_fri_query_paths, set_fri_mmcs_private_data};
use p3_recursion::prepared::ConstrainConstantCommitment;
use p3_recursion::verifier::{verify_p3_batch_proof_circuit, verify_trusted_p3_batch_proof_circuit};
use p3_recursion::{observe_opened_values, replay_batch_layer_transcript, OpeningTranscript};
use p3_symmetric::Permutation;
use std::time::Instant;

pub mod rec5 {
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_dft::Radix2DitParallel;
    use p3_field::extension::QuinticTrinomialExtensionField;
    use p3_field::Field;
    use p3_fri::{FriParameters, TwoAdicFriPcs};
    use p3_koala_bear::{default_koalabear_poseidon2_16, KoalaBear, Poseidon2KoalaBear};
    use p3_merkle_tree::MerkleTreeMmcs;
    use p3_recursion::pcs::{FriProofTargets, InputProofTargets, RecExtensionValMmcs, RecValMmcs, Witness};
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::StarkConfig;

    pub use crate::faraday_fold::rec::FriShape;

    pub const D: usize = 5;
    pub type F = KoalaBear;
    pub type Challenge = QuinticTrinomialExtensionField<F>;
    pub const WIDTH: usize = 16;
    pub const RATE: usize = 8;
    pub const DIGEST_ELEMS: usize = 8;
    pub type Dft = Radix2DitParallel<F>;
    pub type Perm = Poseidon2KoalaBear<WIDTH>;
    pub type MyHash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_ELEMS>;
    pub type MyCompress = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, WIDTH>;
    pub type MyMmcs =
        MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, MyHash, MyCompress, 2, DIGEST_ELEMS>;
    pub type ChallengeMmcs = ExtensionMmcs<F, Challenge, MyMmcs>;
    pub type Challenger = DuplexChallenger<F, Perm, WIDTH, RATE>;
    pub type MyPcs = TwoAdicFriPcs<F, Dft, MyMmcs, ChallengeMmcs>;
    pub type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

    pub const SALT_ELEMS: usize = 4;
    pub type Rng = chacha20::ChaCha20Rng;
    pub type HidingValMmcs = p3_merkle_tree::MerkleTreeHidingMmcs<
        <F as Field>::Packing,
        <F as Field>::Packing,
        MyHash,
        MyCompress,
        Rng,
        2,
        DIGEST_ELEMS,
        SALT_ELEMS,
    >;
    pub type HidingChallengeMmcs = ExtensionMmcs<F, Challenge, HidingValMmcs>;
    pub type ZkPcs = p3_fri::HidingFriPcs<F, Dft, HidingValMmcs, HidingChallengeMmcs, Rng>;
    pub type ZkConfig = StarkConfig<ZkPcs, Challenge, Challenger>;
    pub type RecHidingValMmcs =
        p3_recursion::pcs::RecValHidingMmcs<F, DIGEST_ELEMS, SALT_ELEMS, MyHash, MyCompress, Rng>;
    pub type InnerFri = FriProofTargets<
        F,
        Challenge,
        RecExtensionValMmcs<F, Challenge, DIGEST_ELEMS, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
        InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
        Witness<F>,
    >;
    pub type InnerFriZk = p3_recursion::pcs::HidingFriProofTargets<
        F,
        Challenge,
        RecExtensionValMmcs<F, Challenge, DIGEST_ELEMS, RecHidingValMmcs>,
        InputProofTargets<F, Challenge, RecHidingValMmcs>,
        Witness<F>,
    >;

    #[cfg(test)]
    thread_local! {
        pub static UNGATED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    }

    pub fn fri_instance(shape: FriShape) -> (MyMmcs, FriParameters<ChallengeMmcs>) {
        #[cfg(test)]
        let gated = !UNGATED.with(|u| u.get());
        #[cfg(not(test))]
        let gated = true;
        if gated {
            crate::fri_profile::assert_funds_shape(shape, super::QUERY_POW_BITS);
        }
        let perm = default_koalabear_poseidon2_16();
        let val_mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);
        let fri_params = FriParameters {
            max_log_arity: shape.max_log_arity,
            log_blowup: shape.log_blowup,
            log_final_poly_len: 0,
            num_queries: shape.num_queries,
            batch_proof_of_work_bits: 0,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: super::QUERY_POW_BITS,
            mmcs: ChallengeMmcs::new(val_mmcs.clone()),
        };
        (val_mmcs, fri_params)
    }

    pub fn fold_config(shape: FriShape) -> MyConfig {
        let (val_mmcs, fri_params) = fri_instance(shape);
        MyConfig::new(MyPcs::new(Dft::default(), val_mmcs, fri_params), Challenger::new(default_koalabear_poseidon2_16()))
    }

    pub fn zk_fri_instance_with(shape: FriShape, salts: Rng) -> (HidingValMmcs, FriParameters<HidingChallengeMmcs>) {
        let perm = default_koalabear_poseidon2_16();
        let val_mmcs = HidingValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0, salts);
        let (_, plain) = fri_instance(shape);
        let fri_params = FriParameters {
            max_log_arity: plain.max_log_arity,
            log_blowup: plain.log_blowup,
            log_final_poly_len: plain.log_final_poly_len,
            num_queries: plain.num_queries,
            batch_proof_of_work_bits: plain.batch_proof_of_work_bits,
            commit_proof_of_work_bits: plain.commit_proof_of_work_bits,
            query_proof_of_work_bits: plain.query_proof_of_work_bits,
            mmcs: HidingChallengeMmcs::new(val_mmcs.clone()),
        };
        (val_mmcs, fri_params)
    }

    fn zk_config_with(shape: FriShape, salts: Rng, masks: Rng) -> ZkConfig {
        let (val_mmcs, fri_params) = zk_fri_instance_with(shape, salts);
        let pcs = ZkPcs::new(Dft::default(), val_mmcs, fri_params, D, masks);
        ZkConfig::new(pcs, Challenger::new(default_koalabear_poseidon2_16()))
    }

    pub fn make_zk_config(shape: FriShape) -> ZkConfig {
        zk_config_with(shape, rand::make_rng::<Rng>(), rand::make_rng::<Rng>())
    }

    pub fn keygen_zk_config(shape: FriShape) -> ZkConfig {
        use rand::SeedableRng;
        use sha3::{Digest, Sha3_256};
        let seed = |label: &[u8]| -> [u8; 32] {
            let mut h = Sha3_256::new();
            h.update(b"blocknet faraday spend vk v1 koalabear5");
            for v in [shape.log_blowup, shape.max_log_arity, shape.num_queries] {
                h.update((v as u64).to_le_bytes());
            }
            h.update(label);
            h.finalize().into()
        };
        zk_config_with(shape, Rng::from_seed(seed(b"mmcs")), Rng::from_seed(seed(b"pcs")))
    }
}

use rec5::{Challenge, F};

#[derive(Clone)]
struct Lift<P>(P);

impl<P: Permutation<[F; W]>, const W: usize> Permutation<[Challenge; W]> for Lift<P> {
    fn permute(&self, input: [Challenge; W]) -> [Challenge; W] {
        let base: [F; W] = core::array::from_fn(|i| input[i].as_basis_coefficients_slice()[0]);
        let out = self.0.permute(base);
        core::array::from_fn(|i| Challenge::from(out[i]))
    }
}

type Block = [ExprId; DIGEST];

struct Io {
    priv_vals: Vec<Challenge>,
    pub_vals: Vec<Challenge>,
    #[cfg_attr(not(test), allow(dead_code))]
    marks: Vec<(&'static str, bool, usize)>,
    #[cfg_attr(not(test), allow(dead_code))]
    exprs: Vec<(&'static str, ExprId)>,
    pub_exprs: Vec<ExprId>,
    schema: Option<p3_circuit::StatementSchema>,
}

impl Io {
    fn mark(&mut self, label: &'static str, exprs: &[ExprId]) {
        self.exprs.extend(exprs.iter().map(|&e| (label, e)));
    }
    fn priv_block(&mut self, b: &mut CircuitBuilder<Challenge>, vals: &[Val; DIGEST], label: &'static str) -> Block {
        self.marks.push((label, false, self.priv_vals.len()));
        let out: Block = core::array::from_fn(|i| {
            self.priv_vals.push(Challenge::from(vals[i]));
            b.alloc_private_input(label)
        });
        self.mark(label, &out);
        out
    }
    fn priv_scalar(&mut self, b: &mut CircuitBuilder<Challenge>, v: Challenge, label: &'static str) -> ExprId {
        self.marks.push((label, false, self.priv_vals.len()));
        self.priv_vals.push(v);
        let e = b.alloc_private_input(label);
        self.mark(label, &[e]);
        e
    }
    fn pub_block(&mut self, b: &mut CircuitBuilder<Challenge>, vals: &[Val; DIGEST], label: &'static str) -> Block {
        self.marks.push((label, true, self.pub_vals.len()));
        let out: Block = core::array::from_fn(|i| {
            self.pub_vals.push(Challenge::from(vals[i]));
            b.alloc_public_input(label)
        });
        self.pub_exprs.extend(out);
        out
    }
    fn pub_scalar(&mut self, b: &mut CircuitBuilder<Challenge>, v: Challenge, label: &'static str) -> ExprId {
        self.marks.push((label, true, self.pub_vals.len()));
        self.pub_vals.push(v);
        let e = b.alloc_public_input(label);
        self.pub_exprs.push(e);
        e
    }
}

fn const_block(b: &mut CircuitBuilder<Challenge>, vals: &[Val; DIGEST], label: &'static str) -> Block {
    core::array::from_fn(|i| b.alloc_const(Challenge::from(vals[i]), label))
}

fn wire(b: &mut CircuitBuilder<Challenge>, x: ExprId, one: ExprId) -> ExprId {
    let t = b.add(x, one);
    b.sub(t, one)
}

fn wire_block(b: &mut CircuitBuilder<Challenge>, x: &Block, one: ExprId) -> Block {
    core::array::from_fn(|i| wire(b, x[i], one))
}

fn mux(b: &mut CircuitBuilder<Challenge>, bit: ExprId, t: ExprId, s: ExprId) -> ExprId {
    let d = b.sub(t, s);
    b.mul_add(bit, d, s)
}

fn compress5(b: &mut CircuitBuilder<Challenge>, x: Block, y: Block) -> Block {
    let inputs: Vec<Option<ExprId>> = x.iter().chain(y.iter()).map(|&e| Some(e)).collect();
    let rate = Poseidon2Config::KOALA_BEAR_D1_W32.rate_ext();
    let (_op, outputs) = b
        .add_poseidon2_perm(&Poseidon2PermCall {
            config: Poseidon2Config::KOALA_BEAR_D1_W32,
            new_start: true,
            merkle_path: false,
            mmcs_bit: None,
            mmcs_bit2: None,
            inputs,
            out_ctl: vec![true; rate],
            return_all_outputs: true,
            mmcs_index_sum: None,
            absorb_len: 0,
        })
        .expect("D1 W32 compress wiring");
    core::array::from_fn(|i| outputs[i].expect("digest lane present"))
}

fn amount_limb(v: u64, k: usize) -> Challenge {
    Challenge::from_u64((v >> (16 * k)) & 0xffff)
}

fn build_spend_circuit(seed: u64) -> (p3_circuit::Circuit<Challenge>, Io) {
    build_spend_circuit_with(seed, false)
}

fn build_spend_circuit_with(seed: u64, keccak: bool) -> (p3_circuit::Circuit<Challenge>, Io) {
    let perm = default_koalabear_poseidon2_32();
    let base = seed * 1000;
    let s_key: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(base + 100 + i as u64));
    let r_in: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(base + 500 + i as u64));
    let b_in: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(base + 200 + i as u64));
    let v: u64 = 500;
    let s_pub = oracle_pubkey(&perm, &s_key);
    let p_one = oracle_onetime(&perm, &s_pub, &r_in);
    let zero_cond = [Val::ZERO; DIGEST];
    let leaf = oracle_commit_cond(&perm, &p_one, v, &b_in, &zero_cond);
    let siblings: Vec<[Val; DIGEST]> = (0..DEPTH)
        .map(|d| core::array::from_fn(|i| Val::from_u64((1000 + (d * DIGEST + i)) as u64)))
        .collect();
    let bits: Vec<bool> = (0..DEPTH).map(|d| d % 3 == 0 || d % 2 == 1).collect();
    let image = oracle_image3(&perm, &s_key, &r_in, &bits);
    let root = fold_native(&perm, &leaf, &siblings, &bits);
    let kk_out: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(base + 300 + i as u64));
    let b_out: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(base + 400 + i as u64));
    let o: u64 = 500;
    let fee: u64 = 0;
    let cond_out: [Val; DIGEST] = core::array::from_fn(|i| if seed % 2 == 1 { Val::from_u64(base + 600 + i as u64) } else { Val::ZERO });
    let commit_out = oracle_commit_cond(&perm, &kk_out, o, &b_out, &cond_out);
    debug_assert_eq!(compress(&perm, &dom16(b"blocknet_pubkey"), &s_key), s_pub);

    let mut b = CircuitBuilder::<Challenge>::new();
    b.enable_poseidon2_perm_base_width_32::<KoalaBearD1Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD1Width32>,
        Lift(perm.clone()),
    );
    let mut io = Io { priv_vals: Vec::new(), pub_vals: Vec::new(), marks: Vec::new(), exprs: Vec::new(), pub_exprs: Vec::new(), schema: None };
    let one = b.alloc_const(Challenge::ONE, "one");
    if keccak {
        use sha3::{Digest, Keccak256};
        b.enable_keccak_f1600::<F>();
        let t: [u8; 32] = core::array::from_fn(|i| (seed as u8).wrapping_mul(31).wrapping_add(i as u8));
        let h: [u8; 32] = Keccak256::digest(t).into();
        let limbs = |x: &[u8; 32]| p3_circuit::ops::bytes_to_limbs(x);
        let t_in: Vec<ExprId> = limbs(&t)
            .into_iter()
            .map(|l| {
                let e = io.priv_scalar(&mut b, Challenge::from_u16(l), "veil_t");
                wire(&mut b, e, one)
            })
            .collect();
        let digest = b.keccak256_limbs::<F>(&t_in).expect("keccak-256 of t");
        for (d, l) in digest.into_iter().zip(limbs(&h)) {
            let pub_h = io.pub_scalar(&mut b, Challenge::from_u16(l), "veil_h");
            b.connect(d, pub_h);
        }
    }
    let zero = b.alloc_const(Challenge::ZERO, "zero");
    let dom_pk = const_block(&mut b, &dom16(b"blocknet_pubkey"), "dom_pubkey");
    let dom_im = const_block(&mut b, &dom16(b"blocknet_image"), "dom_image");
    let dom_cm = const_block(&mut b, &dom16(b"blocknet_commit"), "dom_commit");
    let dom_ot = const_block(&mut b, &dom16(b"blocknet_onetime"), "dom_onetime");

    let e_s_raw = io.priv_block(&mut b, &s_key, "s");
    let e_s = wire_block(&mut b, &e_s_raw, one);
    io.mark("s", &e_s);
    let e_r_raw = io.priv_block(&mut b, &r_in, "r");
    let e_r = wire_block(&mut b, &e_r_raw, one);
    io.mark("r", &e_r);
    let e_b_in_raw = io.priv_block(&mut b, &b_in, "b_in");
    let e_b_in = wire_block(&mut b, &e_b_in_raw, one);
    io.mark("b_in", &e_b_in);
    let v_limbs: [ExprId; NLIMBS] = core::array::from_fn(|kk| io.priv_scalar(&mut b, amount_limb(v, kk), "v_limb"));
    let v_lanes: Block = {
        let w: [ExprId; NLIMBS] = core::array::from_fn(|kk| wire(&mut b, v_limbs[kk], one));
        debug_assert_eq!(v_block(v)[4], Val::from_u64((v >> 16) & 0xffff));
        core::array::from_fn(|i| if i % 4 == 0 && i / 4 < NLIMBS { w[i / 4] } else { zero })
    };
    let e_spub = compress5(&mut b, dom_pk, e_s);
    let ot1 = compress5(&mut b, dom_ot, e_spub);
    let e_p = compress5(&mut b, ot1, e_r);
    let im1 = compress5(&mut b, dom_im, e_s);
    let im2 = compress5(&mut b, im1, e_r);
    let s1 = compress5(&mut b, dom_cm, e_p);
    let s2 = compress5(&mut b, s1, v_lanes);
    let s3 = compress5(&mut b, s2, e_b_in);
    let cond_zero = const_block(&mut b, &[Val::ZERO; DIGEST], "cond_zero");
    let mut running = compress5(&mut b, s3, cond_zero);
    io.mark("leaf", &running);
    for &e in v_limbs.iter() {
        b.decompose_to_bits::<F>(e, LIMB_BITS).expect("v range");
    }
    let mut pos_bits = Vec::with_capacity(DEPTH);
    for d in 0..DEPTH {
        let sib_raw = io.priv_block(&mut b, &siblings[d], "sib");
        let sib = wire_block(&mut b, &sib_raw, one);
        let bit = io.priv_scalar(&mut b, if bits[d] { Challenge::ONE } else { Challenge::ZERO }, "pos_bit");
        b.assert_bool(bit);
        pos_bits.push(bit);
        let left: Block = core::array::from_fn(|i| mux(&mut b, bit, sib[i], running[i]));
        let right: Block = core::array::from_fn(|i| mux(&mut b, bit, running[i], sib[i]));
        running = compress5(&mut b, left, right);
    }
    let idx_block: Block = {
        let limb = |b: &mut CircuitBuilder<Challenge>, bits: &[ExprId]| {
            let mut acc = zero;
            for (j, &bit) in bits.iter().enumerate() {
                let w = b.alloc_const(Challenge::from_u64(1 << j), "pos_weight");
                acc = b.mul_add(bit, w, acc);
            }
            acc
        };
        let lo = limb(&mut b, &pos_bits[..16]);
        let hi = limb(&mut b, &pos_bits[16..]);
        core::array::from_fn(|i| match i {
            0 => lo,
            1 => hi,
            _ => zero,
        })
    };
    let e_img = compress5(&mut b, im2, idx_block);
    io.mark("key_image", &e_img);
    let pub_image = io.pub_block(&mut b, &image, "key_image");
    let pub_root = io.pub_block(&mut b, &root, "root");
    for i in 0..DIGEST {
        b.connect(e_img[i], pub_image[i]);
        b.connect(running[i], pub_root[i]);
    }

    let e_kk_out_raw = io.priv_block(&mut b, &kk_out, "kk_out");
    let e_kk_out = wire_block(&mut b, &e_kk_out_raw, one);
    io.mark("kk_out", &e_kk_out);
    let e_b_out_raw = io.priv_block(&mut b, &b_out, "b_out");
    let e_b_out = wire_block(&mut b, &e_b_out_raw, one);
    io.mark("b_out", &e_b_out);
    let o_limbs: [ExprId; NLIMBS] = core::array::from_fn(|kk| io.priv_scalar(&mut b, amount_limb(o, kk), "o_limb"));
    let o_lanes: Block = {
        let w: [ExprId; NLIMBS] = core::array::from_fn(|kk| wire(&mut b, o_limbs[kk], one));
        core::array::from_fn(|i| if i % 4 == 0 && i / 4 < NLIMBS { w[i / 4] } else { zero })
    };
    let e_cond_out_raw = io.priv_block(&mut b, &cond_out, "cond_out");
    let e_cond_out = wire_block(&mut b, &e_cond_out_raw, one);
    let os1 = compress5(&mut b, dom_cm, e_kk_out);
    let os2 = compress5(&mut b, os1, o_lanes);
    let os3 = compress5(&mut b, os2, e_b_out);
    let e_commit = compress5(&mut b, os3, e_cond_out);
    io.mark("commit_out", &e_commit);
    for &e in o_limbs.iter() {
        b.decompose_to_bits::<F>(e, LIMB_BITS).expect("o range");
    }
    let pub_commit = io.pub_block(&mut b, &commit_out, "commitment");
    for i in 0..DIGEST {
        b.connect(e_commit[i], pub_commit[i]);
    }

    let fee_e: [ExprId; NLIMBS] = core::array::from_fn(|kk| io.pub_scalar(&mut b, amount_limb(fee, kk), "fee_limb"));
    for &e in fee_e.iter() {
        b.decompose_to_bits::<F>(e, LIMB_BITS).expect("fee range");
    }
    let base_c = b.alloc_const(Challenge::from_u64(1 << LIMB_BITS), "base");
    let off_c = b.alloc_const(Challenge::from_u64(CARRY_OFF), "carry_off");
    let mut carries = Vec::new();
    {
        let mut c = 0i64;
        let lm = |x: u64, kk: usize| ((x >> (16 * kk)) & 0xffff) as i64;
        for kk in 0..NLIMBS {
            let diff = lm(v, kk) - lm(o, kk) - lm(fee, kk) + c;
            if kk + 1 < NLIMBS {
                c = diff / (1i64 << LIMB_BITS);
                carries.push(c);
            }
        }
    }
    let carry_e: Vec<ExprId> = carries
        .iter()
        .map(|&c| {
            let cf = if c >= 0 { Challenge::from_u64(c as u64) } else { -Challenge::from_u64((-c) as u64) };
            io.priv_scalar(&mut b, cf, "carry")
        })
        .collect();
    let mut carry_in: Option<ExprId> = None;
    for kk in 0..NLIMBS {
        let mut diff = b.sub(v_limbs[kk], o_limbs[kk]);
        diff = b.sub(diff, fee_e[kk]);
        if let Some(ci) = carry_in {
            diff = b.add(diff, ci);
        }
        if kk + 1 < NLIMBS {
            let cb = b.mul(carry_e[kk], base_c);
            let residual = b.sub(diff, cb);
            b.assert_zero(residual);
            let off_val = b.add(carry_e[kk], off_c);
            b.decompose_to_bits::<F>(off_val, CARRY_BITS).expect("carry range");
            carry_in = Some(carry_e[kk]);
        } else {
            b.assert_zero(diff);
        }
    }
    let (valid_from, valid_until) = (999_990u64, 1_000_020u64);
    for (v, label) in [(valid_from, "valid_from"), (valid_until, "valid_until")] {
        let e = io.pub_scalar(&mut b, Challenge::from_u64(v), label);
        b.decompose_to_bits::<F>(e, HEIGHT_BITS).expect("height range");
    }
    let msg: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(base + 700 + i as u64));
    io.pub_block(&mut b, &msg, "tx_msg");
    if !keccak {
        let blocks = statement_blocks(&io.pub_exprs, zero);
        let dom_st = const_block(&mut b, &dom16(stmt_domain()), "dom_stmt");
        let digest = blocks.into_iter().fold(dom_st, |acc, blk| compress5(&mut b, acc, blk));
        let exports: Vec<p3_circuit::StatementExport> = digest.iter().map(|&e| p3_circuit::StatementExport::Base(e)).collect();
        io.schema = Some(b.set_statement_exports::<F>(&exports).expect("spend statement"));
    }
    (b.build().expect("D5 spend circuit builds"), io)
}

#[cfg(test)]
thread_local! {
    static FORGED_STMT_DOMAIN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
thread_local! {
    static UNTRUSTED_BUILD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

fn untrusted_build() -> bool {
    #[cfg(test)]
    if UNTRUSTED_BUILD.with(|u| u.get()) {
        return true;
    }
    false
}

fn stmt_domain() -> &'static [u8] {
    #[cfg(test)]
    if FORGED_STMT_DOMAIN.with(|f| f.get()) {
        return b"blocknet_stmX";
    }
    b"blocknet_stmt"
}

fn spend_traces(seed: u64) -> p3_circuit::Traces<Challenge> {
    let (circuit, io) = build_spend_circuit(seed);
    let mut r = circuit.runner();
    r.set_private_inputs(&io.priv_vals).expect("spend private inputs");
    r.set_public_inputs(&io.pub_vals).expect("spend public inputs");
    r.run().expect("D5 spend runs")
}

fn statement_blocks<T: Copy>(values: &[T], zero: T) -> Vec<[T; DIGEST]> {
    assert_eq!(values.len(), 3 * DIGEST + NLIMBS + 2 + DIGEST, "statement layout");
    let block = |at: usize| -> [T; DIGEST] { core::array::from_fn(|i| values[at + i]) };
    let tail = 3 * DIGEST;
    let mixed: [T; DIGEST] = core::array::from_fn(|i| if i < NLIMBS + 2 { values[tail + i] } else { zero });
    vec![block(0), block(DIGEST), block(2 * DIGEST), mixed, block(tail + NLIMBS + 2)]
}

pub fn statement_digest(values: &[F]) -> Vec<F> {
    let perm = default_koalabear_poseidon2_32();
    statement_blocks(values, F::ZERO)
        .iter()
        .fold(dom16(b"blocknet_stmt"), |acc, blk| compress(&perm, &acc, blk))
        .to_vec()
}

const HEIGHT_BITS: usize = 28;

fn spend_schema() -> p3_circuit::StatementSchema {
    static S: std::sync::OnceLock<p3_circuit::StatementSchema> = std::sync::OnceLock::new();
    S.get_or_init(|| build_spend_circuit(0).1.schema.expect("schema")).clone()
}

fn spend_packing(shape: FriShape) -> TablePacking {
    TablePacking::new(4, 4).with_min_trace_height((2 * (rec5::D * 2 + shape.num_queries)).next_power_of_two())
}

fn spend_nps() -> Vec<Box<dyn TableProver<rec5::ZkConfig>>> {
    let mut v = poseidon2_table_provers_d5::<rec5::ZkConfig>(Poseidon2Config::KOALA_BEAR_D1_W32);
    v.push(Box::new(p3_circuit_prover::StatementProver::<5>::new(spend_schema())));
    v
}

fn fold_nps(schema: &StatementSchema) -> Vec<Box<dyn TableProver<rec5::MyConfig>>> {
    let mut v = poseidon2_table_provers_d5::<rec5::MyConfig>(Poseidon2Config::KOALA_BEAR_D1_W16);
    v.push(Box::new(p3_circuit_prover::RecomposeProver::<5>::new(1, true)));
    v.push(Box::new(p3_circuit_prover::StatementProver::<5>::new(schema.clone())));
    v
}

fn fold_schema(depth: usize) -> StatementSchema {
    StatementSchema::try_new(vec![StatementField::Base; DIGEST << depth]).expect("fold schema")
}

macro_rules! verify_canonical {
    ($verifier:expr, $proof:expr, $statement:expr) => {{
        if common_binding(&$proof.stark_common) != common_binding($verifier.common_data()) {
            Err("the proof's stark_common is not the key's common data".to_string())
        } else {
            $verifier.verify($proof, $statement).map_err(|e| format!("{e:?}"))
        }
    }};
}

macro_rules! spend_key {
    ($key:ident, $make:ident, $sc:ty, $keygen:expr, $prove_config:expr) => {
        pub struct $key {
            shape: FriShape,
            cpd: CircuitProverData<$sc>,
            #[allow(dead_code)]
            commitment: Vec<u8>,
            #[allow(dead_code)]
            airs: Vec<CircuitTableAir<$sc, 5>>,
            verifier: p3_circuit_prover::CircuitVerifier<$sc>,
        }

        pub fn $make(shape: FriShape) -> $key {
            let config: $sc = $keygen(shape);
            let (circuit, _io) = build_spend_circuit(0);
            let npo_prep: Vec<Box<dyn NpoPreprocessor<F>>> = vec![
                Box::new(Poseidon2Preprocessor),
                Box::new(p3_circuit_prover::StatementPreprocessor::new(spend_schema())),
            ];
            let mut air_builders = poseidon2_air_builders_d5::<$sc>();
            air_builders.push(Box::new(p3_circuit_prover::StatementAirBuilder::<5>::new(spend_schema())));
            let (airs_degrees, prim, nonprim) = get_airs_and_degrees_with_prep::<$sc, Challenge, 5>(
                &circuit,
                &spend_packing(shape),
                &npo_prep,
                &air_builders,
                ConstraintProfile::Standard,
            )
            .expect("D5 spend airs");
            let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
            let zk = <$sc as p3_uni_stark::StarkGenericConfig>::is_zk(&config);
            let degrees: Vec<usize> = degrees.iter().map(|d| d + zk).collect();
            let pd = ProverData::from_airs_and_degrees(&config, &airs, &degrees).expect("D5 spend prover data");
            let cpd = CircuitProverData::new(pd, prim, nonprim);
            let commitment = preprocessed_commitment(cpd.common_data());
            let mut prep = BatchStarkProver::new($keygen(shape)).with_table_packing(spend_packing(shape));
            prep.register_poseidon2_table::<5>(Poseidon2Config::KOALA_BEAR_D1_W32);
            prep.register_table_prover(Box::new(p3_circuit_prover::StatementProver::<5>::new(spend_schema())));
            let verifier = prep
                .prepare_circuit::<Challenge, 5>(&circuit, &npo_prep, &air_builders, ConstraintProfile::Standard)
                .expect("D5 spend relation")
                .verifier();
            assert_eq!(
                preprocessed_commitment(verifier.common_data()),
                commitment,
                "the trusted relation's commitment differs from the published spend key"
            );
            $key { shape, cpd, commitment, airs, verifier }
        }

        impl $key {
            fn prover(&self) -> BatchStarkProver<$sc> {
                let mut p = BatchStarkProver::new($prove_config(self.shape)).with_table_packing(spend_packing(self.shape));
                p.register_poseidon2_table::<5>(Poseidon2Config::KOALA_BEAR_D1_W32);
                p.register_table_prover(Box::new(p3_circuit_prover::StatementProver::<5>::new(spend_schema())));
                p
            }

            pub fn prove(&self, seed: u64) -> BatchStarkProof<$sc> {
                self.prover().prove_all_tables(&spend_traces(seed), &self.cpd).expect("D5 prove spend")
            }

            #[cfg(test)]
            #[allow(dead_code)]
            fn prove_traces(&self, traces: &p3_circuit::Traces<Challenge>) -> Result<(), String> {
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let proof = self.prover().prove_all_tables(traces, &self.cpd).map_err(|e| format!("prove: {e:?}"))?;
                    let statement = carried_statement(&proof).ok_or("no statement")?;
                    self.verify(&proof, &statement).map_err(|e| format!("verify: {e}"))
                }))
                .map_err(|_| "prover or verifier panicked".to_string())?
            }

            pub fn verify(&self, proof: &BatchStarkProof<$sc>, statement: &[F]) -> Result<(), String> {
                verify_canonical!(self.verifier, proof, statement)
            }
        }
    };
}

spend_key!(SpendKey5, generate_spend_key, rec5::ZkConfig, rec5::keygen_zk_config, rec5::make_zk_config);
spend_key!(PlainSpendKey5, plain_spend_key, rec5::MyConfig, rec5::fold_config, rec5::fold_config);

pub fn spend_statement(seed: u64) -> Vec<F> {
    statement_digest(&spend_public_values(seed))
}

pub fn spend_public_values(seed: u64) -> Vec<F> {
    build_spend_circuit(seed).1.pub_vals.iter().map(|v| v.as_basis_coefficients_slice()[0]).collect()
}

pub fn carried_statement<SC: p3_uni_stark::StarkGenericConfig>(proof: &BatchStarkProof<SC>) -> Option<Vec<p3_uni_stark::Val<SC>>> {
    proof
        .non_primitives
        .iter()
        .find(|e| e.op_type == p3_circuit::NpoTypeId::statement())
        .map(|e| e.public_values.clone())
}

fn plain_spend_nps() -> Vec<Box<dyn TableProver<rec5::MyConfig>>> {
    let mut v = poseidon2_table_provers_d5::<rec5::MyConfig>(Poseidon2Config::KOALA_BEAR_D1_W32);
    v.push(Box::new(p3_circuit_prover::StatementProver::<5>::new(spend_schema())));
    v
}

pub type SpendProof = BatchStarkProof<rec5::ZkConfig>;
pub type FoldProof = BatchStarkProof<rec5::MyConfig>;

fn preprocessed_commitment<SC: p3_uni_stark::StarkGenericConfig>(common: &p3_batch_stark::CommonData<SC>) -> Vec<u8> {
    match common.preprocessed.as_ref() {
        Some(pre) => postcard::to_allocvec(&pre.commitment).expect("serialize commitment"),
        None => Vec::new(),
    }
}

type CommonBinding = Option<(Vec<u8>, Vec<Option<(usize, usize, usize)>>, Vec<usize>)>;

fn common_binding<SC: p3_uni_stark::StarkGenericConfig>(common: &p3_batch_stark::CommonData<SC>) -> CommonBinding {
    common.preprocessed.as_ref().map(|pre| {
        (
            postcard::to_allocvec(&pre.commitment).expect("serialize commitment"),
            pre.instances.iter().map(|m| m.as_ref().map(|m| (m.matrix_index, m.width, m.degree_bits))).collect(),
            pre.matrix_to_instance.clone(),
        )
    })
}

macro_rules! proof_codec5 {
    ($enc:ident, $dec:ident, $sc:ty) => {
        pub fn $enc(p: &BatchStarkProof<$sc>) -> Vec<u8> {
            postcard::to_allocvec(p).expect("serialize proof")
        }

        pub fn $dec(bytes: &[u8]) -> Result<BatchStarkProof<$sc>, String> {
            let proof: BatchStarkProof<$sc> = postcard::from_bytes(bytes).map_err(|e| format!("decode: {e}"))?;
            if $enc(&proof) != bytes {
                return Err("decode: not the canonical encoding".into());
            }
            Ok(proof)
        }
    };
}

proof_codec5!(encode_spend, decode_spend, rec5::ZkConfig);
proof_codec5!(encode_fold, decode_fold, rec5::MyConfig);

pub fn spend_key(shape: FriShape) -> &'static SpendKey5 {
    static KEYS: std::sync::Mutex<Vec<(FriShape, &'static SpendKey5)>> = std::sync::Mutex::new(Vec::new());
    let mut keys = KEYS.lock().expect("spend key cache");
    if let Some((_, k)) = keys.iter().find(|(s, _)| *s == shape) {
        return k;
    }
    let k: &'static SpendKey5 = Box::leak(Box::new(generate_spend_key(shape)));
    keys.push((shape, k));
    k
}

impl SpendKey5 {
    pub fn commitment(&self) -> &[u8] {
        &self.commitment
    }

    pub fn verifier(&self) -> SpendVerifier5 {
        SpendVerifier5::funds(self.commitment.clone()).expect("canonical key")
    }

    pub fn accepts_bytes(&self, bytes: &[u8], statement: &[F]) -> Result<(), String> {
        self.verify(&decode_spend(bytes)?, statement)
    }
}

pub struct SpendVerifier5 {
    commitment: Vec<u8>,
    verifier: p3_circuit_prover::CircuitVerifier<rec5::ZkConfig>,
}

impl SpendVerifier5 {
    pub fn funds(commitment: Vec<u8>) -> Result<Self, String> {
        let key = spend_key(crate::fri_profile::FUNDS_SHAPE);
        if key.commitment != commitment {
            return Err("published key is not the canonical spend circuit".into());
        }
        Ok(SpendVerifier5 { commitment, verifier: key.verifier.clone() })
    }

    pub fn commitment(&self) -> &[u8] {
        &self.commitment
    }

    pub fn accepts(&self, proof: &SpendProof, statement: &[F]) -> Result<(), String> {
        verify_canonical!(self.verifier, proof, statement)
    }

    pub fn accepts_bytes(&self, bytes: &[u8], statement: &[F]) -> Result<(), String> {
        self.accepts(&decode_spend(bytes)?, statement)
    }
}

pub const MAX_FOLD_DEPTH: usize = 6;

pub struct FoldKey5 {
    depth: usize,
    commitment: Vec<u8>,
    verifier: p3_circuit_prover::CircuitVerifier<rec5::MyConfig>,
}

impl FoldKey5 {
    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn commitment(&self) -> &[u8] {
        &self.commitment
    }

    pub fn accepts(&self, proof: &FoldProof, statement: &[F]) -> Result<(), String> {
        verify_canonical!(self.verifier, proof, statement)
    }

    pub fn accepts_bytes(&self, bytes: &[u8], statement: &[F]) -> Result<(), String> {
        self.accepts(&decode_fold(bytes)?, statement)
    }
}

pub fn fold_statement(leaves: &[Vec<F>]) -> Vec<F> {
    leaves.concat()
}

pub fn fold_key(depth: usize) -> &'static FoldKey5 {
    static KEYS: [std::sync::OnceLock<FoldKey5>; MAX_FOLD_DEPTH] = [const { std::sync::OnceLock::new() }; MAX_FOLD_DEPTH];
    assert!((1..=MAX_FOLD_DEPTH).contains(&depth), "fold depth {depth} outside 1..={MAX_FOLD_DEPTH}");
    KEYS[depth - 1].get_or_init(|| generate_fold_key(depth))
}

pub fn generate_fold_key(depth: usize) -> FoldKey5 {
    assert!((1..=MAX_FOLD_DEPTH).contains(&depth), "fold depth {depth} outside 1..={MAX_FOLD_DEPTH}");
    assert_eq!(spend_schema().base_len(), DIGEST, "a spend statement is one digest");
    let shape = crate::fri_profile::FUNDS_SHAPE;
    let fc = if depth == 1 {
        let key = spend_key(shape);
        let (p0, p1) = (key.prove(0), key.prove(1));
        build_fold_circuit(shape, &[FoldInput::Spend(&p0, key), FoldInput::Spend(&p1, key)])
    } else {
        let (inner, p) = (fold_key(depth - 1), sample_fold(depth - 1));
        build_fold_circuit(shape, &[FoldInput::Fold(p, inner), FoldInput::Fold(p, inner)])
    };
    assert!(fc.schema == fold_schema(depth), "depth-{depth} fold statement schema");
    let (npo_prep, air_builders) = fold_preprocessing(&fc.schema);
    let verifier = fold_prover(&rec5::fold_config(shape), &fc.schema)
        .prepare_circuit::<Challenge, 5>(&fc.circuit, &npo_prep, &air_builders, ConstraintProfile::Standard)
        .expect("D5 fold relation")
        .verifier();
    let commitment = preprocessed_commitment(verifier.common_data());
    FoldKey5 { depth, commitment, verifier }
}

fn sample_fold(depth: usize) -> &'static FoldProof {
    static SAMPLES: [std::sync::OnceLock<FoldProof>; MAX_FOLD_DEPTH] = [const { std::sync::OnceLock::new() }; MAX_FOLD_DEPTH];
    SAMPLES[depth - 1].get_or_init(|| {
        let folded = if depth == 1 {
            let key = spend_key(crate::fri_profile::FUNDS_SHAPE);
            let (p0, p1) = (key.prove(0), key.prove(1));
            fold_pair(FoldInput::Spend(&p0, key), FoldInput::Spend(&p1, key))
        } else {
            let (inner, p) = (fold_key(depth - 1), sample_fold(depth - 1));
            fold_pair(FoldInput::Fold(p, inner), FoldInput::Fold(p, inner))
        };
        folded.expect("sample fold").proof
    })
}

#[derive(Clone, Copy)]
pub enum FoldInput<'a> {
    Spend(&'a BatchStarkProof<rec5::ZkConfig>, &'a SpendKey5),
    #[cfg_attr(not(test), allow(dead_code))]
    PlainSpend(&'a BatchStarkProof<rec5::MyConfig>, &'a PlainSpendKey5),
    Fold(&'a BatchStarkProof<rec5::MyConfig>, &'a FoldKey5),
}

impl FoldInput<'_> {
    fn layer(&self) -> &'static str {
        match self {
            FoldInput::Spend(..) => "Spend",
            FoldInput::PlainSpend(..) => "PlainSpend",
            FoldInput::Fold(..) => "Fold",
        }
    }
}

pub struct Folded5 {
    pub proof: BatchStarkProof<rec5::MyConfig>,
    pub depth: usize,
    pub statement: Vec<F>,
    cpd: CircuitProverData<rec5::MyConfig>,
    airs: Vec<CircuitTableAir<rec5::MyConfig, 5>>,
}

fn num_tables<SC: p3_uni_stark::StarkGenericConfig>(common: &p3_batch_stark::CommonData<SC>) -> usize {
    common.preprocessed.as_ref().map(|g| g.instances.len()).unwrap_or(0)
}

fn table_public_values<SC: p3_uni_stark::StarkGenericConfig>(
    proof: &BatchStarkProof<SC>,
    common: &p3_batch_stark::CommonData<SC>,
) -> Vec<Vec<p3_uni_stark::Val<SC>>> {
    let mut pis = vec![vec![]; num_tables(common)];
    if let Some(pos) = statement_position(proof) {
        pis[p3_circuit_prover::NUM_PRIMITIVE_TABLES + pos] = proof.non_primitives[pos].public_values.clone();
    }
    pis
}

fn statement_position<SC: p3_uni_stark::StarkGenericConfig>(proof: &BatchStarkProof<SC>) -> Option<usize> {
    proof.non_primitives.iter().position(|e| e.op_type == p3_circuit::NpoTypeId::statement())
}

struct FoldCircuit5 {
    circuit: p3_circuit::Circuit<Challenge>,
    public: Vec<Challenge>,
    private: Vec<Challenge>,
    op_ids: Vec<Vec<NonPrimitiveOpId>>,
    claimed: Vec<u32>,
    schema: StatementSchema,
}

impl Folded5 {
    pub fn common(&self) -> &p3_batch_stark::CommonData<rec5::MyConfig> {
        self.cpd.common_data()
    }
}

pub fn fold_pair(a: FoldInput, b: FoldInput) -> Result<Folded5, String> {
    let f = fold_pair_at(crate::fri_profile::FUNDS_SHAPE, [a, b])?;
    fold_key(f.depth)
        .accepts(&f.proof, &f.statement)
        .map_err(|e| format!("fold is not the canonical depth-{} fold: {e}", f.depth))?;
    Ok(f)
}

fn fold_pair_at(shape: FriShape, inputs: [FoldInput; 2]) -> Result<Folded5, String> {
    let depth = match inputs {
        [FoldInput::Spend(..), FoldInput::Spend(..)] => 1,
        [FoldInput::Fold(_, a), FoldInput::Fold(_, b)] if a.depth == b.depth => a.depth + 1,
        _ => return Err("a fold takes two spends or two folds of one depth".into()),
    };
    if depth > MAX_FOLD_DEPTH {
        return Err(format!("fold depth {depth} exceeds {MAX_FOLD_DEPTH}"));
    }
    for (i, input) in inputs.iter().enumerate() {
        let fail = |what: String| format!("inner proof {i} ({}) {what}", input.layer());
        match *input {
            FoldInput::Spend(proof, key) => {
                if key.shape != shape {
                    return Err(fail(format!("has a spend key at {:?}, not the fold shape", key.shape)));
                }
                if key.commitment != spend_key(shape).commitment {
                    return Err(fail("has a spend key that is not the canonical spend circuit".into()));
                }
                let st = carried_statement(proof).ok_or_else(|| fail("carries no statement".into()))?;
                key.verify(proof, &st).map_err(|e| fail(format!("is not valid: {e}")))?;
            }
            FoldInput::PlainSpend(..) => unreachable!("plain spends never reach fold_pair_at"),
            FoldInput::Fold(proof, key) => {
                if key.commitment != fold_key(key.depth).commitment {
                    return Err(fail(format!("has a fold key that is not the canonical depth-{} key", key.depth)));
                }
                let st = carried_statement(proof).ok_or_else(|| fail("carries no statement".into()))?;
                key.accepts(proof, &st).map_err(|e| fail(format!("is not valid: {e}")))?;
            }
        }
    }
    let (fc, traces) = fold_traces(shape, &inputs)?;
    let folded = prove_fold(&rec5::fold_config(shape), &fc, &traces)?;
    Ok(Folded5 { depth, ..folded })
}

fn fold_traces(shape: FriShape, inputs: &[FoldInput]) -> Result<(FoldCircuit5, p3_circuit::Traces<Challenge>), String> {
    let fold_config = rec5::fold_config(shape);
    let fc = build_fold_circuit(shape, inputs);
    let mut runner = fc.circuit.runner();
    runner.set_public_inputs(&fc.public).expect("fold public");
    runner.set_private_inputs(&fc.private).expect("fold private");
    for (input, ops) in inputs.iter().zip(&fc.op_ids) {
        set_mmcs(&mut runner, &fold_config, shape, input, ops);
    }
    let traces = runner.run().map_err(|e| format!("fold circuit: {e:?}"))?;
    Ok((fc, traces))
}

fn build_fold_circuit(shape: FriShape, inputs: &[FoldInput]) -> FoldCircuit5 {
    let first = build_fold_circuit_claiming(shape, inputs, &[]);
    let unclaimed = unclaimed_private_inputs(&first.circuit);
    if unclaimed.is_empty() {
        return first;
    }
    use p3_field::PrimeField64;
    let pos: std::collections::HashMap<u32, usize> =
        first.circuit.private_input_rows.iter().enumerate().map(|(i, w)| (w.0, i)).collect();
    let mut got: Vec<u64> = unclaimed
        .iter()
        .map(|w| {
            let c: &[F] = first.private[pos[w]].as_basis_coefficients_slice();
            assert!(c[1..].iter().all(|x| *x == F::ZERO), "unclaimed private input {w} is not a base value (UnclaimedPrivateInput)");
            c[0].as_canonical_u64()
        })
        .collect();
    let mut want: Vec<u64> = hiding_salts(inputs).iter().map(|x| x.as_canonical_u64()).collect();
    got.sort_unstable();
    want.sort_unstable();
    assert!(got == want, "unclaimed private inputs are not exactly the hiding-MMCS salts (UnclaimedPrivateInput)");
    let by_wid: std::collections::HashMap<u32, ExprId> =
        first.circuit.expr_to_widx.iter().map(|(e, w)| (w.0, *e)).collect();
    let claim: Vec<ExprId> = unclaimed.iter().map(|w| by_wid[w]).collect();
    let mut second = build_fold_circuit_claiming(shape, inputs, &claim);
    assert!(second.public == first.public && second.private == first.private, "fold circuit rebuild differs");
    assert!(unclaimed_private_inputs(&second.circuit).is_empty(), "claim rows left inputs unclaimed");
    second.claimed = claim.iter().map(|e| second.circuit.expr_to_widx[e].0).collect();
    second
}

fn hiding_salts(inputs: &[FoldInput]) -> Vec<F> {
    let mut salts = Vec::new();
    for input in inputs {
        if let FoldInput::Spend(proof, _) = *input {
            for opening in &proof.proof.opening_proof.1.input_openings {
                salts.extend(opening.opening_proof.0.iter().flatten().flatten().copied());
            }
            for step in &proof.proof.opening_proof.1.commit_phase_openings {
                salts.extend(step.opening_proof.0.iter().flatten().flatten().copied());
            }
        }
    }
    salts
}

fn unclaimed_private_inputs(circuit: &p3_circuit::Circuit<Challenge>) -> Vec<u32> {
    use p3_circuit::ops::Op;
    let mut claimed = std::collections::HashSet::new();
    for op in &circuit.ops {
        match op {
            Op::Alu { a, b, c, out, .. } => {
                claimed.extend([Some(*a), Some(*b), *c, Some(*out)].into_iter().flatten().map(|w| w.0));
            }
            Op::Const { out, .. } | Op::Public { out, .. } => {
                claimed.insert(out.0);
            }
            Op::Hint { outputs, .. } => claimed.extend(outputs.iter().map(|w| w.0)),
            Op::NonPrimitiveOpWithExecutor { outputs, .. } => claimed.extend(outputs.concat().iter().map(|w| w.0)),
        }
    }
    circuit.private_input_rows.iter().map(|w| w.0).filter(|w| !claimed.contains(w)).collect()
}

macro_rules! pin_key_and_export {
    ($b:expr, $vi:expr, $verifier:expr, $exports:expr) => {{
        let expected = &$verifier.common_data().preprocessed.as_ref().expect("child key has preprocessing").commitment;
        $vi.common_data
            .preprocessed_commitment()
            .expect("child targets have preprocessing")
            .constrain_constant($b, expected)
            .expect("pin child key");
        let at = $verifier.statement_layout().table_instance().expect("child exports a statement");
        assert!(
            $vi.air_public_targets.iter().enumerate().all(|(i, t)| i == at || t.is_empty()),
            "a child table other than the Statement has public values"
        );
        $exports.extend($vi.air_public_targets[at].iter().map(|&t| StatementExport::Base(t)));
    }};
}

fn build_fold_circuit_claiming(shape: FriShape, inputs: &[FoldInput], claim: &[ExprId]) -> FoldCircuit5 {
    let fold_config = rec5::fold_config(shape);
    let mut b = CircuitBuilder::<Challenge>::new();
    b.enable_poseidon2_perm_base::<KoalaBearD1Width16, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD1Width16>,
        Lift(default_koalabear_poseidon2_16()),
    );
    b.enable_recompose::<F>(generate_recompose_trace::<F, Challenge>);
    b.set_recompose_coeff_ctl_for_decompose_links(true);
    let fri_vp = FriVerifierParams::with_mmcs(
        shape.log_blowup,
        0,
        shape.max_log_arity,
        0,
        QUERY_POW_BITS,
        shape.num_queries,
        Poseidon2Config::KOALA_BEAR_D1_W16,
    );
    let lookup = LogUpGadget::new();
    let mut public = Vec::new();
    let mut private = Vec::new();
    let mut op_ids: Vec<Vec<NonPrimitiveOpId>> = Vec::new();
    let mut exports = Vec::new();
    for input in inputs {
        let (pb, pv, op) = match *input {
            FoldInput::Spend(proof, key) if untrusted_build() => {
                let common = key.cpd.common_data();
                let (vi, op) = verify_p3_batch_proof_circuit::<
                    rec5::ZkConfig,
                    MerkleCapTargets<F, 8>,
                    InputProofTargets<F, Challenge, rec5::RecHidingValMmcs>,
                    rec5::InnerFriZk,
                    LogUpGadget,
                    _,
                    16,
                    8,
                    5,
                >(&rec5::make_zk_config(shape), &mut b, proof, &fri_vp, common, &lookup, Poseidon2Config::KOALA_BEAR_D1_W16, &spend_nps())
                .expect("untrusted in-circuit spend verifier builds");
                let at = p3_circuit_prover::NUM_PRIMITIVE_TABLES + statement_position(proof).expect("spend statement");
                exports.extend(vi.air_public_targets[at].iter().map(|&t| StatementExport::Base(t)));
                let (pb, pv) = vi.pack_values(&table_public_values(proof, common), &proof.proof, common);
                (pb, pv, op)
            }
            FoldInput::Fold(proof, key) if untrusted_build() => {
                let common = key.verifier.common_data();
                let (vi, op) = verify_p3_batch_proof_circuit::<
                    rec5::MyConfig,
                    MerkleCapTargets<F, 8>,
                    InputProofTargets<F, Challenge, p3_recursion::pcs::RecValMmcs<F, 8, rec5::MyHash, rec5::MyCompress>>,
                    rec5::InnerFri,
                    LogUpGadget,
                    _,
                    16,
                    8,
                    5,
                >(&fold_config, &mut b, proof, &fri_vp, common, &lookup, Poseidon2Config::KOALA_BEAR_D1_W16, &fold_nps(&fold_schema(key.depth)))
                .expect("untrusted in-circuit fold verifier builds");
                let at = p3_circuit_prover::NUM_PRIMITIVE_TABLES + statement_position(proof).expect("fold statement");
                exports.extend(vi.air_public_targets[at].iter().map(|&t| StatementExport::Base(t)));
                let (pb, pv) = vi.pack_values(&table_public_values(proof, common), &proof.proof, common);
                (pb, pv, op)
            }
            FoldInput::Spend(proof, key) => {
                let statement = carried_statement(proof).expect("spend carries a statement");
                let (vi, op) = verify_trusted_p3_batch_proof_circuit::<
                    rec5::ZkConfig,
                    MerkleCapTargets<F, 8>,
                    InputProofTargets<F, Challenge, rec5::RecHidingValMmcs>,
                    rec5::InnerFriZk,
                    LogUpGadget,
                    _,
                    16,
                    8,
                    5,
                >(&key.verifier, &mut b, proof, &statement, &fri_vp, &lookup, Poseidon2Config::KOALA_BEAR_D1_W16)
                .expect("D5 in-circuit spend verifier builds");
                pin_key_and_export!(&mut b, vi, key.verifier, exports);
                let pis = key.verifier.table_public_values(&statement).expect("spend statement");
                let (pb, pv) = vi.pack_values(&pis, &proof.proof, key.verifier.common_data());
                (pb, pv, op)
            }
            FoldInput::PlainSpend(proof, key) => {
                let common = key.cpd.common_data();
                let (vi, op) = verify_p3_batch_proof_circuit::<
                    rec5::MyConfig,
                    MerkleCapTargets<F, 8>,
                    InputProofTargets<F, Challenge, p3_recursion::pcs::RecValMmcs<F, 8, rec5::MyHash, rec5::MyCompress>>,
                    rec5::InnerFri,
                    LogUpGadget,
                    _,
                    16,
                    8,
                    5,
                >(&fold_config, &mut b, proof, &fri_vp, common, &lookup, Poseidon2Config::KOALA_BEAR_D1_W16, &plain_spend_nps())
                .expect("D5 in-circuit plain spend verifier builds");
                let at = p3_circuit_prover::NUM_PRIMITIVE_TABLES + statement_position(proof).expect("plain spend statement");
                exports.extend(vi.air_public_targets[at].iter().map(|&t| StatementExport::Base(t)));
                let (pb, pv) = vi.pack_values(&table_public_values(proof, common), &proof.proof, common);
                (pb, pv, op)
            }
            FoldInput::Fold(proof, key) => {
                let statement = carried_statement(proof).expect("fold carries a statement");
                let (vi, op) = verify_trusted_p3_batch_proof_circuit::<
                    rec5::MyConfig,
                    MerkleCapTargets<F, 8>,
                    InputProofTargets<F, Challenge, p3_recursion::pcs::RecValMmcs<F, 8, rec5::MyHash, rec5::MyCompress>>,
                    rec5::InnerFri,
                    LogUpGadget,
                    _,
                    16,
                    8,
                    5,
                >(&key.verifier, &mut b, proof, &statement, &fri_vp, &lookup, Poseidon2Config::KOALA_BEAR_D1_W16)
                .expect("D5 in-circuit fold verifier builds");
                pin_key_and_export!(&mut b, vi, key.verifier, exports);
                let pis = key.verifier.table_public_values(&statement).expect("fold statement");
                let (pb, pv) = vi.pack_values(&pis, &proof.proof, key.verifier.common_data());
                (pb, pv, op)
            }
        };
        public.extend(pb);
        private.extend(pv);
        op_ids.push(op);
    }
    let schema = b.set_statement_exports::<F>(&exports).expect("fold statement");
    if !claim.is_empty() {
        let one = b.alloc_const(Challenge::ONE, "claim_one");
        for &e in claim {
            b.add(e, one);
        }
    }
    let circuit = b.build().expect("D5 fold circuit builds");
    FoldCircuit5 { circuit, public, private, op_ids, claimed: Vec::new(), schema }
}

#[allow(clippy::type_complexity)]
fn fold_preprocessing(
    schema: &StatementSchema,
) -> (Vec<Box<dyn NpoPreprocessor<F>>>, Vec<Box<dyn p3_circuit_prover::common::NpoAirBuilder<rec5::MyConfig, 5>>>) {
    let npo_prep: Vec<Box<dyn NpoPreprocessor<F>>> = vec![
        Box::new(Poseidon2Preprocessor),
        Box::new(RecomposePreprocessor::new(true)),
        Box::new(p3_circuit_prover::StatementPreprocessor::new(schema.clone())),
    ];
    let mut air_builders = poseidon2_air_builders_d5::<rec5::MyConfig>();
    air_builders.extend(recompose_air_builders::<rec5::MyConfig, 5>(1, true));
    air_builders.push(Box::new(p3_circuit_prover::StatementAirBuilder::<5>::new(schema.clone())));
    (npo_prep, air_builders)
}

fn prove_fold(fold_config: &rec5::MyConfig, fc: &FoldCircuit5, traces: &p3_circuit::Traces<Challenge>) -> Result<Folded5, String> {
    let (npo_prep, air_builders) = fold_preprocessing(&fc.schema);
    let (ad, prim, nonprim) = get_airs_and_degrees_with_prep::<rec5::MyConfig, Challenge, 5>(
        &fc.circuit,
        &TablePacking::new(1, 8),
        &npo_prep,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .expect("D5 fold airs");
    let (airs, degrees): (Vec<_>, Vec<usize>) = ad.into_iter().unzip();
    let pd = ProverData::from_airs_and_degrees(fold_config, &airs, &degrees).expect("D5 fold prover data");
    let cpd = CircuitProverData::new(pd, prim, nonprim);
    let prover = fold_prover(fold_config, &fc.schema);
    let proof = prover.prove_all_tables(traces, &cpd).map_err(|e| format!("prove: {e:?}"))?;
    prover.verify_all_tables::<Challenge>(&proof).map_err(|e| format!("verify: {e:?}"))?;
    let statement = carried_statement(&proof).ok_or("fold carries no statement")?;
    Ok(Folded5 { proof, depth: 0, statement, cpd, airs })
}

fn fold_prover(config: &rec5::MyConfig, schema: &StatementSchema) -> BatchStarkProver<rec5::MyConfig> {
    let mut p = BatchStarkProver::new(config.clone()).with_table_packing(TablePacking::new(1, 8));
    p.register_poseidon2_table::<5>(Poseidon2Config::KOALA_BEAR_D1_W16);
    p.register_recompose_table::<5>(true);
    p.register_table_prover(Box::new(p3_circuit_prover::StatementProver::<5>::new(schema.clone())));
    p
}

fn set_mmcs(
    runner: &mut CircuitRunner<'_, Challenge>,
    fold_config: &rec5::MyConfig,
    shape: FriShape,
    input: &FoldInput,
    op_ids: &[NonPrimitiveOpId],
) {
    let (plain, fri_params) = rec5::fri_instance(shape);
    let paths = match *input {
        FoldInput::Spend(proof, key) => {
            let OpeningTranscript { mut challenger, mut commitments_with_opening_points } =
                replay_batch_layer_transcript::<rec5::ZkConfig, 5>(
                    &rec5::make_zk_config(shape),
                    proof,
                    key.cpd.common_data(),
                    &spend_nps(),
                )
                .expect("replay D5 spend");
            p3_recursion::merge_hiding_random_openings::<rec5::ZkConfig>(
                &mut commitments_with_opening_points,
                &proof.proof.opening_proof.0,
            )
            .expect("merge hiding openings");
            observe_opened_values::<rec5::ZkConfig>(&mut challenger, &commitments_with_opening_points, fri_params.batch_proof_of_work_bits);
            let claims: Vec<_> = commitments_with_opening_points.iter().cloned().map(Into::into).collect();
            let (hiding, zk_params) = rec5::zk_fri_instance_with(shape, rand::make_rng::<rec5::Rng>());
            p3_recursion::pcs::restore_hiding_fri_query_paths(
                &zk_params, &hiding, &plain, &plain, &proof.proof.opening_proof.1, &mut challenger, &claims,
            )
            .expect("restore D5 hiding paths")
        }
        FoldInput::PlainSpend(proof, key) => {
            let OpeningTranscript { mut challenger, commitments_with_opening_points } =
                replay_batch_layer_transcript::<rec5::MyConfig, 5>(fold_config, proof, key.cpd.common_data(), &plain_spend_nps())
                    .expect("replay D5 plain spend");
            observe_opened_values::<rec5::MyConfig>(&mut challenger, &commitments_with_opening_points, fri_params.batch_proof_of_work_bits);
            let claims: Vec<_> = commitments_with_opening_points.iter().cloned().map(Into::into).collect();
            restore_fri_query_paths(&fri_params, &plain, &plain, &proof.proof.opening_proof, &mut challenger, &claims)
                .expect("restore D5 plain spend paths")
        }
        FoldInput::Fold(proof, key) => {
            let OpeningTranscript { mut challenger, commitments_with_opening_points } =
                replay_batch_layer_transcript::<rec5::MyConfig, 5>(fold_config, proof, key.verifier.common_data(), &fold_nps(&fold_schema(key.depth)))
                    .expect("replay D5 fold");
            observe_opened_values::<rec5::MyConfig>(&mut challenger, &commitments_with_opening_points, fri_params.batch_proof_of_work_bits);
            let claims: Vec<_> = commitments_with_opening_points.iter().cloned().map(Into::into).collect();
            restore_fri_query_paths(&fri_params, &plain, &plain, &proof.proof.opening_proof, &mut challenger, &claims)
                .expect("restore D5 paths")
        }
    };
    set_fri_mmcs_private_data::<F, Challenge, 8>(runner, op_ids, &paths, Poseidon2Config::KOALA_BEAR_D1_W16)
        .expect("D5 mmcs private data");
}

fn kb_spend(p: &BatchStarkProof<rec5::ZkConfig>) -> f64 {
    postcard::to_allocvec(p).map(|v| v.len()).unwrap_or(0) as f64 / 1024.0
}

fn kb_fold(p: &BatchStarkProof<rec5::MyConfig>) -> f64 {
    postcard::to_allocvec(p).map(|v| v.len()).unwrap_or(0) as f64 / 1024.0
}

pub fn peak_rss_mb() -> Option<f64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    let kb: f64 = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(kb / 1024.0)
}

macro_rules! soundness_d5 {
    ($name:ident, $sc:ty) => {
        fn $name(
            shape: FriShape,
            airs: &[CircuitTableAir<$sc, 5>],
            common: &p3_batch_stark::CommonData<$sc>,
            proof: &BatchStarkProof<$sc>,
        ) -> Vec<crate::soundness::TableShape> {
            let _ = shape;
            proof
                .proof
                .opened_values
                .instances
                .iter()
                .zip(airs)
                .zip(&proof.proof.degree_bits)
                .zip(&common.lookups)
                .map(|(((inst, air), &degree_bits), lookups)| {
                    let ov = &inst.base_opened_values;
                    crate::soundness::table_shape::<F, Challenge, _>(
                        air,
                        lookups,
                        degree_bits,
                        ov.trace_next.is_some(),
                        ov.preprocessed.as_ref().map(|p| p.local.len()).unwrap_or(0),
                        ov.preprocessed.as_ref().map(|p| p.next.is_some()).unwrap_or(false),
                        ov.quotient_chunks.len(),
                    )
                })
                .collect()
        }
    };
}

soundness_d5!(spend_tables, rec5::ZkConfig);
soundness_d5!(fold_tables, rec5::MyConfig);

fn print_bits(name: &str, tables: &[crate::soundness::TableShape], shape: FriShape) -> f64 {
    let fri = crate::soundness::FriShapeBits {
        log_blowup: shape.log_blowup,
        max_log_arity: shape.max_log_arity,
        log_final_poly_len: 0,
        num_queries: shape.num_queries,
        commit_pow_bits: 0,
        query_pow_bits: QUERY_POW_BITS,
        batch_pow_bits: 0,
        lookup_pow_bits: 0,
        ood_pow_bits: 0,
    };
    let r = crate::soundness::report::<F>(tables, &fri, rec5::D, rec5::DIGEST_ELEMS);
    for t in tables {
        println!(
            "  D5 {name:<15} table: log2 rows {:>2} main {:>4} prep {:>3} quotient {} lookups {:>2} interactions {:>3} max message {:>2} constraints {:>4} deg {}",
            t.degree_bits, t.main_width, t.preprocessed_width, t.quotient_chunks, t.num_lookups,
            t.interactions_per_row, t.max_message_width, t.num_constraints, t.max_constraint_degree
        );
    }
    println!(
        "  D5 {name:<15} tables {} log2 domain {} batched {} constraints {} max deg {}: proven {:.1} (UDR {:.1} {}, LDR {:.1} {}) conjectured {:.1} ({})",
        r.tables, r.log_domain, r.batched_functions, r.constraints, r.max_degree, r.proven_bits(),
        r.udr_bits, r.udr_binding, r.ldr_bits, r.ldr_binding, r.conjectured_bits, r.conjectured_binding
    );
    r.udr_bits
}

pub fn cpu_secs() -> Option<f64> {
    let stat = std::fs::read_to_string("/proc/self/stat").ok()?;
    let rest = stat.rsplit_once(')')?.1;
    let f: Vec<&str> = rest.split_whitespace().collect();
    let ticks: f64 = f.get(11)?.parse::<f64>().ok()? + f.get(12)?.parse::<f64>().ok()?;
    Some(ticks / 100.0)
}

fn timed<T>(f: impl FnOnce() -> T) -> (T, f64, f64) {
    let (t, c) = (Instant::now(), cpu_secs().unwrap_or(0.0));
    let out = f();
    (out, t.elapsed().as_secs_f64(), cpu_secs().unwrap_or(0.0) - c)
}

pub fn measure(shape: FriShape) {
    let (key, keygen, _) = timed(|| spend_key(shape));
    let (zk, prove, prove_cpu) = timed(|| key.prove(0));
    let node = SpendVerifier5::funds(key.commitment().to_vec()).expect("canonical key");
    let statement = spend_statement(0);
    let (mut verify, mut verify_cpu) = (f64::MAX, f64::MAX);
    for _ in 0..5 {
        let (ok, w, c) = timed(|| node.accepts(&zk, &statement));
        ok.expect("D5 ZK spend verifies");
        (verify, verify_cpu) = (verify.min(w), verify_cpu.min(c));
    }

    let spends: Vec<_> = std::iter::once(zk).chain((1..4).map(|s| key.prove(s))).collect();
    let (f01, fold, fold_cpu) =
        timed(|| fold_pair_at(shape, [FoldInput::Spend(&spends[0], key), FoldInput::Spend(&spends[1], key)]).expect("fold"));
    let f23 = fold_pair_at(shape, [FoldInput::Spend(&spends[2], key), FoldInput::Spend(&spends[3], key)]).expect("fold");
    let (root, fold2, fold2_cpu) = timed(|| {
        fold_pair_at(shape, [FoldInput::Fold(&f01.proof, fold_key(1)), FoldInput::Fold(&f23.proof, fold_key(1))])
            .expect("fold")
    });
    println!(
        "KoalaBear^5 {shape:?} (wall s / CPU s): keygen {keygen:.1} s; ZK spend {:.1} KB, prove {prove:.2} / {prove_cpu:.1}, \
         verify {:.1} ms / {verify_cpu:.2} s; fold of 2 ZK spends {:.1} KB in {fold:.1} / {fold_cpu:.0}; \
         fold of folds {:.1} KB in {fold2:.1} / {fold2_cpu:.0}; peak RSS {:?} MB",
        kb_spend(&spends[0]),
        verify * 1e3,
        kb_fold(&f01.proof),
        kb_fold(&root.proof),
        peak_rss_mb().map(|m| m.round()),
    );
    let st = spend_tables(shape, &key.airs, key.cpd.common_data(), &spends[0]);
    let ft = fold_tables(shape, &f01.airs, f01.cpd.common_data(), &f01.proof);
    let rt = fold_tables(shape, &root.airs, root.cpd.common_data(), &root.proof);
    for (name, tables) in [("ZK spend", &st), ("fold", &ft), ("fold of folds", &rt)] {
        let udr = print_bits(name, tables, shape);
        assert!(udr >= crate::fri_profile::TARGET_BITS, "{name}: {udr:.1} bits in unique decoding at {shape:?}");
    }
    crate::faraday_fold::min_queries_sweep_for("D5 ZK spend", &st, shape.max_log_arity, &[5], &[0]);
    crate::faraday_fold::min_queries_sweep_for("D5 fold", &ft, shape.max_log_arity, &[5], &[0]);
    crate::faraday_fold::min_queries_sweep_for("D5 fold of folds", &rt, shape.max_log_arity, &[5], &[0]);
}

pub fn keccak_cost_probe() {
    use p3_circuit_prover::{KeccakF1600AirBuilder, KeccakF1600Preprocessor, KeccakF1600Prover};
    let shape = crate::fri_profile::FUNDS_SHAPE;
    let base = spend_key(shape);
    let (p, w, c) = timed(|| base.prove(0));
    println!("baseline ZK spend: {:.1} KB, prove {w:.2} s wall / {c:.1} s CPU", kb_spend(&p));

    let config = rec5::keygen_zk_config(shape);
    let (circuit, io) = build_spend_circuit_with(0, true);
    let npo_prep: Vec<Box<dyn NpoPreprocessor<F>>> = vec![Box::new(Poseidon2Preprocessor), Box::new(KeccakF1600Preprocessor)];
    let mut air_builders = poseidon2_air_builders_d5::<rec5::ZkConfig>();
    air_builders.push(Box::new(KeccakF1600AirBuilder::<5>));
    let (airs_degrees, prim, nonprim) = get_airs_and_degrees_with_prep::<rec5::ZkConfig, Challenge, 5>(
        &circuit,
        &spend_packing(shape),
        &npo_prep,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .expect("D5 spend + keccak airs");
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    let degrees: Vec<usize> = degrees.iter().map(|d| d + 1).collect();
    let pd = ProverData::from_airs_and_degrees(&config, &airs, &degrees).expect("prover data");
    let cpd = CircuitProverData::new(pd, prim, nonprim);
    let mut prover = BatchStarkProver::new(rec5::make_zk_config(shape)).with_table_packing(spend_packing(shape));
    prover.register_poseidon2_table::<5>(Poseidon2Config::KOALA_BEAR_D1_W32);
    prover.register_table_prover(Box::new(KeccakF1600Prover::<5>));
    let mut runner = circuit.runner();
    runner.set_private_inputs(&io.priv_vals).expect("private");
    runner.set_public_inputs(&io.pub_vals).expect("public");
    let traces = runner.run().expect("spend + keccak runs");
    let (proof, w, c) = timed(|| prover.prove_all_tables(&traces, &cpd).expect("prove spend + keccak"));
    let (ok, vw, _) = timed(|| prover.verify_all_tables::<Challenge>(&proof));
    ok.expect("spend + keccak verifies");
    println!(
        "ZK spend + 1 Keccak-256: {:.1} KB, prove {w:.2} s wall / {c:.1} s CPU, verify {:.0} ms; degree bits {:?}",
        kb_spend(&proof),
        vw * 1e3,
        proof.proof.degree_bits
    );
    let st = spend_tables(shape, &airs, cpd.common_data(), &proof);
    for t in &st {
        println!("  table: log2 rows {:>2} main {:>5} prep {:>4} quotient {}", t.degree_bits, t.main_width, t.preprocessed_width, t.quotient_chunks);
    }
    print_bits("ZK spend + Keccak", &st, shape);
}

fn in_circuit_check(key: &SpendKey5, proof: &SpendProof) {
    let shape = crate::fri_profile::FUNDS_SHAPE;
    let inputs = [FoldInput::Spend(proof, key)];
    let (fc, _) = fold_traces(shape, &inputs).expect("M4c: honest spend verifies in-circuit");
    let mut bad = fc.private.clone();
    bad[0] += Challenge::ONE;
    let mut runner = fc.circuit.runner();
    runner.set_public_inputs(&fc.public).expect("public");
    runner.set_private_inputs(&bad).expect("private");
    set_mmcs(&mut runner, &rec5::fold_config(shape), shape, &inputs[0], &fc.op_ids[0]);
    assert!(runner.run().is_err(), "M4c: a tampered spend proof was accepted in-circuit");
}

pub fn run_all_and_save() {
    let key = spend_key(crate::fri_profile::FUNDS_SHAPE);
    let spends: Vec<SpendProof> = (0..4).map(|s| key.prove(s)).collect();
    for (seed, p) in spends.iter().enumerate() {
        key.accepts_bytes(&encode_spend(p), &spend_statement(seed as u64)).expect("spend verifies against its statement");
    }
    in_circuit_check(key, &spends[0]);
    println!("M4c OK: spend verified in-circuit; a tampered proof is rejected.");
    let f01 = fold_pair(FoldInput::Spend(&spends[0], key), FoldInput::Spend(&spends[1], key)).expect("fold");
    let f23 = fold_pair(FoldInput::Spend(&spends[2], key), FoldInput::Spend(&spends[3], key)).expect("fold");
    let root = fold_pair(FoldInput::Fold(&f01.proof, fold_key(1)), FoldInput::Fold(&f23.proof, fold_key(1))).expect("fold");
    let leaves: Vec<Vec<F>> = (0..4).map(spend_statement).collect();
    for (f, st) in [(&f01, fold_statement(&leaves[0..2])), (&f23, fold_statement(&leaves[2..4])), (&root, fold_statement(&leaves))] {
        fold_key(f.depth).accepts_bytes(&encode_fold(&f.proof), &st).expect("fold verifies against its leaves");
    }
    println!(
        "M4d/M4e OK: spend {:.1} KB, fold of 2 spends {:.1} KB, root of 4 {:.1} KB.",
        kb_spend(&spends[0]),
        kb_fold(&f01.proof),
        kb_fold(&root.proof)
    );
    use crate::faraday_fold::save_proof;
    save_proof("spend-vk.bin", key.commitment());
    save_proof("fold-vk-1.bin", fold_key(1).commitment());
    save_proof("fold-vk-2.bin", fold_key(2).commitment());
    save_proof("spend-funds.bin", &encode_spend(&spends[0]));
    save_proof("fold-funds.bin", &encode_fold(&f01.proof));
    save_proof("root-funds.bin", &encode_fold(&root.proof));
}

pub fn verify_saved_proofs() -> bool {
    let dir = crate::faraday_fold::proof_dir();
    let read = |name: &str| {
        std::fs::read(format!("{dir}/{name}")).unwrap_or_else(|e| panic!("{dir}/{name}: {e} (run the faraday_fold bin first)"))
    };
    let funds = SpendVerifier5::funds(read("spend-vk.bin")).expect("spend-vk.bin is the canonical spend key");
    let statement = spend_statement(0);
    assert_eq!(
        funds.commitment(),
        generate_spend_key(crate::fri_profile::FUNDS_SHAPE).commitment(),
        "spend-vk.bin is not the verifying key recomputed from the spend circuit"
    );
    for depth in [1, 2] {
        assert_eq!(
            read(&format!("fold-vk-{depth}.bin")),
            generate_fold_key(depth).commitment(),
            "fold-vk-{depth}.bin is not the fold key recomputed from the fold circuit"
        );
    }
    let leaves: Vec<Vec<F>> = (0..4).map(spend_statement).collect();
    let (fold_st, root_st) = (fold_statement(&leaves[0..2]), fold_statement(&leaves));
    let checks: [(&str, &dyn Fn(&[u8]) -> Result<(), String>); 3] = [
        ("spend-funds.bin", &|b| funds.accepts_bytes(b, &statement)),
        ("fold-funds.bin", &|b| fold_key(1).accepts_bytes(b, &fold_st)),
        ("root-funds.bin", &|b| fold_key(2).accepts_bytes(b, &root_st)),
    ];
    let mut ok = true;
    for (name, verify) in checks {
        let bytes = read(name);
        verify(&bytes).unwrap_or_else(|e| panic!("{name}: honest proof rejected: {e}"));
        let t = crate::faraday_fold::tamper_sweep(&bytes, 256, verify);
        println!("{name}: honest accepted; tampered {t:?}");
        ok &= t.accepted == 0 && t.panics == 0;
    }
    ok
}

pub struct Measurement {
    pub proof_bytes: usize,
    pub prove_wall: std::time::Duration,
    pub prove_cpu: std::time::Duration,
    pub verify_wall: std::time::Duration,
    pub verify_cpu: std::time::Duration,
}

pub struct Prepared {
    key: &'static SpendKey5,
}

pub fn prepare() -> Prepared {
    Prepared { key: spend_key(crate::fri_profile::FUNDS_SHAPE) }
}

pub fn run_one(prep: &Prepared, seed: u64, cpu_now: &dyn Fn() -> std::time::Duration) -> Measurement {
    let traces = spend_traces(seed);
    let prover = prep.key.prover();
    let (c0, w0) = (cpu_now(), Instant::now());
    let proof = prover.prove_all_tables(&traces, &prep.key.cpd).expect("prove");
    let (prove_wall, prove_cpu) = (w0.elapsed(), cpu_now().saturating_sub(c0));
    let (c0, w0) = (cpu_now(), Instant::now());
    prep.key.verify(&proof, &spend_statement(seed)).expect("verify");
    let (verify_wall, verify_cpu) = (w0.elapsed(), cpu_now().saturating_sub(c0));
    Measurement { proof_bytes: encode_spend(&proof).len(), prove_wall, prove_cpu, verify_wall, verify_cpu }
}

pub struct FoldMeasurement {
    pub base_bytes: usize,
    pub folded_bytes: usize,
    pub fold_wall: std::time::Duration,
}

pub fn fold_two() -> FoldMeasurement {
    let key = spend_key(crate::fri_profile::FUNDS_SHAPE);
    let (p0, p1) = (key.prove(0), key.prove(1));
    let t = Instant::now();
    let folded = fold_pair(FoldInput::Spend(&p0, key), FoldInput::Spend(&p1, key)).expect("fold");
    FoldMeasurement { base_bytes: encode_spend(&p0).len(), folded_bytes: encode_fold(&folded.proof).len(), fold_wall: t.elapsed() }
}

pub fn self_check() -> Result<(), String> {
    let perm = default_koalabear_poseidon2_32();
    let x: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(i as u64 + 1));
    let y: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64((DIGEST + i) as u64 + 1));
    let native = compress(&perm, &x, &y);
    let mut b = CircuitBuilder::<Challenge>::new();
    b.enable_poseidon2_perm_base_width_32::<KoalaBearD1Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD1Width32>,
        Lift(perm.clone()),
    );
    let ex = const_block(&mut b, &x, "x");
    let ey = const_block(&mut b, &y, "y");
    let digest = compress5(&mut b, ex, ey);
    let circuit = b.build().map_err(|e| format!("{e:?}"))?;
    let traces = circuit.runner().run().map_err(|e| format!("{e:?}"))?;
    let got: Vec<Val> = digest
        .iter()
        .map(|e| traces.witness_trace.get_value(circuit.expr_to_widx[e]).expect("digest value").as_basis_coefficients_slice()[0])
        .collect();
    if got == native {
        Ok(())
    } else {
        Err("D1 W32 compression != native KoalaBear Poseidon2".into())
    }
}
