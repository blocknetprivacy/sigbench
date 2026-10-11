use p3_batch_stark::ProverData;
use p3_circuit::ops::{
    generate_poseidon2_trace, generate_recompose_trace, Poseidon2Config, Poseidon2PermCall,
};
use p3_circuit::{CircuitBuilder, ExprId};
use p3_circuit_prover::batch_stark_prover::{
    poseidon2_air_builders, poseidon2_air_builders_for_configs, poseidon2_table_provers_d4,
    recompose_air_builders,
    BatchStarkProof, TableProver,
};
use p3_circuit_prover::common::{get_airs_and_degrees_with_prep, CircuitTableAir, NpoPreprocessor};
use p3_circuit_prover::config::{self, KoalaBearConfig};
use p3_circuit_prover::{
    BatchStarkProver, CircuitProverData, ConstraintProfile, Poseidon2Preprocessor,
    RecomposePreprocessor, TablePacking,
};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_koala_bear::{
    default_koalabear_poseidon2_16, default_koalabear_poseidon2_32, KoalaBear, Poseidon2KoalaBear,
};
use p3_lookup::logup::LogUpGadget;
use p3_poseidon2_circuit_air::{KoalaBearD4Width16, KoalaBearD4Width32};
use p3_recursion::pcs::fri::{FriVerifierParams, InputProofTargets, MerkleCapTargets, RecValMmcs};
use p3_recursion::pcs::{restore_fri_query_paths, set_fri_mmcs_private_data};
use p3_recursion::{observe_opened_values, replay_batch_layer_transcript, OpeningTranscript};
use p3_circuit::{CircuitRunner, NonPrimitiveOpId};
use p3_recursion::verifier::verify_p3_batch_proof_circuit;
use p3_symmetric::Permutation;
use std::time::{Duration, Instant};

pub(crate) type Val = KoalaBear;
type Challenge = BinomialExtensionField<Val, 4>;
pub(crate) type Perm32 = Poseidon2KoalaBear<32>;

pub mod rec {
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_dft::Radix2DitParallel;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::Field;
    use p3_fri::{FriParameters, TwoAdicFriPcs};
    use p3_koala_bear::{default_koalabear_poseidon2_16, KoalaBear, Poseidon2KoalaBear};
    use p3_merkle_tree::MerkleTreeMmcs;
    use p3_recursion::pcs::{
        FriProofTargets, InputProofTargets, RecExtensionValMmcs, RecValMmcs, Witness,
    };
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::StarkConfig;

    pub type F = KoalaBear;
    pub const WIDTH: usize = 16;
    pub const RATE: usize = 8;
    pub const DIGEST_ELEMS: usize = 8;

    pub type Challenge = BinomialExtensionField<F, 4>;
    pub type Dft = Radix2DitParallel<F>;
    pub type Perm = Poseidon2KoalaBear<WIDTH>;
    pub type MyHash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_ELEMS>;
    pub type MyCompress = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, WIDTH>;
    pub type MyMmcs = MerkleTreeMmcs<
        <F as Field>::Packing,
        <F as Field>::Packing,
        MyHash,
        MyCompress,
        2,
        DIGEST_ELEMS,
    >;
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

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct FriShape {
        pub log_blowup: usize,
        pub max_log_arity: usize,
        pub num_queries: usize,
    }

    pub const QUERY_POW_BITS: usize = 16;

    pub fn fri_instance(shape: FriShape) -> (MyMmcs, FriParameters<ChallengeMmcs>) {
        let perm = default_koalabear_poseidon2_16();
        let val_mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);
        let fri_params = FriParameters {
            max_log_arity: shape.max_log_arity,
            log_blowup: shape.log_blowup,
            log_final_poly_len: 0,
            num_queries: shape.num_queries,
            batch_proof_of_work_bits: 0,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: QUERY_POW_BITS,
            mmcs: ChallengeMmcs::new(val_mmcs.clone()),
        };
        (val_mmcs, fri_params)
    }

    pub fn fold_config(shape: FriShape) -> MyConfig {
        make_config(shape.log_blowup, shape.max_log_arity, shape.num_queries)
    }

    pub fn zk_fri_instance(shape: FriShape) -> (HidingValMmcs, FriParameters<HidingChallengeMmcs>) {
        zk_fri_instance_with(shape, rand::make_rng::<Rng>())
    }

    fn zk_fri_instance_with(shape: FriShape, salts: Rng) -> (HidingValMmcs, FriParameters<HidingChallengeMmcs>) {
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

    pub fn make_zk_config(shape: FriShape) -> ZkConfig {
        zk_config_with(shape, rand::make_rng::<Rng>(), rand::make_rng::<Rng>())
    }

    pub fn keygen_zk_config(shape: FriShape) -> ZkConfig {
        use rand::SeedableRng;
        use sha3::{Digest, Sha3_256};
        let seed = |label: &[u8]| -> [u8; 32] {
            let mut h = Sha3_256::new();
            h.update(b"blocknet faraday spend vk v1");
            for v in [shape.log_blowup, shape.max_log_arity, shape.num_queries] {
                h.update((v as u64).to_le_bytes());
            }
            h.update(label);
            h.finalize().into()
        };
        zk_config_with(shape, Rng::from_seed(seed(b"mmcs")), Rng::from_seed(seed(b"pcs")))
    }

    fn zk_config_with(shape: FriShape, salts: Rng, masks: Rng) -> ZkConfig {
        let (val_mmcs, fri_params) = zk_fri_instance_with(shape, salts);
        let pcs = ZkPcs::new(Dft::default(), val_mmcs, fri_params, 4, masks);
        ZkConfig::new(pcs, Challenger::new(default_koalabear_poseidon2_16()))
    }

    pub fn make_config(log_blowup: usize, max_log_arity: usize, num_queries: usize) -> MyConfig {
        let (val_mmcs, fri_params) =
            fri_instance(FriShape { log_blowup, max_log_arity, num_queries });
        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri_params);
        MyConfig::new(pcs, Challenger::new(default_koalabear_poseidon2_16()))
    }
}

pub(crate) const WIDTH: usize = 32;
const LIMB: usize = 4;
const WIDTH_EXT: usize = WIDTH / LIMB;
const RATE_EXT: usize = 6;
pub(crate) const DIGEST: usize = 16;
const DIGEST_EXT: usize = DIGEST / LIMB;
pub(crate) const DEPTH: usize = 32;

pub(crate) const NLIMBS: usize = 4;
pub(crate) const LIMB_BITS: usize = 16;
pub(crate) const CARRY_BITS: usize = 12;
pub(crate) const CARRY_OFF: u64 = 1 << 11;

pub(crate) fn compress(perm: &Perm32, x: &[Val; DIGEST], y: &[Val; DIGEST]) -> [Val; DIGEST] {
    let mut state = [Val::ZERO; WIDTH];
    state[..DIGEST].copy_from_slice(x);
    state[DIGEST..].copy_from_slice(y);
    let out = perm.permute(state);
    core::array::from_fn(|i| out[i])
}

pub(crate) fn dom16(label: &[u8]) -> [Val; DIGEST] {
    assert!(label.len() <= DIGEST, "domain label exceeds one 16-element block");
    core::array::from_fn(|i| {
        if i < label.len() {
            Val::from_u64(label[i] as u64)
        } else {
            Val::ZERO
        }
    })
}

pub(crate) fn v_block(v: u64) -> [Val; DIGEST] {
    core::array::from_fn(|i| {
        if i % LIMB == 0 && i / LIMB < NLIMBS {
            Val::from_u64((v >> (16 * (i / LIMB))) & 0xffff)
        } else {
            Val::ZERO
        }
    })
}

fn amount_limb(v: u64, k: usize) -> Challenge {
    Challenge::from_u64((v >> (16 * k)) & 0xffff)
}

pub(crate) fn oracle_pubkey(perm: &Perm32, k: &[Val; DIGEST]) -> [Val; DIGEST] {
    compress(perm, &dom16(b"blocknet_pubkey"), k)
}
pub(crate) fn oracle_image(perm: &Perm32, k: &[Val; DIGEST]) -> [Val; DIGEST] {
    compress(perm, &dom16(b"blocknet_image"), k)
}
pub(crate) fn oracle_onetime(perm: &Perm32, s_pub: &[Val; DIGEST], r: &[Val; DIGEST]) -> [Val; DIGEST] {
    compress(perm, &compress(perm, &dom16(b"blocknet_onetime"), s_pub), r)
}
pub(crate) fn oracle_image2(perm: &Perm32, s: &[Val; DIGEST], r: &[Val; DIGEST]) -> [Val; DIGEST] {
    compress(perm, &compress(perm, &dom16(b"blocknet_image"), s), r)
}
pub fn bits_of_index(n: u64) -> Vec<bool> {
    assert!(n < 1 << 32, "depth-32 tree");
    (0..32).map(|d| (n >> d) & 1 == 1).collect()
}

pub(crate) fn oracle_image3(perm: &Perm32, s: &[Val; DIGEST], r: &[Val; DIGEST], bits: &[bool]) -> [Val; DIGEST] {
    assert_eq!(bits.len(), 32, "depth-32 path");
    let limb = |bits: &[bool]| bits.iter().enumerate().map(|(j, &x)| (x as u64) << j).sum::<u64>();
    let idx: [Val; DIGEST] = core::array::from_fn(|i| match i {
        0 => Val::from_u64(limb(&bits[..16])),
        1 => Val::from_u64(limb(&bits[16..])),
        _ => Val::ZERO,
    });
    compress(perm, &oracle_image2(perm, s, r), &idx)
}
pub(crate) fn oracle_commit_cond(perm: &Perm32, p: &[Val; DIGEST], v: u64, b: &[Val; DIGEST], cond: &[Val; DIGEST]) -> [Val; DIGEST] {
    compress(perm, &oracle_commit(perm, p, v, b), cond)
}
pub(crate) fn oracle_commit(perm: &Perm32, k_pub: &[Val; DIGEST], v: u64, b: &[Val; DIGEST]) -> [Val; DIGEST] {
    let s1 = compress(perm, &dom16(b"blocknet_commit"), k_pub);
    let s2 = compress(perm, &s1, &v_block(v));
    compress(perm, &s2, b)
}

pub fn scan_match_leaf(s_pub: &[u32; DIGEST], r: &[u32; DIGEST], v: u64, b: &[u32; DIGEST]) -> [u32; DIGEST] {
    use p3_field::PrimeField32;
    static PERM: std::sync::OnceLock<Perm32> = std::sync::OnceLock::new();
    let perm = PERM.get_or_init(default_koalabear_poseidon2_32);
    let f = |x: &[u32; DIGEST]| -> [Val; DIGEST] { core::array::from_fn(|i| Val::from_u32(x[i])) };
    let p = oracle_onetime(perm, &f(s_pub), &f(r));
    let leaf = oracle_commit_cond(perm, &p, v, &f(b), &[Val::ZERO; DIGEST]);
    core::array::from_fn(|i| leaf[i].as_canonical_u32())
}

pub(crate) fn fold_native(
    perm: &Perm32,
    leaf: &[Val; DIGEST],
    siblings: &[[Val; DIGEST]],
    bits: &[bool],
) -> [Val; DIGEST] {
    let mut node = *leaf;
    for (sib, &bit) in siblings.iter().zip(bits.iter()) {
        node = if !bit {
            compress(perm, &node, sib)
        } else {
            compress(perm, sib, &node)
        };
    }
    node
}

fn pack16(vals: &[Val; DIGEST]) -> [Challenge; DIGEST_EXT] {
    core::array::from_fn(|i| {
        Challenge::from_basis_coefficients_slice(&vals[i * LIMB..(i + 1) * LIMB])
            .expect("4 coeffs pack into one Ext4 limb")
    })
}

fn unpack(limb: &Challenge) -> [Val; LIMB] {
    let c = limb.as_basis_coefficients_slice();
    core::array::from_fn(|i| c[i])
}

fn alloc_block(
    builder: &mut CircuitBuilder<Challenge>,
    vals: &[Val; DIGEST],
    label: &'static str,
) -> [ExprId; DIGEST_EXT] {
    let limbs = pack16(vals);
    core::array::from_fn(|i| builder.alloc_const(limbs[i], label))
}

fn wire_scalar(builder: &mut CircuitBuilder<Challenge>, x: ExprId, one: ExprId) -> ExprId {
    let t = builder.add(x, one);
    builder.sub(t, one)
}
fn wire_block(
    builder: &mut CircuitBuilder<Challenge>,
    block: &[ExprId; DIGEST_EXT],
    one: ExprId,
) -> [ExprId; DIGEST_EXT] {
    core::array::from_fn(|i| wire_scalar(builder, block[i], one))
}

fn mux(builder: &mut CircuitBuilder<Challenge>, bit: ExprId, t: ExprId, s: ExprId) -> ExprId {
    let d = builder.sub(t, s);
    builder.mul_add(bit, d, s)
}

fn dsl_compress(
    builder: &mut CircuitBuilder<Challenge>,
    x: [ExprId; DIGEST_EXT],
    y: [ExprId; DIGEST_EXT],
) -> [ExprId; DIGEST_EXT] {
    let inputs: Vec<Option<ExprId>> = x.iter().chain(y.iter()).map(|&e| Some(e)).collect();
    assert_eq!(inputs.len(), WIDTH_EXT);
    let (_op, outputs) = builder
        .add_poseidon2_perm(&Poseidon2PermCall {
            config: Poseidon2Config::KOALA_BEAR_D4_W32,
            new_start: true,
            merkle_path: false,
            mmcs_bit: None,
            mmcs_bit2: None,
            inputs,
            out_ctl: vec![true; RATE_EXT],
            return_all_outputs: true,
            mmcs_index_sum: None,
            absorb_len: 0,
        })
        .expect("W32 compress wiring");
    core::array::from_fn(|i| outputs[i].expect("digest limb present (out_ctl true)"))
}

fn milestone_0() {
    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    let a = builder.alloc_public_input("a");
    let b = builder.alloc_public_input("b");
    builder.connect(a, b);
    let circuit = builder.build().expect("empty circuit builds");
    let _runner = circuit.runner();
    println!(
        "M0 OK: frozen Plonky3-recursion fork resolves; CircuitBuilder<Ext4> builds end to end."
    );
}

fn milestone_1a() {
    let input: [Val; WIDTH] = core::array::from_fn(|i| Val::from_u64((i + 1) as u64));
    let x: [Val; DIGEST] = core::array::from_fn(|i| input[i]);
    let y: [Val; DIGEST] = core::array::from_fn(|i| input[DIGEST + i]);

    let perm = default_koalabear_poseidon2_32();
    let native_digest = compress(&perm, &x, &y);

    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    builder.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD4Width32>,
        perm.clone(),
    );
    builder.enable_recompose::<Val>(generate_recompose_trace::<Val, Challenge>);

    let ex = alloc_block(&mut builder, &x, "node_l");
    let ey = alloc_block(&mut builder, &y, "node_r");
    let digest = dsl_compress(&mut builder, ex, ey);

    let circuit = builder.build().expect("M1a circuit builds");
    let expr_to_widx = circuit.expr_to_widx.clone();
    let traces = circuit.runner().run().expect("M1a circuit runs");
    let get_val = |e: ExprId| -> Challenge {
        let wid = *expr_to_widx.get(&e).expect("witness id for expr");
        *traces.witness_trace.get_value(wid).expect("witness value")
    };
    let circuit_digest = read_digest(&get_val, &digest);

    assert_eq!(
        circuit_digest, native_digest,
        "M1a FAILED: DSL W32 compression != native KoalaBear Poseidon2"
    );
    println!(
        "M1a OK: DSL W32 2-to-1 compression == native KoalaBear Poseidon2 (16-element digest)."
    );
}

fn milestone_1b() {
    let perm = default_koalabear_poseidon2_32();

    let k: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64((100 + i) as u64));
    let b: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64((200 + i) as u64));
    let v: u64 = 500;

    let o_pubkey = oracle_pubkey(&perm, &k);
    let o_image = oracle_image(&perm, &k);
    let o_leaf = oracle_commit(&perm, &o_pubkey, v, &b);
    assert_ne!(
        o_pubkey, o_image,
        "oracle sanity: pubkey and image domains must separate the same secret"
    );

    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    builder.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD4Width32>,
        perm.clone(),
    );
    builder.enable_recompose::<Val>(generate_recompose_trace::<Val, Challenge>);

    let e_k = alloc_block(&mut builder, &k, "k");
    let e_b = alloc_block(&mut builder, &b, "b");
    let e_vblock = alloc_block(&mut builder, &v_block(v), "v_block");
    let e_dom_pubkey = alloc_block(&mut builder, &dom16(b"blocknet_pubkey"), "dom_pubkey");
    let e_dom_image = alloc_block(&mut builder, &dom16(b"blocknet_image"), "dom_image");
    let e_dom_commit = alloc_block(&mut builder, &dom16(b"blocknet_commit"), "dom_commit");

    let d_pubkey = dsl_compress(&mut builder, e_dom_pubkey, e_k);
    let d_image = dsl_compress(&mut builder, e_dom_image, e_k);
    let s1 = dsl_compress(&mut builder, e_dom_commit, d_pubkey);
    let s2 = dsl_compress(&mut builder, s1, e_vblock);
    let d_leaf = dsl_compress(&mut builder, s2, e_b);

    let circuit = builder.build().expect("M1b circuit builds");
    let expr_to_widx = circuit.expr_to_widx.clone();
    let traces = circuit.runner().run().expect("M1b circuit runs");
    let get_val = |e: ExprId| -> Challenge {
        let wid = *expr_to_widx.get(&e).expect("witness id for expr");
        *traces.witness_trace.get_value(wid).expect("witness value")
    };

    let c_pubkey = read_digest(&get_val, &d_pubkey);
    let c_image = read_digest(&get_val, &d_image);
    let c_leaf = read_digest(&get_val, &d_leaf);

    assert_eq!(c_pubkey, o_pubkey, "M1b FAILED: DSL H_pubkey != oracle");
    assert_eq!(c_image, o_image, "M1b FAILED: DSL H_image != oracle");
    assert_eq!(c_leaf, o_leaf, "M1b FAILED: DSL commit(leaf) != oracle");
    println!(
        "M1b OK: DSL H_pubkey / H_image / commit == option-B oracle (16-element, \
         domain-in-message); pubkey and image domains separate."
    );
}

fn milestone_2() {
    let perm = default_koalabear_poseidon2_32();

    let k: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64((100 + i) as u64));
    let b: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64((200 + i) as u64));
    let k_pub = oracle_pubkey(&perm, &k);
    let leaf = oracle_commit(&perm, &k_pub, 500, &b);

    let siblings: Vec<[Val; DIGEST]> = (0..DEPTH)
        .map(|d| core::array::from_fn(|i| Val::from_u64((1000 + (d * DIGEST + i)) as u64)))
        .collect();
    let bits: Vec<bool> = (0..DEPTH).map(|d| d % 3 == 0 || d % 2 == 1).collect();

    let native_root = fold_native(&perm, &leaf, &siblings, &bits);

    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    builder.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD4Width32>,
        perm.clone(),
    );
    builder.enable_recompose::<Val>(generate_recompose_trace::<Val, Challenge>);

    let mut running = alloc_block(&mut builder, &leaf, "leaf");
    let mut pub_vals: Vec<Challenge> = Vec::with_capacity(DEPTH * (DIGEST_EXT + 1));
    for d in 0..DEPTH {
        let sib: [ExprId; DIGEST_EXT] =
            core::array::from_fn(|_| builder.alloc_public_input("sib"));
        let bit = builder.alloc_public_input("pos_bit");
        builder.assert_bool(bit);
        let left: [ExprId; DIGEST_EXT] =
            core::array::from_fn(|i| mux(&mut builder, bit, sib[i], running[i]));
        let right: [ExprId; DIGEST_EXT] =
            core::array::from_fn(|i| mux(&mut builder, bit, running[i], sib[i]));
        running = dsl_compress(&mut builder, left, right);

        pub_vals.extend_from_slice(&pack16(&siblings[d]));
        pub_vals.push(if bits[d] { Challenge::ONE } else { Challenge::ZERO });
    }

    let circuit = builder.build().expect("M2 circuit builds");
    let expr_to_widx = circuit.expr_to_widx.clone();
    let mut runner = circuit.runner();
    runner
        .set_public_inputs(&pub_vals)
        .expect("set M2 public inputs");
    let traces = runner.run().expect("M2 circuit runs");
    let get_val = |e: ExprId| -> Challenge {
        let wid = *expr_to_widx.get(&e).expect("witness id for expr");
        *traces.witness_trace.get_value(wid).expect("witness value")
    };
    let circuit_root = read_digest(&get_val, &running);

    assert_eq!(
        circuit_root, native_root,
        "M2 FAILED: DSL depth-32 fold root != native option-B root"
    );
    println!(
        "M2 OK: DSL depth-{DEPTH} binary Merkle fold, position-bit mux + assert_bool \
         == native option-B root."
    );
}

fn milestone_3() {
    const IN: usize = 2;
    const OUT: usize = 2;
    let vin = [500u64, 300];
    let vout = [600u64, 190];
    let fee = 10u64;

    let limb = |v: u64, k: usize| (v >> (16 * k)) & 0xffff;
    let cf = |x: i64| -> Challenge {
        if x >= 0 {
            Challenge::from_u64(x as u64)
        } else {
            -Challenge::from_u64((-x) as u64)
        }
    };

    let base_i = 1i64 << LIMB_BITS;
    let mut carries = Vec::new();
    let mut carry = 0i64;
    for k in 0..NLIMBS {
        let sin: i64 = (0..IN).map(|i| limb(vin[i], k) as i64).sum();
        let sout: i64 = (0..OUT).map(|j| limb(vout[j], k) as i64).sum();
        let diff = sin - sout - limb(fee, k) as i64 + carry;
        if k + 1 < NLIMBS {
            assert_eq!(diff % base_i, 0, "native balance: limb {k} does not carry cleanly");
            carry = diff / base_i;
            carries.push(carry);
        } else {
            assert_eq!(diff, 0, "native balance: top limb must close to zero");
        }
    }

    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    let mut priv_vals: Vec<Challenge> = Vec::new();
    let mut pub_vals: Vec<Challenge> = Vec::new();

    let mut vin_e: Vec<ExprId> = Vec::new();
    for i in 0..IN {
        for k in 0..NLIMBS {
            vin_e.push(builder.alloc_private_input("vin_limb"));
            priv_vals.push(Challenge::from_u64(limb(vin[i], k)));
        }
    }
    let mut vout_e: Vec<ExprId> = Vec::new();
    for j in 0..OUT {
        for k in 0..NLIMBS {
            vout_e.push(builder.alloc_private_input("vout_limb"));
            priv_vals.push(Challenge::from_u64(limb(vout[j], k)));
        }
    }
    let mut carry_e: Vec<ExprId> = Vec::new();
    for &c in &carries {
        carry_e.push(builder.alloc_private_input("carry"));
        priv_vals.push(cf(c));
    }
    let mut fee_e: Vec<ExprId> = Vec::new();
    for k in 0..NLIMBS {
        fee_e.push(builder.alloc_public_input("fee_limb"));
        pub_vals.push(Challenge::from_u64(limb(fee, k)));
    }

    for &e in vin_e.iter().chain(vout_e.iter()).chain(fee_e.iter()) {
        builder
            .decompose_to_bits::<Val>(e, LIMB_BITS)
            .expect("16-bit range check");
    }

    let base_c = builder.alloc_const(Challenge::from_u64(1 << LIMB_BITS), "base");
    let off_c = builder.alloc_const(Challenge::from_u64(CARRY_OFF), "carry_off");
    let mut carry_in: Option<ExprId> = None;
    for k in 0..NLIMBS {
        let mut sin = vin_e[k];
        for i in 1..IN {
            sin = builder.add(sin, vin_e[i * NLIMBS + k]);
        }
        let mut sout = vout_e[k];
        for j in 1..OUT {
            sout = builder.add(sout, vout_e[j * NLIMBS + k]);
        }
        let mut diff = builder.sub(sin, sout);
        diff = builder.sub(diff, fee_e[k]);
        if let Some(ci) = carry_in {
            diff = builder.add(diff, ci);
        }
        if k + 1 < NLIMBS {
            let cb = builder.mul(carry_e[k], base_c);
            let residual = builder.sub(diff, cb);
            builder.assert_zero(residual);
            let off_val = builder.add(carry_e[k], off_c);
            builder
                .decompose_to_bits::<Val>(off_val, CARRY_BITS)
                .expect("carry range check");
            carry_in = Some(carry_e[k]);
        } else {
            builder.assert_zero(diff);
        }
    }

    let circuit = builder.build().expect("M3 circuit builds");

    let ok = {
        let mut runner = circuit.runner();
        runner.set_private_inputs(&priv_vals).expect("set M3 private");
        runner.set_public_inputs(&pub_vals).expect("set M3 public");
        runner.run()
    };
    assert!(ok.is_ok(), "M3 FAILED: balancing tx should run, got {:?}", ok.err());

    let bad = {
        let mut bad_pub = pub_vals.clone();
        bad_pub[0] = bad_pub[0] + Challenge::ONE;
        let mut runner = circuit.runner();
        runner.set_private_inputs(&priv_vals).expect("set M3 private");
        runner.set_public_inputs(&bad_pub).expect("set M3 public");
        runner.run()
    };
    assert!(bad.is_err(), "M3 FAILED: unbalanced tx should be rejected, but it ran");

    println!(
        "M3 OK: DSL limbed balance + 16-bit range checks accept a balancing tx and reject an \
         unbalanced one."
    );
}

fn milestone_4a() {
    let perm = default_koalabear_poseidon2_32();
    let input: [Val; WIDTH] = core::array::from_fn(|i| Val::from_u64((i + 1) as u64));
    let x: [Val; DIGEST] = core::array::from_fn(|i| input[i]);
    let y: [Val; DIGEST] = core::array::from_fn(|i| input[DIGEST + i]);

    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    builder.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD4Width32>,
        perm.clone(),
    );
    builder.enable_recompose::<Val>(generate_recompose_trace::<Val, Challenge>);
    let ex = alloc_block(&mut builder, &x, "node_l");
    let ey = alloc_block(&mut builder, &y, "node_r");
    let _digest = dsl_compress(&mut builder, ex, ey);
    let circuit = builder.build().expect("M4a circuit builds");

    let stark_config = config::koala_bear();
    let table_packing = TablePacking::new(4, 4);
    let poseidon2_config = Poseidon2Config::KOALA_BEAR_D4_W32;
    let npo_prep: Vec<Box<dyn NpoPreprocessor<Val>>> = vec![
        Box::new(Poseidon2Preprocessor),
        Box::new(RecomposePreprocessor::default()),
    ];
    let mut air_builders = poseidon2_air_builders::<_, 4>();
    air_builders.extend(recompose_air_builders(1, false));
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<KoalaBearConfig, _, 4>(
            &circuit,
            &table_packing,
            &npo_prep,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .expect("derive airs + preprocessed columns");

    let traces = circuit.runner().run().expect("M4a circuit runs");

    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&stark_config, &airs, &degrees).expect("prover data");
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let mut prover = BatchStarkProver::new(stark_config).with_table_packing(table_packing);
    prover.register_poseidon2_table::<4>(poseidon2_config);
    prover.register_recompose_table::<4>(false);

    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .expect("prove all tables");
    prover
        .verify_all_tables::<Challenge>(&proof)
        .expect("verify all tables");

    let bytes = postcard::to_allocvec(&proof).map(|v| v.len()).unwrap_or(0);
    println!(
        "M4a OK: batch-STARK prove + verify of the W32 compression circuit ({} bytes serialized).",
        bytes
    );
}

fn prove_and_verify(
    circuit: &p3_circuit::Circuit<Challenge>,
    traces: &p3_circuit::Traces<Challenge>,
) -> Result<usize, String> {
    let stark_config = config::koala_bear();
    let table_packing = TablePacking::new(4, 4);
    let npo_prep: Vec<Box<dyn NpoPreprocessor<Val>>> = vec![
        Box::new(Poseidon2Preprocessor),
        Box::new(RecomposePreprocessor::default()),
    ];
    let mut air_builders = poseidon2_air_builders::<_, 4>();
    air_builders.extend(recompose_air_builders(1, false));
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<KoalaBearConfig, _, 4>(
            circuit,
            &table_packing,
            &npo_prep,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .expect("airs");
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&stark_config, &airs, &degrees).expect("prover data");
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    let mut prover = BatchStarkProver::new(stark_config).with_table_packing(table_packing);
    prover.register_poseidon2_table::<4>(Poseidon2Config::KOALA_BEAR_D4_W32);
    prover.register_recompose_table::<4>(false);
    let proof = prover
        .prove_all_tables(traces, &circuit_prover_data)
        .expect("prove");
    prover
        .verify_all_tables::<Challenge>(&proof)
        .map_err(|e| format!("{e:?}"))?;
    Ok(postcard::to_allocvec(&proof).map(|v| v.len()).unwrap_or(0))
}

struct Io {
    priv_vals: Vec<Challenge>,
    pub_vals: Vec<Challenge>,
    marks: Vec<(&'static str, ExprId)>,
}
impl Io {
    fn new() -> Self {
        Self { priv_vals: Vec::new(), pub_vals: Vec::new(), marks: Vec::new() }
    }
    fn mark(&mut self, label: &'static str, exprs: &[ExprId]) {
        self.marks.extend(exprs.iter().map(|&e| (label, e)));
    }
    fn priv_block(
        &mut self,
        b: &mut CircuitBuilder<Challenge>,
        vals: &[Val; DIGEST],
        label: &'static str,
    ) -> [ExprId; DIGEST_EXT] {
        let limbs = pack16(vals);
        let out: [ExprId; DIGEST_EXT] = core::array::from_fn(|i| {
            self.priv_vals.push(limbs[i]);
            b.alloc_private_input(label)
        });
        self.mark(label, &out);
        out
    }
    fn priv_scalar(
        &mut self,
        b: &mut CircuitBuilder<Challenge>,
        v: Challenge,
        label: &'static str,
    ) -> ExprId {
        self.priv_vals.push(v);
        let e = b.alloc_private_input(label);
        self.mark(label, &[e]);
        e
    }
    fn pub_block(
        &mut self,
        b: &mut CircuitBuilder<Challenge>,
        vals: &[Val; DIGEST],
        label: &'static str,
    ) -> [ExprId; DIGEST_EXT] {
        let limbs = pack16(vals);
        core::array::from_fn(|i| {
            self.pub_vals.push(limbs[i]);
            b.alloc_public_input(label)
        })
    }
    fn pub_scalar(
        &mut self,
        b: &mut CircuitBuilder<Challenge>,
        v: Challenge,
        label: &'static str,
    ) -> ExprId {
        self.pub_vals.push(v);
        b.alloc_public_input(label)
    }
}

fn build_spend_circuit(seed: u64) -> (p3_circuit::Circuit<Challenge>, Io) {
    let perm = default_koalabear_poseidon2_32();
    let s = seed * 1000;

    let k: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(s + 100 + i as u64));
    let b_in: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(s + 200 + i as u64));
    let v: u64 = 500;
    let k_pub = oracle_pubkey(&perm, &k);
    let image = oracle_image(&perm, &k);
    let leaf = oracle_commit(&perm, &k_pub, v, &b_in);
    let siblings: Vec<[Val; DIGEST]> = (0..DEPTH)
        .map(|d| core::array::from_fn(|i| Val::from_u64((1000 + (d * DIGEST + i)) as u64)))
        .collect();
    let bits: Vec<bool> = (0..DEPTH).map(|d| d % 3 == 0 || d % 2 == 1).collect();
    let root = fold_native(&perm, &leaf, &siblings, &bits);

    let kk_out: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(s + 300 + i as u64));
    let b_out: [Val; DIGEST] = core::array::from_fn(|i| Val::from_u64(s + 400 + i as u64));
    let o: u64 = 500;
    let fee: u64 = 0;
    let commit_out = oracle_commit(&perm, &kk_out, o, &b_out);

    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    builder.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD4Width32>,
        perm.clone(),
    );
    builder.enable_recompose::<Val>(generate_recompose_trace::<Val, Challenge>);
    let mut io = Io::new();
    let one_c = builder.alloc_const(Challenge::ONE, "one");

    let dom_pk = alloc_block(&mut builder, &dom16(b"blocknet_pubkey"), "dom_pubkey");
    let dom_im = alloc_block(&mut builder, &dom16(b"blocknet_image"), "dom_image");
    let dom_cm = alloc_block(&mut builder, &dom16(b"blocknet_commit"), "dom_commit");

    let e_k_raw = io.priv_block(&mut builder, &k, "k");
    let e_k = wire_block(&mut builder, &e_k_raw, one_c);
    io.mark("k", &e_k);
    let e_b_in_raw = io.priv_block(&mut builder, &b_in, "b_in");
    let e_b_in = wire_block(&mut builder, &e_b_in_raw, one_c);
    io.mark("b_in", &e_b_in);
    let v_limbs: [ExprId; NLIMBS] =
        core::array::from_fn(|kk| io.priv_scalar(&mut builder, amount_limb(v, kk), "v_limb"));
    let v_limbs_w: [ExprId; NLIMBS] =
        core::array::from_fn(|kk| wire_scalar(&mut builder, v_limbs[kk], one_c));
    let e_cap = dsl_compress(&mut builder, dom_pk, e_k);
    let e_img = dsl_compress(&mut builder, dom_im, e_k);
    let s1 = dsl_compress(&mut builder, dom_cm, e_cap);
    let s2 = dsl_compress(&mut builder, s1, v_limbs_w);
    let mut running = dsl_compress(&mut builder, s2, e_b_in);
    io.mark("leaf", &running);
    io.mark("key_image", &e_img);
    for &e in v_limbs.iter() {
        builder.decompose_to_bits::<Val>(e, LIMB_BITS).expect("v range");
    }

    for d in 0..DEPTH {
        let sib_raw = io.priv_block(&mut builder, &siblings[d], "sib");
        let sib = wire_block(&mut builder, &sib_raw, one_c);
        let bit = io.priv_scalar(
            &mut builder,
            if bits[d] { Challenge::ONE } else { Challenge::ZERO },
            "pos_bit",
        );
        builder.assert_bool(bit);
        let left: [ExprId; DIGEST_EXT] =
            core::array::from_fn(|i| mux(&mut builder, bit, sib[i], running[i]));
        let right: [ExprId; DIGEST_EXT] =
            core::array::from_fn(|i| mux(&mut builder, bit, running[i], sib[i]));
        running = dsl_compress(&mut builder, left, right);
    }

    let pub_image = io.pub_block(&mut builder, &image, "key_image");
    let pub_root = io.pub_block(&mut builder, &root, "root");
    for i in 0..DIGEST_EXT {
        builder.connect(e_img[i], pub_image[i]);
        builder.connect(running[i], pub_root[i]);
    }

    let e_kk_out_raw = io.priv_block(&mut builder, &kk_out, "kk_out");
    let e_kk_out = wire_block(&mut builder, &e_kk_out_raw, one_c);
    io.mark("kk_out", &e_kk_out);
    let e_b_out_raw = io.priv_block(&mut builder, &b_out, "b_out");
    let e_b_out = wire_block(&mut builder, &e_b_out_raw, one_c);
    io.mark("b_out", &e_b_out);
    let o_limbs: [ExprId; NLIMBS] =
        core::array::from_fn(|kk| io.priv_scalar(&mut builder, amount_limb(o, kk), "o_limb"));
    let o_limbs_w: [ExprId; NLIMBS] =
        core::array::from_fn(|kk| wire_scalar(&mut builder, o_limbs[kk], one_c));
    let os1 = dsl_compress(&mut builder, dom_cm, e_kk_out);
    let os2 = dsl_compress(&mut builder, os1, o_limbs_w);
    let e_commit = dsl_compress(&mut builder, os2, e_b_out);
    io.mark("commit_out", &e_commit);
    for &e in o_limbs.iter() {
        builder.decompose_to_bits::<Val>(e, LIMB_BITS).expect("o range");
    }
    let pub_commit = io.pub_block(&mut builder, &commit_out, "commitment");
    for i in 0..DIGEST_EXT {
        builder.connect(e_commit[i], pub_commit[i]);
    }

    let fee_e: [ExprId; NLIMBS] =
        core::array::from_fn(|kk| io.pub_scalar(&mut builder, amount_limb(fee, kk), "fee_limb"));
    for &e in fee_e.iter() {
        builder.decompose_to_bits::<Val>(e, LIMB_BITS).expect("fee range");
    }
    let base_c = builder.alloc_const(Challenge::from_u64(1 << LIMB_BITS), "base");
    let off_c = builder.alloc_const(Challenge::from_u64(CARRY_OFF), "carry_off");
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
            let cf = if c >= 0 {
                Challenge::from_u64(c as u64)
            } else {
                -Challenge::from_u64((-c) as u64)
            };
            io.priv_scalar(&mut builder, cf, "carry")
        })
        .collect();
    let mut carry_in: Option<ExprId> = None;
    for kk in 0..NLIMBS {
        let mut diff = builder.sub(v_limbs[kk], o_limbs[kk]);
        diff = builder.sub(diff, fee_e[kk]);
        if let Some(ci) = carry_in {
            diff = builder.add(diff, ci);
        }
        if kk + 1 < NLIMBS {
            let cb = builder.mul(carry_e[kk], base_c);
            let residual = builder.sub(diff, cb);
            builder.assert_zero(residual);
            let off_val = builder.add(carry_e[kk], off_c);
            builder
                .decompose_to_bits::<Val>(off_val, CARRY_BITS)
                .expect("carry range");
            carry_in = Some(carry_e[kk]);
        } else {
            builder.assert_zero(diff);
        }
    }

    let circuit = builder.build().expect("M4b circuit builds");

    (circuit, io)
}

fn milestone_4b() {
    let (circuit, io) = build_spend_circuit(0);
    let traces = {
        let mut runner = circuit.runner();
        runner
            .set_private_inputs(&io.priv_vals)
            .expect("set M4b private");
        runner.set_public_inputs(&io.pub_vals).expect("set M4b public");
        runner.run().expect("M4b spend circuit runs (valid tx)")
    };
    let bytes = prove_and_verify(&circuit, &traces).expect("M4b prove + verify");
    println!(
        "M4b OK: full 1-in/1-out spend (K/I/leaf + depth-{DEPTH} membership + commit + range + \
         balance) proves and verifies. Base proof: {bytes} bytes ({:.1} KB) at the default FRI \
         config (untuned).",
        bytes as f64 / 1024.0
    );
}

fn read_digest(
    get_val: impl Fn(ExprId) -> Challenge,
    digest_exprs: &[ExprId; DIGEST_EXT],
) -> [Val; DIGEST] {
    let mut out = [Val::ZERO; DIGEST];
    for (limb_idx, &expr) in digest_exprs.iter().enumerate() {
        let limb = get_val(expr);
        for (j, coeff) in unpack(&limb).into_iter().enumerate() {
            out[limb_idx * LIMB + j] = coeff;
        }
    }
    out
}

fn set_proof_mmcs(
    runner: &mut CircuitRunner<'_, rec::Challenge>,
    fold_config: &rec::MyConfig,
    shape: rec::FriShape,
    input: &FoldInput,
    op_ids: &[NonPrimitiveOpId],
) -> Result<(), String> {
    let err = |e: &dyn std::fmt::Debug| format!("{e:?}");
    let (plain_tree, fri_params) = rec::fri_instance(shape);
    let query_paths = match *input {
        FoldInput::Spend { proof, key } => {
            let OpeningTranscript { mut challenger, mut commitments_with_opening_points } =
                replay_batch_layer_transcript::<rec::ZkConfig, 4>(&rec::make_zk_config(key.shape), proof, key.cpd.common_data(), &spend_nps())
                    .map_err(|e| err(&e))?;
            p3_recursion::merge_hiding_random_openings::<rec::ZkConfig>(
                &mut commitments_with_opening_points,
                &proof.proof.opening_proof.0,
            )
            .map_err(|e| err(&e))?;
            observe_opened_values::<rec::ZkConfig>(&mut challenger, &commitments_with_opening_points, fri_params.batch_proof_of_work_bits);
            let claims: Vec<_> = commitments_with_opening_points.iter().cloned().map(Into::into).collect();
            let (hiding_mmcs, zk_fri_params) = rec::zk_fri_instance(shape);
            p3_recursion::pcs::restore_hiding_fri_query_paths(
                &zk_fri_params,
                &hiding_mmcs,
                &plain_tree,
                &plain_tree,
                &proof.proof.opening_proof.1,
                &mut challenger,
                &claims,
            )
            .map_err(|e| err(&e))?
        }
        FoldInput::Fold { proof, common } => {
            let OpeningTranscript { mut challenger, commitments_with_opening_points } =
                replay_batch_layer_transcript::<rec::MyConfig, 4>(fold_config, proof, common, &fold_nps())
                    .map_err(|e| err(&e))?;
            observe_opened_values::<rec::MyConfig>(&mut challenger, &commitments_with_opening_points, fri_params.batch_proof_of_work_bits);
            let claims: Vec<_> = commitments_with_opening_points.iter().cloned().map(Into::into).collect();
            restore_fri_query_paths(&fri_params, &plain_tree, &plain_tree, &proof.proof.opening_proof, &mut challenger, &claims)
                .map_err(|e| err(&e))?
        }
    };
    set_fri_mmcs_private_data::<rec::F, rec::Challenge, 8>(runner, op_ids, &query_paths, Poseidon2Config::KOALA_BEAR_D4_W16)
        .map_err(|e| err(&e))
}

pub const D4_SHAPE: rec::FriShape =
    rec::FriShape { log_blowup: 4, max_log_arity: 4, num_queries: 56 };
pub const FEASIBILITY_SHAPE: rec::FriShape =
    rec::FriShape { log_blowup: 3, max_log_arity: 4, num_queries: 28 };

fn spend_table_packing(shape: rec::FriShape) -> TablePacking {
    let min_rows = (2 * (4 * 2 + shape.num_queries)).next_power_of_two();
    TablePacking::new(4, 4).with_min_trace_height(min_rows)
}

fn fold_table_packing() -> TablePacking {
    TablePacking::new(1, 8)
}

fn spend_nps() -> Vec<Box<dyn TableProver<rec::ZkConfig>>> {
    poseidon2_table_provers_d4::<rec::ZkConfig>(Poseidon2Config::KOALA_BEAR_D4_W32)
}

fn fold_nps() -> Vec<Box<dyn TableProver<rec::MyConfig>>> {
    let mut v = poseidon2_table_provers_d4::<rec::MyConfig>(
        Poseidon2Config::KOALA_BEAR_D4_W16.for_challenger(),
    );
    v.extend(poseidon2_table_provers_d4::<rec::MyConfig>(Poseidon2Config::KOALA_BEAR_D4_W16));
    v.push(Box::new(p3_circuit_prover::RecomposeProver::<4>::new(1, true)));
    v
}

pub type SpendProof = BatchStarkProof<rec::ZkConfig>;
pub type FoldProof = BatchStarkProof<rec::MyConfig>;

macro_rules! proof_codec {
    ($enc:ident, $dec:ident, $commit:ident, $sc:ty) => {
        pub fn $enc(p: &BatchStarkProof<$sc>) -> Vec<u8> {
            postcard::to_allocvec(p).expect("serialize proof")
        }

        pub fn $dec(bytes: &[u8]) -> Result<BatchStarkProof<$sc>, String> {
            let proof: BatchStarkProof<$sc> =
                postcard::from_bytes(bytes).map_err(|e| format!("decode: {e}"))?;
            if $enc(&proof) != bytes {
                return Err("decode: not the canonical encoding".into());
            }
            Ok(proof)
        }

        fn $commit(common: &p3_batch_stark::CommonData<$sc>) -> Vec<u8> {
            let pre = common.preprocessed.as_ref().expect("preprocessed commitment");
            postcard::to_allocvec(&pre.commitment).expect("serialize commitment")
        }
    };
}

proof_codec!(encode_proof, decode_proof, preprocessed_commitment, rec::MyConfig);
proof_codec!(encode_spend, decode_spend, spend_commitment, rec::ZkConfig);

pub struct SpendKey {
    shape: rec::FriShape,
    cpd: CircuitProverData<rec::ZkConfig>,
    commitment: Vec<u8>,
    airs: Vec<CircuitTableAir<rec::ZkConfig, 4>>,
}

pub fn spend_key(shape: rec::FriShape) -> &'static SpendKey {
    static KEYS: std::sync::Mutex<Vec<(rec::FriShape, &'static SpendKey)>> = std::sync::Mutex::new(Vec::new());
    let mut keys = KEYS.lock().expect("spend key cache");
    if let Some((_, k)) = keys.iter().find(|(s, _)| *s == shape) {
        return k;
    }
    let k: &'static SpendKey = Box::leak(Box::new(generate_spend_key(shape)));
    keys.push((shape, k));
    k
}

fn generate_spend_key(shape: rec::FriShape) -> SpendKey {
    let config = rec::keygen_zk_config(shape);
    let (circuit, _io) = build_spend_circuit(0);
    let npo_prep: Vec<Box<dyn NpoPreprocessor<Val>>> = vec![
        Box::new(Poseidon2Preprocessor),
        Box::new(RecomposePreprocessor::default()),
    ];
    let mut air_builders = poseidon2_air_builders::<_, 4>();
    air_builders.extend(recompose_air_builders(1, false));
    let (airs_degrees, prim, nonprim) = get_airs_and_degrees_with_prep::<rec::ZkConfig, Challenge, 4>(
        &circuit,
        &spend_table_packing(shape),
        &npo_prep,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .expect("spend airs");
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    let zk = <rec::ZkConfig as p3_uni_stark::StarkGenericConfig>::is_zk(&config);
    let degrees: Vec<usize> = degrees.iter().map(|d| d + zk).collect();
    let prover_data =
        ProverData::from_airs_and_degrees(&config, &airs, &degrees).expect("spend prover data");
    let cpd = CircuitProverData::new(prover_data, prim, nonprim);
    let commitment = spend_commitment(cpd.common_data());
    SpendKey { shape, cpd, commitment, airs }
}

impl SpendKey {
    fn prover(&self) -> BatchStarkProver<rec::ZkConfig> {
        let mut prover = BatchStarkProver::new(rec::make_zk_config(self.shape)).with_table_packing(spend_table_packing(self.shape));
        prover.register_poseidon2_table::<4>(Poseidon2Config::KOALA_BEAR_D4_W32);
        prover.register_recompose_table::<4>(false);
        prover
    }

    pub fn verifier(&self) -> SpendVerifier {
        SpendVerifier { shape: self.shape, commitment: self.commitment.clone() }
    }

    pub fn accepts(&self, proof: &SpendProof) -> Result<(), String> {
        self.verifier().accepts(proof)
    }

    pub fn accepts_bytes(&self, bytes: &[u8]) -> Result<(), String> {
        self.accepts(&decode_spend(bytes)?)
    }
}

pub struct SpendVerifier {
    shape: rec::FriShape,
    commitment: Vec<u8>,
}

impl SpendVerifier {
    pub fn new(shape: rec::FriShape, commitment: Vec<u8>) -> Self {
        SpendVerifier { shape, commitment }
    }

    pub fn commitment(&self) -> &[u8] {
        &self.commitment
    }

    pub fn accepts(&self, proof: &SpendProof) -> Result<(), String> {
        if spend_commitment(&proof.stark_common) != self.commitment {
            return Err("proof is not for the canonical spend circuit".into());
        }
        let mut verifier = BatchStarkProver::new(rec::make_zk_config(self.shape))
            .with_table_packing(spend_table_packing(self.shape));
        verifier.register_poseidon2_table::<4>(Poseidon2Config::KOALA_BEAR_D4_W32);
        verifier.register_recompose_table::<4>(false);
        verifier.verify_all_tables::<Challenge>(proof).map_err(|e| format!("{e:?}"))
    }

    pub fn accepts_bytes(&self, bytes: &[u8]) -> Result<(), String> {
        self.accepts(&decode_spend(bytes)?)
    }
}

fn spend_traces(seed: u64) -> p3_circuit::Traces<Challenge> {
    let (circuit, io) = build_spend_circuit(seed);
    let mut r = circuit.runner();
    r.set_private_inputs(&io.priv_vals).expect("spend private inputs");
    r.set_public_inputs(&io.pub_vals).expect("spend public inputs");
    r.run().expect("spend runs")
}

fn prove_spend(key: &SpendKey, seed: u64) -> SpendProof {
    let proof = key
        .prover()
        .prove_all_tables(&spend_traces(seed), &key.cpd)
        .expect("prove spend");
    key.accepts_bytes(&encode_spend(&proof))
        .expect("spend proof verifies against the spend key");
    proof
}

fn num_tables<SC: p3_uni_stark::StarkGenericConfig>(common: &p3_batch_stark::CommonData<SC>) -> usize {
    common.preprocessed.as_ref().map(|g| g.instances.len()).unwrap_or(0)
}

#[derive(Clone, Copy)]
pub enum FoldInput<'a> {
    Spend { proof: &'a SpendProof, key: &'a SpendKey },
    Fold { proof: &'a FoldProof, common: &'a p3_batch_stark::CommonData<rec::MyConfig> },
}

impl FoldInput<'_> {
    fn layer(&self) -> &'static str {
        match self {
            FoldInput::Spend { .. } => "Spend",
            FoldInput::Fold { .. } => "Fold",
        }
    }
}

struct FoldCircuit {
    circuit: p3_circuit::Circuit<rec::Challenge>,
    public: Vec<rec::Challenge>,
    private: Vec<rec::Challenge>,
    op_ids: Vec<Vec<NonPrimitiveOpId>>,
}

fn build_fold_circuit(fold_config: &rec::MyConfig, shape: rec::FriShape, inputs: &[FoldInput]) -> FoldCircuit {
    let mut vcircuit = CircuitBuilder::<rec::Challenge>::new();
    vcircuit.enable_poseidon2_perm::<KoalaBearD4Width16, _>(
        generate_poseidon2_trace::<rec::Challenge, KoalaBearD4Width16>,
        default_koalabear_poseidon2_16(),
    );
    vcircuit.enable_recompose::<rec::F>(generate_recompose_trace::<rec::F, rec::Challenge>);
    let fri_vp = FriVerifierParams::with_mmcs(
        shape.log_blowup,
        0,
        shape.max_log_arity,
        0,
        rec::QUERY_POW_BITS,
        shape.num_queries,
        Poseidon2Config::KOALA_BEAR_D4_W16,
    );
    let lookup_gadget = LogUpGadget::new();
    let (snps, fnps) = (spend_nps(), fold_nps());
    let mut public = Vec::new();
    let mut private = Vec::new();
    let mut op_ids = Vec::new();
    for input in inputs {
        let (pb, pv, op) = match *input {
            FoldInput::Spend { proof, key } => {
                let common = key.cpd.common_data();
                let (vi, op) = verify_p3_batch_proof_circuit::<
                    rec::ZkConfig,
                    MerkleCapTargets<rec::F, 8>,
                    InputProofTargets<rec::F, rec::Challenge, rec::RecHidingValMmcs>,
                    rec::InnerFriZk,
                    LogUpGadget,
                    _,
                    16,
                    8,
                    4,
                >(&rec::make_zk_config(key.shape), &mut vcircuit, proof, &fri_vp, common, &lookup_gadget, Poseidon2Config::KOALA_BEAR_D4_W16, &snps)
                .expect("in-circuit verifier builds");
                let pis: Vec<Vec<rec::F>> = vec![vec![]; num_tables(common)];
                let (pb, pv) = vi.pack_values(&pis, &proof.proof, common);
                (pb, pv, op)
            }
            FoldInput::Fold { proof, common } => {
                let (vi, op) = verify_p3_batch_proof_circuit::<
                    rec::MyConfig,
                    MerkleCapTargets<rec::F, 8>,
                    InputProofTargets<rec::F, rec::Challenge, RecValMmcs<rec::F, 8, rec::MyHash, rec::MyCompress>>,
                    rec::InnerFri,
                    LogUpGadget,
                    _,
                    16,
                    8,
                    4,
                >(fold_config, &mut vcircuit, proof, &fri_vp, common, &lookup_gadget, Poseidon2Config::KOALA_BEAR_D4_W16, &fnps)
                .expect("in-circuit verifier builds");
                let pis: Vec<Vec<rec::F>> = vec![vec![]; num_tables(common)];
                let (pb, pv) = vi.pack_values(&pis, &proof.proof, common);
                (pb, pv, op)
            }
        };
        public.extend(pb);
        private.extend(pv);
        op_ids.push(op);
    }
    let circuit = vcircuit.build().expect("fold circuit builds");
    FoldCircuit { circuit, public, private, op_ids }
}

fn run_fold_circuit(
    config: &rec::MyConfig,
    shape: rec::FriShape,
    fc: &FoldCircuit,
    inputs: &[FoldInput],
    private: &[rec::Challenge],
) -> Result<p3_circuit::Traces<rec::Challenge>, String> {
    let mut runner = fc.circuit.runner();
    runner.set_public_inputs(&fc.public).map_err(|e| format!("{e:?}"))?;
    runner.set_private_inputs(private).map_err(|e| format!("{e:?}"))?;
    for (input, op) in inputs.iter().zip(&fc.op_ids) {
        set_proof_mmcs(&mut runner, config, shape, input, op)?;
    }
    runner.run().map_err(|e| format!("{e:?}"))
}

fn prove_fold_circuit(
    config: &rec::MyConfig,
    fc: &FoldCircuit,
    traces: &p3_circuit::Traces<rec::Challenge>,
) -> Folded {
    let w16 = Poseidon2Config::KOALA_BEAR_D4_W16;
    let npo_prep: Vec<Box<dyn NpoPreprocessor<rec::F>>> = vec![
        Box::new(Poseidon2Preprocessor),
        Box::new(RecomposePreprocessor::new(true)),
    ];
    let mut air_builders = poseidon2_air_builders_for_configs::<_, 4>(vec![w16.for_challenger(), w16]);
    air_builders.extend(recompose_air_builders(1, true));
    let (ad, prim, nonprim) = get_airs_and_degrees_with_prep::<rec::MyConfig, rec::Challenge, 4>(
        &fc.circuit,
        &fold_table_packing(),
        &npo_prep,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .expect("fold airs");
    let (airs, degrees): (Vec<_>, Vec<usize>) = ad.into_iter().unzip();
    let pd = ProverData::from_airs_and_degrees(config, &airs, &degrees).expect("fold prover data");
    let cpd = CircuitProverData::new(pd, prim, nonprim);
    let folded = fold_prover(config).prove_all_tables(traces, &cpd).expect("prove fold");
    fold_accepts_bytes(config, &encode_proof(&folded)).expect("verify fold");
    Folded { proof: folded, cpd, airs }
}

fn fold_prover(config: &rec::MyConfig) -> BatchStarkProver<rec::MyConfig> {
    let w16 = Poseidon2Config::KOALA_BEAR_D4_W16;
    let mut prover = BatchStarkProver::new(config.clone()).with_table_packing(fold_table_packing());
    prover.register_poseidon2_table::<4>(w16.for_challenger());
    prover.register_poseidon2_table::<4>(w16);
    prover.register_recompose_table::<4>(true);
    prover
}

pub fn fold_accepts_bytes(config: &rec::MyConfig, bytes: &[u8]) -> Result<(), String> {
    fold_prover(config)
        .verify_all_tables::<rec::Challenge>(&decode_proof(bytes)?)
        .map_err(|e| format!("{e:?}"))
}

pub struct Folded {
    proof: BatchStarkProof<rec::MyConfig>,
    cpd: CircuitProverData<rec::MyConfig>,
    airs: Vec<CircuitTableAir<rec::MyConfig, 4>>,
}

fn fold_pair(a: FoldInput, b: FoldInput) -> Result<Folded, String> {
    fold_pair_at_shape(D4_SHAPE, a, b)
}

fn fold_pair_at_shape(shape: rec::FriShape, a: FoldInput, b: FoldInput) -> Result<Folded, String> {
    let config = rec::fold_config(shape);
    let inputs = [a, b];
    for (i, input) in inputs.iter().enumerate() {
        let fail = |what: String| format!("inner proof {i} ({}) {what}", input.layer());
        match *input {
            FoldInput::Spend { proof, key } => {
                if key.shape != shape {
                    return Err(fail(format!("has a spend key at {:?}, not the fold shape", key.shape)));
                }
                if key.commitment != spend_key(shape).commitment {
                    return Err(fail("has a spend key that is not the canonical spend circuit".into()));
                }
                key.accepts(proof).map_err(|e| fail(format!("is not valid at the fold shape: {e}")))?;
            }
            FoldInput::Fold { proof, common } => {
                if preprocessed_commitment(common) != preprocessed_commitment(&proof.stark_common) {
                    return Err(fail("does not match the verifying data it was given".into()));
                }
                fold_prover(&config)
                    .verify_all_tables::<Challenge>(proof)
                    .map_err(|e| fail(format!("is not valid at the fold shape: {e:?}")))?;
            }
        }
    }
    let fc = build_fold_circuit(&config, shape, &inputs);
    let traces = run_fold_circuit(&config, shape, &fc, &inputs, &fc.private)?;
    Ok(prove_fold_circuit(&config, &fc, &traces))
}

fn kb(bytes: &[u8]) -> f64 {
    bytes.len() as f64 / 1024.0
}

fn milestone_4c() {
    let key = spend_key(D4_SHAPE);
    let proof = prove_spend(&key, 0);
    let config = rec::fold_config(key.shape);
    let inputs = [FoldInput::Spend { proof: &proof, key: &key }];
    let fc = build_fold_circuit(&config, key.shape, &inputs);
    run_fold_circuit(&config, key.shape, &fc, &inputs, &fc.private)
        .expect("M4c honest spend verifies in-circuit");
    let mut bad = fc.private.clone();
    bad[0] += rec::Challenge::ONE;
    assert!(
        run_fold_circuit(&config, key.shape, &fc, &inputs, &bad).is_err(),
        "M4c NEGATIVE FAILED: a tampered spend proof was accepted in-circuit"
    );
    println!("M4c OK: spend proof verified in-circuit; a tampered proof is rejected.");
}

fn milestone_4d() -> (SpendProof, FoldProof) {
    let key = spend_key(D4_SHAPE);
    let p0 = prove_spend(&key, 0);
    let p1 = prove_spend(&key, 1);
    let t = Instant::now();
    let folded = fold_pair(
        FoldInput::Spend { proof: &p0, key: &key },
        FoldInput::Spend { proof: &p1, key: &key },
    )
    .expect("fold");
    println!(
        "M4d OK: 2 spends -> 1 folded proof, {:.1} KB, fold {:.1} s (base {:.1} KB).",
        kb(&encode_proof(&folded.proof)),
        t.elapsed().as_secs_f64(),
        kb(&encode_spend(&p0))
    );
    (p0, folded.proof)
}

fn milestone_4e() -> FoldProof {
    let key = spend_key(D4_SHAPE);
    let leaves: Vec<_> = (0..4).map(|s| prove_spend(&key, s)).collect();
    let leaf = |i: usize| FoldInput::Spend { proof: &leaves[i], key: &key };
    let f01 = fold_pair(leaf(0), leaf(1)).expect("fold");
    let f23 = fold_pair(leaf(2), leaf(3)).expect("fold");
    let root = fold_pair(
        FoldInput::Fold { proof: &f01.proof, common: f01.cpd.common_data() },
        FoldInput::Fold { proof: &f23.proof, common: f23.cpd.common_data() },
    )
    .expect("fold");
    println!(
        "M4e OK: 4 spends -> tree -> 1 root. layer-1 fold {:.1} KB, root {:.1} KB.",
        kb(&encode_proof(&f01.proof)),
        kb(&encode_proof(&root.proof))
    );
    root.proof
}

pub fn proof_dir() -> String {
    std::env::var("PQC_PROOF_DIR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/target/proofs").into())
}

pub(crate) fn save_proof(name: &str, bytes: &[u8]) {
    let dir = proof_dir();
    std::fs::create_dir_all(&dir).expect("create proof dir");
    std::fs::write(format!("{dir}/{name}"), bytes).expect("write proof");
}

#[derive(Default, Debug)]
pub struct TamperTally {
    pub decode_rejects: usize,
    pub verify_rejects: usize,
    pub panics: usize,
    pub accepted: usize,
    pub accepted_cases: Vec<String>,
}

pub(crate) fn tamper_sweep(bytes: &[u8], flips: usize, verify: &dyn Fn(&[u8]) -> Result<(), String>) -> TamperTally {
    let mut t = TamperTally::default();
    let mut cases: Vec<(String, Vec<u8>)> = (0..flips)
        .map(|i| {
            let mut b = bytes.to_vec();
            let pos = (i * 7919 + i / 3) % b.len();
            b[pos] ^= 1 << (i % 8);
            (format!("flip byte {pos} bit {}", i % 8), b)
        })
        .collect();
    for cut in [0, 1, bytes.len() / 2, bytes.len() - 1] {
        cases.push((format!("truncate to {cut}"), bytes[..cut].to_vec()));
    }
    for extra in [0u8, 1, 0xff] {
        let mut longer = bytes.to_vec();
        longer.push(extra);
        cases.push((format!("append {extra:#04x}"), longer));
    }
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    for (label, case) in &cases {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify(case))) {
            Err(_) => t.panics += 1,
            Ok(Ok(())) => {
                t.accepted += 1;
                t.accepted_cases.push(label.clone());
            }
            Ok(Err(e)) if e.starts_with("decode:") => t.decode_rejects += 1,
            Ok(Err(_)) => t.verify_rejects += 1,
        }
    }
    std::panic::set_hook(hook);
    t
}

pub fn verify_saved_proofs() -> bool {
    let dir = proof_dir();
    let read = |name: &str| {
        std::fs::read(format!("{dir}/{name}"))
            .unwrap_or_else(|e| panic!("{dir}/{name}: {e} (run the faraday_fold bin first)"))
    };
    let funds = SpendVerifier::new(D4_SHAPE, read("spend-vk.bin"));
    assert_eq!(
        funds.commitment(),
        generate_spend_key(D4_SHAPE).commitment,
        "spend-vk.bin is not the verifying key recomputed from the spend circuit"
    );
    let fold_config = rec::fold_config(D4_SHAPE);
    let checks: [(&str, Box<dyn Fn(&[u8]) -> Result<(), String>>); 3] = [
        ("spend-funds.bin", Box::new(|b| funds.accepts_bytes(b))),
        ("fold-funds.bin", Box::new(|b| fold_accepts_bytes(&fold_config, b))),
        ("root-funds.bin", Box::new(|b| fold_accepts_bytes(&fold_config, b))),
    ];
    let mut ok = true;
    for (name, verify) in &checks {
        let bytes = read(name);
        verify(&bytes).unwrap_or_else(|e| panic!("{name}: honest proof rejected: {e}"));
        let t = tamper_sweep(&bytes, 256, verify.as_ref());
        println!("{name}: honest accepted; tampered {t:?}");
        ok &= t.accepted == 0 && t.panics == 0;
    }
    ok
}

pub fn run_all_milestones() {
    milestone_0();
    milestone_1a();
    milestone_1b();
    milestone_2();
    milestone_3();
    milestone_4a();
    milestone_4b();
    milestone_4c();
    let (spend, fold) = milestone_4d();
    save_proof("spend-vk.bin", spend_key(D4_SHAPE).verifier().commitment());
    save_proof("spend-funds.bin", &encode_spend(&spend));
    save_proof("fold-funds.bin", &encode_proof(&fold));
    save_proof("root-funds.bin", &encode_proof(&milestone_4e()));
}

fn timed<T>(cpu_now: &dyn Fn() -> Duration, f: impl FnOnce() -> T) -> (T, Duration, Duration) {
    let c0 = cpu_now();
    let w0 = Instant::now();
    let out = f();
    (out, w0.elapsed(), cpu_now().saturating_sub(c0))
}

pub struct Measurement {
    pub proof_bytes: usize,
    pub prove_wall: Duration,
    pub prove_cpu: Duration,
    pub verify_wall: Duration,
    pub verify_cpu: Duration,
}

pub struct Prepared {
    key: &'static SpendKey,
}

pub fn prepare() -> Prepared {
    Prepared { key: spend_key(D4_SHAPE) }
}

pub fn run_one(prep: &Prepared, seed: u64, cpu_now: &dyn Fn() -> Duration) -> Measurement {
    let traces = spend_traces(seed);
    let prover = prep.key.prover();
    let (proof, prove_wall, prove_cpu) =
        timed(cpu_now, || prover.prove_all_tables(&traces, &prep.key.cpd).expect("prove"));
    let (_, verify_wall, verify_cpu) =
        timed(cpu_now, || prep.key.accepts(&proof).expect("verify"));
    let proof_bytes = encode_spend(&proof).len();
    Measurement { proof_bytes, prove_wall, prove_cpu, verify_wall, verify_cpu }
}

pub struct FoldMeasurement {
    pub base_bytes: usize,
    pub folded_bytes: usize,
    pub fold_wall: Duration,
}

pub fn fold_two() -> FoldMeasurement {
    let key = spend_key(D4_SHAPE);
    let p0 = prove_spend(&key, 0);
    let p1 = prove_spend(&key, 1);
    let t = Instant::now();
    let folded = fold_pair(
        FoldInput::Spend { proof: &p0, key: &key },
        FoldInput::Spend { proof: &p1, key: &key },
    )
    .expect("fold");
    let fold_wall = t.elapsed();
    FoldMeasurement {
        base_bytes: encode_spend(&p0).len(),
        folded_bytes: encode_proof(&folded.proof).len(),
        fold_wall,
    }
}

pub fn self_check() -> Result<(), String> {
    let perm = default_koalabear_poseidon2_32();
    let input: [Val; WIDTH] = core::array::from_fn(|i| Val::from_u64((i + 1) as u64));
    let x: [Val; DIGEST] = core::array::from_fn(|i| input[i]);
    let y: [Val; DIGEST] = core::array::from_fn(|i| input[DIGEST + i]);
    let native = compress(&perm, &x, &y);

    let mut builder: CircuitBuilder<Challenge> = CircuitBuilder::new();
    builder.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<Challenge, KoalaBearD4Width32>,
        perm.clone(),
    );
    builder.enable_recompose::<Val>(generate_recompose_trace::<Val, Challenge>);
    let ex = alloc_block(&mut builder, &x, "x");
    let ey = alloc_block(&mut builder, &y, "y");
    let digest = dsl_compress(&mut builder, ex, ey);
    let circuit = builder.build().map_err(|e| format!("{e:?}"))?;
    let expr_to_widx = circuit.expr_to_widx.clone();
    let traces = circuit.runner().run().map_err(|e| format!("{e:?}"))?;
    let get_val = |e: ExprId| -> Challenge {
        let wid = *expr_to_widx.get(&e).expect("widx");
        *traces.witness_trace.get_value(wid).expect("val")
    };
    let got = read_digest(&get_val, &digest);
    if got == native {
        Ok(())
    } else {
        Err("DSL W32 compression != native KoalaBear Poseidon2".into())
    }
}

#[cfg(test)]
#[macro_export]
macro_rules! check_fold_leaf_binding {
    ($circuit:expr, $ef:ty, $d:literal, $mmcs_bit_slot:expr) => {{
        use p3_circuit::ops::Op;
            let ops = &$circuit.ops;
            let label = |op: &Op<$ef>| match op {
                Op::Const { .. } => "const".to_string(),
                Op::Public { .. } => "public".to_string(),
                Op::Alu { kind, .. } => format!("alu/{kind:?}"),
                Op::Hint { .. } => "hint".to_string(),
                Op::NonPrimitiveOpWithExecutor { executor, .. } => executor.op_type().as_str().to_string(),
            };
            let mut writer = std::collections::HashMap::new();
            for (i, op) in ops.iter().enumerate() {
                let outs: Vec<p3_circuit::WitnessId> = match op {
                    Op::Const { out, .. } | Op::Public { out, .. } => vec![*out],
                    Op::Alu { out, intermediate_out, .. } => std::iter::once(*out).chain(*intermediate_out).collect(),
                    Op::Hint { outputs, .. } => outputs.clone(),
                    Op::NonPrimitiveOpWithExecutor { outputs, .. } => outputs.concat(),
                };
                for w in outs {
                    writer.entry(w).or_insert(i);
                }
            }
            let mut census = std::collections::BTreeMap::<(String, String), usize>::new();
            for op in ops {
                if let Op::NonPrimitiveOpWithExecutor { inputs, .. } = op {
                    let me = label(op);
                    for (slot, ws) in inputs.iter().enumerate() {
                        for w in ws {
                            let by = writer.get(w).map(|&i| label(&ops[i])).unwrap_or("none".into());
                            let slot = if me.starts_with("poseidon2_perm") { format!(" slot {slot}") } else { String::new() };
                            *census.entry((format!("{me}{slot}"), by)).or_default() += 1;
                        }
                    }
                }
            }
            for ((reader, by), n) in &census {
                println!("CENSUS {reader} <- {by}: {n}");
            }

            assert!(ops.iter().all(|op| label(op) != "recompose"), "legacy recompose op present");
            let prep = $circuit.generate_preprocessed_columns::<$d>().expect("preprocessed");
            let mut unbound = 0;
            for op in ops {
                if let Op::NonPrimitiveOpWithExecutor { inputs, .. } = op {
                    if label(op) == "recompose/coeff" {
                        for w in inputs.concat() {
                            if !writer.contains_key(&w) && !prep.recompose_coeff_creator_wids.contains(&w.0) {
                                unbound += 1;
                            }
                        }
                    }
                }
            }
            assert_eq!(unbound, 0, "recompose/coeff inputs with no creator");
            let alu_read: std::collections::HashSet<_> = ops
                .iter()
                .filter_map(|op| match op {
                    Op::Alu { a, b, c, .. } => Some([Some(*a), Some(*b), *c]),
                    _ => None,
                })
                .flatten()
                .flatten()
                .collect();
            let mut unwritten_perm = Vec::new();
            for op in ops {
                if let Op::NonPrimitiveOpWithExecutor { inputs, .. } = op {
                    if label(op).starts_with("poseidon2_perm") {
                        for w in inputs.concat() {
                            if !writer.contains_key(&w)
                                && !alu_read.contains(&w)
                                && !prep.recompose_coeff_creator_wids.contains(&w.0)
                            {
                                unwritten_perm.push(w.0);
                            }
                        }
                    }
                }
            }
            assert!(unwritten_perm.is_empty(), "permutation inputs with no creator: {unwritten_perm:?}");
            let mmcs_bit: usize = $mmcs_bit_slot;
            let bool_checked: std::collections::HashSet<_> = ops
                .iter()
                .filter_map(|op| match op {
                    Op::Alu { kind, a, .. } if format!("{kind:?}") == "BoolCheck" => Some(*a),
                    _ => None,
                })
                .collect();
            let mut hinted = 0;
            let mut hint_ops = std::collections::BTreeSet::new();
            let mut bit_hints = std::collections::BTreeSet::new();
            for op in ops {
                if let Op::NonPrimitiveOpWithExecutor { inputs, .. } = op {
                    if label(op).starts_with("poseidon2_perm") {
                        for (slot, ws) in inputs.iter().enumerate() {
                            for w in ws {
                                let Some(&i) = writer.get(w) else { continue };
                                if matches!(ops[i], Op::Hint { .. }) {
                                    hinted += 1;
                                    if slot == mmcs_bit {
                                        assert!(bool_checked.contains(w), "direction bit not BoolCheck'ed");
                                        bit_hints.insert(i);
                                    }
                                    hint_ops.insert(i);
                                }
                            }
                        }
                    }
                }
            }
            assert!(hinted > 0, "census found no hinted inputs; the check says nothing");
            let rebuilt_from = |outs: &[p3_circuit::WitnessId]| {
                let mut derived: std::collections::HashSet<_> = outs.iter().copied().collect();
                loop {
                    let before = derived.len();
                    for op in ops {
                        let (reads, writes): (Vec<_>, Vec<_>) = match op {
                            Op::Alu { a, b, c, out, .. } => {
                                ([Some(*a), Some(*b), *c].into_iter().flatten().collect(), vec![*out])
                            }
                            Op::NonPrimitiveOpWithExecutor { inputs, outputs, .. }
                                if label(op) == "recompose/coeff" =>
                            {
                                (inputs.concat(), outputs.concat())
                            }
                            _ => continue,
                        };
                        if reads.iter().any(|w| derived.contains(w)) {
                            derived.extend(writes);
                        }
                    }
                    if derived.len() == before {
                        return derived;
                    }
                }
            };
            let mut stack: Vec<usize> = hint_ops.iter().copied().collect();
            let mut seen = std::collections::HashSet::new();
            while let Some(h) = stack.pop() {
                if !seen.insert(h) {
                    continue;
                }
                let Op::Hint { inputs: decomposed, outputs, .. } = &ops[h] else { unreachable!() };
                let derived = rebuilt_from(outputs);
                for x in decomposed {
                    assert!(derived.contains(x), "hint {h}: decomposed value not rebuilt from its outputs");
                    if let Some(&i) = writer.get(x) {
                        if matches!(ops[i], Op::Hint { .. }) {
                            stack.push(i);
                        }
                    }
                }
            }
            assert!(!bit_hints.is_empty(), "no direction-bit hints found");
            for &h in &bit_hints {
                let Op::Hint { outputs, .. } = &ops[h] else { unreachable!() };
                assert!(outputs.iter().all(|w| bool_checked.contains(w)), "hint {h}: a bit is not BoolCheck'ed");
            }
            println!("CENSUS hinted permutation inputs {hinted} from {} hints ({} bit splits); {} hints in their chains, all rebuilt", hint_ops.len(), bit_hints.len(), seen.len());
    }};
}

#[cfg(test)]
pub(crate) fn logup_terminal_analysis<EF: p3_field::Field>(
    circuit: &p3_circuit::Circuit<EF>,
    marks: &[(&'static str, ExprId)],
    secrets: &[&str],
) {
    use p3_circuit::ops::Op;
    use std::collections::{BTreeMap, BTreeSet, HashMap};
    let widx = &circuit.expr_to_widx;
    let mut fixed: HashMap<p3_circuit::WitnessId, BTreeSet<&str>> = HashMap::new();
    for &(label, e) in marks {
        let set = match label {
            "leaf" | "key_image" | "commit_out" => BTreeSet::from(["on-chain"]),
            other => BTreeSet::from([other]),
        };
        fixed.insert(widx[&e], set);
    }
    let mut taint: HashMap<p3_circuit::WitnessId, BTreeSet<&str>> = HashMap::new();
    let io_of = |op: &Op<EF>| -> (Vec<p3_circuit::WitnessId>, Vec<p3_circuit::WitnessId>) {
        match op {
            Op::Const { out, .. } | Op::Public { out, .. } => (vec![], vec![*out]),
            Op::Alu { a, b, c, out, intermediate_out, .. } => (
                [Some(*a), Some(*b), *c].into_iter().flatten().collect(),
                std::iter::once(*out).chain(*intermediate_out).collect(),
            ),
            Op::Hint { inputs, outputs, .. } => (inputs.clone(), outputs.clone()),
            Op::NonPrimitiveOpWithExecutor { inputs, outputs, .. } => (inputs.concat(), outputs.concat()),
        }
    };
    for op in &circuit.ops {
        match op {
            Op::Const { out, .. } => {
                fixed.entry(*out).or_insert_with(|| BTreeSet::from(["const"]));
            }
            Op::Public { out, .. } => {
                fixed.entry(*out).or_insert_with(|| BTreeSet::from(["on-chain"]));
            }
            _ => {}
        }
    }
    taint.extend(fixed.iter().map(|(w, t)| (*w, t.clone())));
    loop {
        let mut changed = false;
        for op in &circuit.ops {
            let (ins, outs) = io_of(op);
            let (sources, targets): (Vec<_>, Vec<_>) = match op {
                Op::Alu { .. } => {
                    let all: Vec<_> = ins.iter().chain(&outs).copied().collect();
                    (all.clone(), all)
                }
                _ => (ins, outs),
            };
            let t: BTreeSet<&str> = sources.iter().flat_map(|w| taint.get(w).cloned().unwrap_or_default()).collect();
            for o in targets {
                if !fixed.contains_key(&o) {
                    let e = taint.entry(o).or_default();
                    let before = e.len();
                    e.extend(t.iter().copied());
                    changed |= e.len() != before;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let table = |op: &Op<EF>| -> Option<String> {
        match op {
            Op::Const { .. } => Some("const".into()),
            Op::Public { .. } => Some("public".into()),
            Op::Alu { .. } => Some("alu".into()),
            Op::Hint { .. } => None,
            Op::NonPrimitiveOpWithExecutor { executor, .. } => Some(executor.op_type().as_str().to_string()),
        }
    };
    let mut per_table: BTreeMap<String, (BTreeSet<&str>, usize, usize)> = BTreeMap::new();
    for op in &circuit.ops {
        let Some(t) = table(op) else { continue };
        let (ins, outs) = io_of(op);
        let entry = per_table.entry(t).or_default();
        entry.1 += 1;
        let mut row_secret = false;
        for w in ins.iter().chain(&outs) {
            let tw = taint.get(w).cloned().unwrap_or_default();
            row_secret |= tw.iter().any(|l| secrets.contains(l));
            entry.0.extend(tw);
        }
        entry.2 += usize::from(row_secret);
    }
    let mut reads: HashMap<p3_circuit::WitnessId, Vec<String>> = HashMap::new();
    let mut creator: HashMap<p3_circuit::WitnessId, String> = HashMap::new();
    for op in &circuit.ops {
        let Some(t) = table(op) else { continue };
        let (ins, outs) = io_of(op);
        for w in outs {
            creator.entry(w).or_insert_with(|| t.clone());
        }
        for w in ins {
            reads.entry(w).or_default().push(t.clone());
        }
    }
    for op in &circuit.ops {
        let Some(t) = table(op) else { continue };
        for w in io_of(op).0 {
            creator.entry(w).or_insert_with(|| t.clone());
        }
    }
    let mut net: BTreeMap<String, BTreeSet<&str>> = BTreeMap::new();
    let mut direct: BTreeMap<String, Vec<(u32, &str)>> = BTreeMap::new();
    let mut net_rows: BTreeMap<String, usize> = BTreeMap::new();
    for (w, by) in &reads {
        let total = by.len() as i64;
        let tables: BTreeSet<&String> = by.iter().chain(creator.get(w)).collect();
        for t in tables {
            let created = i64::from(creator.get(w) == Some(t)) * total;
            let read_here = by.iter().filter(|x| *x == t).count() as i64;
            if created - read_here != 0 {
                if let Some(label) = fixed.get(w).and_then(|f| f.iter().find(|l| secrets.contains(l))) {
                    direct.entry(t.clone()).or_default().push((w.0, label));
                }
                let tw = taint.get(w).cloned().unwrap_or_default();
                if tw.iter().any(|l| secrets.contains(l)) {
                    *net_rows.entry(t.clone()).or_default() += 1;
                }
                net.entry(t.clone()).or_default().extend(tw);
            }
        }
    }
    for (t, (labels, rows, secret_rows)) in &per_table {
        let kept = net.get(t).cloned().unwrap_or_default();
        let needs = kept.iter().any(|l| secrets.contains(l));
        println!(
            "TABLE {t}: {rows} ops, {secret_rows} touch a secret; touched {labels:?}; \
             terminal keeps {kept:?} ({} secret witnesses with nonzero net); terminal needs a secret: {needs}",
            net_rows.get(t).copied().unwrap_or(0)
        );
        let direct_here = direct.get(t).cloned().unwrap_or_default();
        println!("  {t}: directly labelled secret witnesses kept: {direct_here:?}");
        assert!(
            !direct_here.is_empty() || kept.iter().all(|l| ["const", "on-chain"].contains(l)),
            "table {t}: terminal keeps no directly labelled secret and is not public-only: {kept:?}"
        );
    }
    assert!(net.values().any(|k| k.iter().any(|l| secrets.contains(l))), "analysis found no secret at all");
}

macro_rules! soundness_of {
    ($name:ident, $sc:ty) => {
        fn $name(
            config: &$sc,
            shape: rec::FriShape,
            airs: &[CircuitTableAir<$sc, 4>],
            common: &p3_batch_stark::CommonData<$sc>,
            proof: &BatchStarkProof<$sc>,
        ) -> (Vec<crate::soundness::TableShape>, crate::soundness::Report) {
            use p3_uni_stark::StarkGenericConfig;
            let instances = &proof.proof.opened_values.instances;
            assert_eq!(airs.len(), instances.len(), "one AIR per proof instance");
            let tables: Vec<_> = airs
                .iter()
                .zip(instances)
                .zip(&proof.proof.degree_bits)
                .zip(&common.lookups)
                .map(|(((air, inst), &degree_bits), lookups)| {
                    let ov = &inst.base_opened_values;
                    crate::soundness::table_shape::<rec::F, rec::Challenge, _>(
                        air,
                        lookups,
                        degree_bits,
                        ov.trace_next.is_some(),
                        ov.preprocessed.as_ref().map(|p| p.local.len()).unwrap_or(0),
                        ov.preprocessed.as_ref().map(|p| p.next.is_some()).unwrap_or(false),
                        ov.quotient_chunks.len(),
                    )
                })
                .collect();
            let fri = crate::soundness::FriShapeBits {
                log_blowup: shape.log_blowup,
                max_log_arity: shape.max_log_arity,
                log_final_poly_len: 0,
                num_queries: shape.num_queries,
                commit_pow_bits: 0,
                query_pow_bits: rec::QUERY_POW_BITS,
                batch_pow_bits: 0,
                lookup_pow_bits: config.lookup_proof_of_work_bits(),
                ood_pow_bits: config.ood_proof_of_work_bits(),
            };
            let report = crate::soundness::report::<rec::F>(&tables, &fri, 4, rec::DIGEST_ELEMS);
            (tables, report)
        }
    };
}

soundness_of!(soundness_of_spend, rec::ZkConfig);
soundness_of!(soundness_of_fold, rec::MyConfig);

pub fn min_queries_sweep(name: &str, tables: &[crate::soundness::TableShape], max_log_arity: usize) {
    min_queries_sweep_for(name, tables, max_log_arity, &[4, 5], &[0, 20]);
}

pub fn min_queries_sweep_for(
    name: &str,
    tables: &[crate::soundness::TableShape],
    max_log_arity: usize,
    degrees: &[usize],
    batch_pows: &[usize],
) {
    let bits = |degree: usize, log_blowup: usize, q: usize, batch_pow: usize| {
        let fri = crate::soundness::FriShapeBits {
            log_blowup,
            max_log_arity,
            log_final_poly_len: 0,
            num_queries: q,
            commit_pow_bits: 0,
            query_pow_bits: rec::QUERY_POW_BITS,
            batch_pow_bits: batch_pow,
            lookup_pow_bits: 0,
            ood_pow_bits: 0,
        };
        crate::soundness::report::<rec::F>(tables, &fri, degree, rec::DIGEST_ELEMS)
    };
    for &degree in degrees {
        for &batch_pow in batch_pows {
            for log_blowup in 1..=6usize {
                let mut cells = Vec::new();
                for target in [100.0f64, 112.0, 128.0] {
                    let proven = (1..=400).find(|&q| bits(degree, log_blowup, q, batch_pow).proven_bits() >= target);
                    let conj = (1..=400).find(|&q| bits(degree, log_blowup, q, batch_pow).conjectured_bits >= target);
                    let f = |x: Option<usize>| x.map(|q| q.to_string()).unwrap_or("-".into());
                    cells.push(format!("{target:>3}: proven {:>3} conj {:>3}", f(proven), f(conj)));
                }
                println!("  sweep {name:<14} D={degree} batch_pow={batch_pow:>2} log_blowup={log_blowup}  {}", cells.join("  |  "));
            }
        }
    }
}

fn what_if(name: &str, tables: &[crate::soundness::TableShape], shape: rec::FriShape) {
    for &(degree, queries, batch_pow) in &[
        (4usize, 56usize, 0usize),
        (4, 56, 20),
        (4, 120, 20),
        (5, 56, 0),
        (5, 56, 20),
        (5, 120, 20),
        (5, 150, 20),
        (6, 56, 20),
        (8, 56, 20),
    ] {
        let fri = crate::soundness::FriShapeBits {
            log_blowup: shape.log_blowup,
            max_log_arity: shape.max_log_arity,
            log_final_poly_len: 0,
            num_queries: queries,
            commit_pow_bits: 0,
            query_pow_bits: rec::QUERY_POW_BITS,
            batch_pow_bits: batch_pow,
            lookup_pow_bits: 0,
            ood_pow_bits: 0,
        };
        let r = crate::soundness::report::<rec::F>(tables, &fri, degree, rec::DIGEST_ELEMS);
        println!(
            "  what-if {name:<15} D={degree} queries={queries:>3} batch_pow={batch_pow:>2}: proven {:>5.1} \
             (UDR {:>5.1} {}, LDR {:>5.1} {})  conjectured {:>5.1}",
            r.proven_bits(), r.udr_bits, r.udr_binding, r.ldr_bits, r.ldr_binding, r.conjectured_bits
        );
    }
}

fn print_soundness(name: &str, r: &crate::soundness::Report, bytes: f64) {
    println!(
        "{name:<16} tables {:>2}  log2 domain {:>2}  batched {:>5}  constraints {:>6}  max deg {}  \
         |EF| {} bits  hash {} bits  size {:>6.1} KB",
        r.tables, r.log_domain, r.batched_functions, r.constraints, r.max_degree,
        r.modulus_bits, r.collision_bits, bytes
    );
    println!(
        "{:<16} PROVEN UDR {:>5.1} ({})  PROVEN LDR {:>5.1} ({})  CONJECTURED {:>5.1} ({})",
        "", r.udr_bits, r.udr_binding, r.ldr_bits, r.ldr_binding, r.conjectured_bits,
        r.conjectured_binding
    );
}

pub fn soundness_suite(shape: rec::FriShape) {
    println!(
        "FRI shape: log_blowup {}  max_log_arity {}  queries {}  query PoW {} bits",
        shape.log_blowup, shape.max_log_arity, shape.num_queries, rec::QUERY_POW_BITS
    );
    let key = spend_key(shape);
    let p0 = prove_spend(&key, 0);
    let p1 = prove_spend(&key, 1);
    let p2 = prove_spend(&key, 2);
    let p3 = prove_spend(&key, 3);
    let (spend_tables, r) = soundness_of_spend(&rec::make_zk_config(shape), shape, &key.airs, key.cpd.common_data(), &p0);
    print_soundness("spend proof", &r, kb(&encode_spend(&p0)));

    let f01 = fold_pair_at_shape(shape,
        FoldInput::Spend { proof: &p0, key: &key },
        FoldInput::Spend { proof: &p1, key: &key },
    ).expect("fold");
    let f23 = fold_pair_at_shape(shape,
        FoldInput::Spend { proof: &p2, key: &key },
        FoldInput::Spend { proof: &p3, key: &key },
    ).expect("fold");
    let fold_config = rec::fold_config(shape);
    let (fold_tables, r) = soundness_of_fold(&fold_config, shape, &f01.airs, f01.cpd.common_data(), &f01.proof);
    print_soundness("fold of spends", &r, kb(&encode_proof(&f01.proof)));

    let root = fold_pair_at_shape(shape,
        FoldInput::Fold { proof: &f01.proof, common: f01.cpd.common_data() },
        FoldInput::Fold { proof: &f23.proof, common: f23.cpd.common_data() },
    ).expect("fold");
    let (_, r) = soundness_of_fold(&fold_config, shape, &root.airs, root.cpd.common_data(), &root.proof);
    print_soundness("fold of folds", &r, kb(&encode_proof(&root.proof)));
    for t in &fold_tables {
        println!(
            "  fold table: log2 rows {:>2}  main {:>4}  prep {:>3}  quotient {}  lookups {:>2}  interactions {:>3}  constraints {:>4}  deg {}",
            t.degree_bits, t.main_width, t.preprocessed_width, t.quotient_chunks, t.num_lookups,
            t.interactions_per_row, t.num_constraints, t.max_constraint_degree
        );
    }
    what_if("spend proof", &spend_tables, shape);
    what_if("fold", &fold_tables, shape);
    min_queries_sweep("spend proof", &spend_tables, shape.max_log_arity);
    min_queries_sweep("fold", &fold_tables, shape.max_log_arity);
}

mod rec16 {
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_dft::Radix2DitParallel;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::Field;
    use p3_fri::{FriParameters, TwoAdicFriPcs};
    use p3_koala_bear::{
        default_koalabear_poseidon2_16, default_koalabear_poseidon2_32, KoalaBear, Poseidon2KoalaBear,
    };
    use p3_merkle_tree::MerkleTreeMmcs;
    use p3_recursion::pcs::{
        FriProofTargets, InputProofTargets, RecExtensionValMmcs, RecValMmcs, Witness,
    };
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::StarkConfig;

    pub type F = KoalaBear;
    pub const DIGEST_ELEMS: usize = 16;
    pub type Challenge = BinomialExtensionField<F, 4>;
    pub type Perm16 = Poseidon2KoalaBear<16>;
    pub type Perm32 = Poseidon2KoalaBear<32>;
    pub type MyHash = PaddingFreeSponge<Perm32, 32, 16, DIGEST_ELEMS>;
    pub type MyCompress = TruncatedPermutation<Perm32, 2, DIGEST_ELEMS, 32>;
    pub type MyMmcs = MerkleTreeMmcs<
        <F as Field>::Packing,
        <F as Field>::Packing,
        MyHash,
        MyCompress,
        2,
        DIGEST_ELEMS,
    >;
    pub type ChallengeMmcs = ExtensionMmcs<F, Challenge, MyMmcs>;
    pub type Challenger = DuplexChallenger<F, Perm16, 16, 8>;
    pub type MyPcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, MyMmcs, ChallengeMmcs>;
    pub type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;
    pub type InnerFri = FriProofTargets<
        F,
        Challenge,
        RecExtensionValMmcs<F, Challenge, DIGEST_ELEMS, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
        InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
        Witness<F>,
    >;

    pub fn fri_instance(shape: super::rec::FriShape) -> (MyMmcs, FriParameters<ChallengeMmcs>) {
        let perm = default_koalabear_poseidon2_32();
        let val_mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);
        let fri_params = FriParameters {
            max_log_arity: shape.max_log_arity,
            log_blowup: shape.log_blowup,
            log_final_poly_len: 0,
            num_queries: shape.num_queries,
            batch_proof_of_work_bits: 0,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: super::rec::QUERY_POW_BITS,
            mmcs: ChallengeMmcs::new(val_mmcs.clone()),
        };
        (val_mmcs, fri_params)
    }

    pub fn make_config(shape: super::rec::FriShape) -> MyConfig {
        let (val_mmcs, fri_params) = fri_instance(shape);
        let pcs = MyPcs::new(Radix2DitParallel::default(), val_mmcs, fri_params);
        MyConfig::new(pcs, Challenger::new(default_koalabear_poseidon2_16()))
    }
}

pub fn wide_commitment_probe(shape: rec::FriShape) -> Result<(), String> {
    let config = rec16::make_config(shape);
    let (circuit, _) = build_spend_circuit(0);
    let npo_prep: Vec<Box<dyn NpoPreprocessor<Val>>> = vec![
        Box::new(Poseidon2Preprocessor),
        Box::new(RecomposePreprocessor::default()),
    ];
    let mut air_builders = poseidon2_air_builders::<_, 4>();
    air_builders.extend(recompose_air_builders(1, false));
    let (airs_degrees, prim, nonprim) = get_airs_and_degrees_with_prep::<rec16::MyConfig, Challenge, 4>(
        &circuit,
        &TablePacking::new(4, 4),
        &npo_prep,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .map_err(|e| format!("airs: {e:?}"))?;
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    let pd = ProverData::from_airs_and_degrees(&config, &airs, &degrees).map_err(|e| format!("{e:?}"))?;
    let cpd = CircuitProverData::new(pd, prim, nonprim);
    let mut prover = BatchStarkProver::new(config.clone()).with_table_packing(TablePacking::new(4, 4));
    prover.register_poseidon2_table::<4>(Poseidon2Config::KOALA_BEAR_D4_W32);
    prover.register_recompose_table::<4>(false);
    let proof = prover
        .prove_all_tables(&spend_traces(0), &cpd)
        .map_err(|e| format!("prove: {e:?}"))?;
    prover
        .verify_all_tables::<Challenge>(&proof)
        .map_err(|e| format!("native verify: {e:?}"))?;
    println!(
        "wide probe: spend proof with a 16-element W32 commitment proves and verifies natively, {:.1} KB",
        postcard::to_allocvec(&proof).map(|v| v.len()).unwrap_or(0) as f64 / 1024.0
    );

    let common = cpd.common_data();
    let nps = poseidon2_table_provers_d4::<rec16::MyConfig>(Poseidon2Config::KOALA_BEAR_D4_W32);
    let mut vcircuit = CircuitBuilder::<rec16::Challenge>::new();
    vcircuit.enable_poseidon2_perm::<KoalaBearD4Width16, _>(
        generate_poseidon2_trace::<rec16::Challenge, KoalaBearD4Width16>,
        default_koalabear_poseidon2_16(),
    );
    vcircuit.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<rec16::Challenge, KoalaBearD4Width32>,
        default_koalabear_poseidon2_32(),
    );
    vcircuit.enable_recompose::<rec16::F>(generate_recompose_trace::<rec16::F, rec16::Challenge>);
    let fri_vp = FriVerifierParams::with_mmcs(
        shape.log_blowup,
        0,
        shape.max_log_arity,
        0,
        rec::QUERY_POW_BITS,
        shape.num_queries,
        Poseidon2Config::KOALA_BEAR_D4_W32,
    );
    let lookup_gadget = LogUpGadget::new();
    let (vi, op_ids) = verify_p3_batch_proof_circuit::<
        rec16::MyConfig,
        MerkleCapTargets<rec16::F, 16>,
        InputProofTargets<rec16::F, rec16::Challenge, RecValMmcs<rec16::F, 16, rec16::MyHash, rec16::MyCompress>>,
        rec16::InnerFri,
        LogUpGadget,
        _,
        16,
        8,
        4,
    >(
        &config,
        &mut vcircuit,
        &proof,
        &fri_vp,
        common,
        &lookup_gadget,
        Poseidon2Config::KOALA_BEAR_D4_W16,
        &nps,
    )
    .map_err(|e| format!("in-circuit verifier build: {e:?}"))?;
    let vcirc = vcircuit.build().map_err(|e| format!("fold circuit build: {e:?}"))?;
    let pis: Vec<Vec<rec16::F>> = vec![vec![]; common.preprocessed.as_ref().map(|g| g.instances.len()).unwrap_or(0)];
    let (public, private) = vi.pack_values(&pis, &proof.proof, common);
    let mut runner = vcirc.runner();
    runner.set_public_inputs(&public).map_err(|e| format!("{e:?}"))?;
    runner.set_private_inputs(&private).map_err(|e| format!("{e:?}"))?;
    let OpeningTranscript { mut challenger, commitments_with_opening_points } =
        replay_batch_layer_transcript::<rec16::MyConfig, 4>(&config, &proof, common, &nps)
            .map_err(|e| format!("replay: {e:?}"))?;
    let (val_mmcs, fri_params) = rec16::fri_instance(shape);
    observe_opened_values::<rec16::MyConfig>(
        &mut challenger,
        &commitments_with_opening_points,
        fri_params.batch_proof_of_work_bits,
    );
    let claims: Vec<_> = commitments_with_opening_points.iter().cloned().map(Into::into).collect();
    let paths = restore_fri_query_paths(
        &fri_params,
        &val_mmcs,
        &val_mmcs,
        &proof.proof.opening_proof,
        &mut challenger,
        &claims,
    )
    .map_err(|e| format!("restore paths: {e:?}"))?;
    let siblings: usize = paths
        .iter()
        .map(|q| q.input.iter().chain(q.commit_phase.iter()).map(|p| p.len()).sum::<usize>())
        .sum();
    println!("wide probe: {} MMCS op ids, {} sibling digests in the proof", op_ids.len(), siblings);
    let mut idx = 0usize;
    for q in &paths {
        for p in q.input.iter().chain(q.commit_phase.iter()) {
            for sib in p3_recursion::pcs::convert_merkle_proof_to_siblings::<rec16::F, rec16::Challenge, 16>(p) {
                if idx >= op_ids.len() {
                    return Err(format!("more siblings than op ids at {idx}"));
                }
                runner
                    .set_private_data(
                        op_ids[idx],
                        p3_circuit::ops::perm_private_data(Poseidon2Config::KOALA_BEAR_D4_W32, sib.clone()),
                    )
                    .map_err(|e| format!("set_private_data failed at op {idx} (sibling limbs {}): {e:?}", sib.len()))?;
                idx += 1;
            }
        }
    }
    runner.run().map_err(|e| format!("in-circuit verification run: {e:?}"))?;
    println!("wide probe: the 16-element commitment proof VERIFIES IN-CIRCUIT on 485455c.");
    Ok(())
}
