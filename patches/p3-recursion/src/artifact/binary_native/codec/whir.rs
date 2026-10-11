use p3_binary_field::BinaryField128;
use p3_binary_pcs::whir::BinaryWhirDomain;
use p3_whir::WhirDomain;
use p3_whir::pcs::proof::{PcsProof, QueryOpenings, SharedProofOpening, WhirProof, WhirRoundProof};

use super::super::{
    BinaryNativeWhirAuthority, BinaryNativeWhirConfig, BinaryNativeWhirLayout,
    VerifiedBinaryNativeWhirProof,
};
use super::*;
use crate::pcs::binary::RecursiveBinaryWhirTowerField;

impl<F, A, L> BinaryNativeWhirAuthority<F, A, L>
where
    F: RecursiveBinaryWhirTowerField
        + EncodableLevel
        + FoldAlphabet<BinaryField128>
        + PackedValue<Value = F>
        + Ord,
    BinaryField128: ExtensionField<F> + ChallengeField<F>,
    BinaryWhirDomain<F>: WhirDomain<F, BinaryField128>,
    L: BinaryNativeWhirLayout<F>,
    A: VerifierAir<F, BinaryField128>,
{
    pub fn encode_statement(&self, public: &[Vec<F>]) -> Result<Vec<u8>, ArtifactError> {
        self.state
            .check_public(public)
            .map_err(|_| ArtifactError::VerificationRejected)?;
        let mut writer = Writer::new(self.state.limits.max_proof_bytes);
        write_public(&mut writer, public)?;
        writer.finish()
    }
    pub fn encode_native_proof(
        &self,
        proof: &MultiStarkProof<BinaryNativeWhirConfig<F, L>>,
        public: &[Vec<F>],
    ) -> Result<Vec<u8>, ArtifactError> {
        self.verify_native(proof, public)
            .map_err(|_| ArtifactError::VerificationRejected)?;
        encode_multi::<BinaryNativeWhirConfig<F, L>>(
            proof,
            public,
            suite::<F, BinaryField128>() | 0x400,
            &self.state.limits,
            write_whir::<F>,
        )
    }
    pub fn decode_and_verify(
        &self,
        candidate: &[u8],
        expected: ExpectedVerifierArtifact<'_>,
        proof_bytes: &[u8],
        statement: CanonicalBinaryStatement<'_>,
    ) -> Result<VerifiedBinaryNativeWhirProof<F>, ArtifactError> {
        let authority = DecodeAuthority {
            identity: &self.state.identity,
            shape: &self.state.decode,
            limits: &self.state.limits,
            usage: self.state.binary.input_resource_usage(),
            suite: suite::<F, BinaryField128>() | 0x400,
        };
        let (proof, public) = authority.decode::<BinaryNativeWhirConfig<F, L>>(
            candidate,
            expected,
            proof_bytes,
            statement,
            read_whir::<F>,
        )?;
        self.verify_native(&proof, &public)
            .map_err(|_| ArtifactError::VerificationRejected)
    }
}

type NativeWhirProof<F, E = BinaryField128> = PcsProof<F, E, NativeMmcs<F>>;

pub(super) fn write_whir<F>(w: &mut Writer, p: &NativeWhirProof<F>) -> Result<(), ArtifactError>
where
    F: RecursiveBinaryTowerField + PackedValue<Value = F>,
{
    write_whir_with::<F, BinaryField128>(w, p)
}
pub(super) fn read_whir<F>(
    r: &mut Reader<'_>,
    s: &WhirDecode,
    total: &mut usize,
) -> Result<NativeWhirProof<F>, ArtifactError>
where
    F: RecursiveBinaryTowerField + PackedValue<Value = F>,
{
    read_whir_with::<F, BinaryField128>(r, s, total)
}

pub(super) fn write_whir_with<F, E>(
    w: &mut Writer,
    p: &NativeWhirProof<F, E>,
) -> Result<(), ArtifactError>
where
    F: ScalarWire + PackedValue<Value = F>,
    E: ScalarWire,
{
    for batch in &p.evals {
        write_fields(w, batch.current())?;
        write_fields(w, batch.next())?;
    }
    write_fields(w, &p.whir.initial_ood_answers)?;
    write_fold(w, &p.whir.initial_sumcheck)?;
    for round in &p.whir.rounds {
        write_cap(
            w,
            round
                .commitment
                .as_ref()
                .ok_or_else(|| malformed("binary WHIR round cap"))?,
        )?;
        write_fields(w, &round.ood_answers)?;
        write_field(w, round.pow_witness)?;
        write_opening(w, &round.openings)?;
        write_fold(w, &round.sumcheck)?;
    }
    write_fields(
        w,
        p.whir
            .final_poly
            .as_ref()
            .ok_or_else(|| malformed("binary WHIR final polynomial"))?
            .as_slice(),
    )?;
    write_field(w, p.whir.final_pow_witness)?;
    write_opening(w, &p.whir.final_openings)?;
    if let Some(fold) = &p.whir.final_sumcheck {
        write_fold(w, fold)?;
    }
    Ok(())
}
fn write_fold<F: ScalarWire, E: ScalarWire>(
    w: &mut Writer,
    p: &SumcheckData<F, E>,
) -> Result<(), ArtifactError> {
    for pair in &p.polynomial_evaluations {
        write_fields(w, pair)?;
    }
    write_fields(w, &p.pow_witnesses)
}
fn write_opening<F: ScalarWire, E: ScalarWire>(
    w: &mut Writer,
    p: &QueryOpenings<F, E, PrunedMerklePaths<u8, 32>>,
) -> Result<(), ArtifactError> {
    match p {
        QueryOpenings::Base(o) => {
            for row in &o.rows {
                write_fields(w, row)?;
            }
            write_frontier(w, &o.proof)
        }
        QueryOpenings::Extension(o) => {
            for row in &o.rows {
                write_fields(w, row)?;
            }
            write_frontier(w, &o.proof)
        }
    }
}
fn read_fold<F: ScalarWire, E: ScalarWire>(
    r: &mut Reader<'_>,
    s: &WhirFoldDecode,
) -> Result<SumcheckData<F, E>, ArtifactError> {
    Ok(SumcheckData {
        polynomial_evaluations: r.read_exact_items(
            "binary WHIR fold rounds",
            s.rounds,
            checked_product(2, E::WIRE_BYTES)?,
            read_array::<E, 2>,
        )?,
        pow_witnesses: read_fields(r, s.pow_count)?,
    })
}
fn read_opening<F: ScalarWire, E: ScalarWire>(
    r: &mut Reader<'_>,
    s: &WhirSiteDecode,
    base: bool,
    total: &mut usize,
) -> Result<QueryOpenings<F, E, PrunedMerklePaths<u8, 32>>, ArtifactError> {
    fn rows<T: ScalarWire>(
        r: &mut Reader<'_>,
        s: &WhirSiteDecode,
    ) -> Result<Vec<Vec<T>>, ArtifactError> {
        r.read_exact_items(
            "binary WHIR query rows",
            s.oracle.rows,
            checked_product(s.width, T::WIRE_BYTES)?,
            |r| read_fields(r, s.width),
        )
    }
    if base {
        Ok(QueryOpenings::Base(SharedProofOpening {
            rows: rows(r, s)?,
            proof: read_frontier(r, &s.oracle, total)?,
        }))
    } else {
        Ok(QueryOpenings::Extension(SharedProofOpening {
            rows: rows(r, s)?,
            proof: read_frontier(r, &s.oracle, total)?,
        }))
    }
}
fn read_query_pow<F: ScalarWire>(
    r: &mut Reader<'_>,
    site: &WhirSiteDecode,
) -> Result<F, ArtifactError> {
    let witness = read_field::<F>(r)?;
    if site.query_pow_bits == 0 && witness != F::ZERO {
        return Err(malformed("binary WHIR disabled query PoW witness"));
    }
    Ok(witness)
}
pub(super) fn read_whir_with<F, E>(
    r: &mut Reader<'_>,
    s: &WhirDecode,
    total: &mut usize,
) -> Result<NativeWhirProof<F, E>, ArtifactError>
where
    F: ScalarWire + PackedValue<Value = F>,
    E: ScalarWire,
{
    let evals = r.read_exact_items("binary WHIR opening batches", s.eval_widths.len(), 0, {
        let mut index = 0;
        move |r| {
            let (current, next) = s.eval_widths[index];
            index += 1;
            Ok(OpeningBatch::new(
                read_fields(r, current)?,
                read_fields(r, next)?,
            ))
        }
    })?;
    let initial_ood_answers = read_fields(r, s.initial_ood)?;
    let initial_sumcheck = read_fold(r, &s.initial_fold)?;
    let last = s
        .sites
        .last()
        .ok_or_else(|| malformed("binary WHIR query sites"))?;
    let round_total = &mut *total;
    let rounds = r.read_exact_items("binary WHIR intermediate rounds", s.sites.len() - 1, 0, {
        let mut index = 0;
        move |r| {
            let site = &s.sites[index];
            let base = index == 0;
            index += 1;
            Ok(WhirRoundProof {
                commitment: Some(read_cap(r, s.cap_roots)?),
                ood_answers: read_fields(r, site.ood)?,
                pow_witness: read_query_pow(r, site)?,
                openings: read_opening(r, site, base, round_total)?,
                sumcheck: read_fold(r, &site.fold)?,
            })
        }
    })?;
    let final_poly = Some(Poly::new(read_fields(r, s.final_poly_len)?));
    let final_pow_witness = read_query_pow(r, last)?;
    let final_openings = read_opening(r, last, s.sites.len() == 1, total)?;
    let final_sumcheck = if last.fold.rounds == 0 {
        None
    } else {
        Some(read_fold(r, &last.fold)?)
    };
    Ok(PcsProof {
        evals,
        whir: WhirProof {
            initial_ood_answers,
            initial_sumcheck,
            rounds,
            final_poly,
            final_pow_witness,
            final_openings,
            final_sumcheck,
        },
    })
}
