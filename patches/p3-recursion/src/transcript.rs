use alloc::vec::Vec;

use p3_challenger::fs::{DomainSeparator, FieldUnit, TranscriptField, TypeTag};
use p3_challenger::{
    CanObserve, CanSample, CanSampleBits, CanSampleUniformBits, FieldChallenger, GrindingChallenger,
};
use p3_field::{ExtensionField, Field, PrimeField64};
use p3_lookup::LookupProtocol;
use p3_uni_stark::StarkShape;

use crate::traits::RecursiveAir;

struct SeedRecorder<F>(Vec<F>);

impl<F> CanObserve<F> for SeedRecorder<F> {
    fn observe(&mut self, value: F) {
        self.0.push(value);
    }
}

#[must_use]
pub fn domain_separator_seed<F: TranscriptField>(
    separator: &DomainSeparator<FieldUnit<F>>,
) -> Vec<F> {
    let mut recorder = SeedRecorder(Vec::new());
    separator.seed(&mut recorder);
    recorder.0
}

#[derive(Clone, Debug, Default)]
pub struct SeedTap<F> {
    observed: Vec<F>,
    sampled: bool,
}

impl<F> SeedTap<F> {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            observed: Vec::new(),
            sampled: false,
        }
    }
}

impl<F: PrimeField64> SeedTap<F> {
    #[must_use]
    pub fn seed(&self) -> Vec<F> {
        let bits = u64::BITS - F::ORDER_U64.leading_zeros();
        let bytes_per_element = ((bits as usize) - 1) / 8;
        let byte_len = self
            .observed
            .first()
            .expect("a native sub-transcript always opens with its seed")
            .as_canonical_u64() as usize;
        let len = 1 + byte_len.div_ceil(bytes_per_element);
        assert!(
            self.observed.len() >= len,
            "the tap recorded a truncated seed"
        );
        self.observed[..len].to_vec()
    }
}

impl<F: TranscriptField> SeedTap<F> {
    #[must_use]
    pub fn binary_seed(&self) -> Vec<F> {
        assert!(
            matches!(
                F::algebra_tag(1, [0; 32]),
                TypeTag::BinaryTower { .. } | TypeTag::BinaryPolynomial { .. }
            ),
            "binary seed capture requires a native binary alphabet"
        );
        let width = F::wire_len();
        assert!(matches!(width, 1 | 2 | 4 | 8 | 16));
        let prefix_len = 8usize.div_ceil(width);
        assert!(
            self.observed.len() >= prefix_len,
            "the tap recorded a truncated binary length prefix"
        );
        let mut length_bytes = Vec::with_capacity(prefix_len * width);
        for element in &self.observed[..prefix_len] {
            let mut encoded = Vec::with_capacity(width);
            F::encode(element, &mut encoded);
            length_bytes.extend(encoded.into_iter().rev());
        }
        let byte_len = usize::try_from(u64::from_le_bytes(
            length_bytes[..8].try_into().expect("eight length bytes"),
        ))
        .expect("a recorded native seed length fits usize");
        let len = prefix_len
            .checked_add(byte_len.div_ceil(width))
            .expect("a recorded native seed length fits usize");
        assert!(
            self.observed.len() >= len,
            "the tap recorded a truncated seed"
        );
        self.observed[..len].to_vec()
    }
}

impl<F: Clone> CanObserve<F> for SeedTap<F> {
    fn observe(&mut self, value: F) {
        if !self.sampled {
            self.observed.push(value);
        }
    }
}

impl<F: Field> CanSample<F> for SeedTap<F> {
    fn sample(&mut self) -> F {
        self.sampled = true;
        F::ZERO
    }
}

impl<F> CanSampleBits<usize> for SeedTap<F> {
    fn sample_bits(&mut self, _bits: usize) -> usize {
        self.sampled = true;
        0
    }
}

impl<F: Field> CanSampleUniformBits<F> for SeedTap<F> {
    fn sample_uniform_bits<const RESAMPLE: bool>(
        &mut self,
        _bits: usize,
    ) -> Result<usize, p3_challenger::ResamplingError> {
        self.sampled = true;
        Ok(0)
    }
}

impl<F: Field> FieldChallenger<F> for SeedTap<F> {}

impl<F: Field> GrindingChallenger for SeedTap<F> {
    type Witness = F;

    fn grind(&mut self, _bits: usize) -> F {
        F::ZERO
    }
}

#[allow(clippy::too_many_arguments)]
#[must_use]
pub fn uni_stark_shape<F, EF, LG, A>(
    air: &A,
    preprocessed_width: usize,
    num_public_values: usize,
    log_ext_degree: usize,
    log_degree: usize,
    num_quotient_chunks: usize,
    has_randomization: bool,
    ood_pow_bits: usize,
) -> StarkShape
where
    F: PrimeField64,
    EF: ExtensionField<F>,
    LG: LookupProtocol,
    A: RecursiveAir<F, EF, LG> + ?Sized,
{
    StarkShape {
        log_ext_degree,
        log_degree,
        main_width: air.width(),
        preprocessed_width,
        num_public_values,
        num_periodic_columns: air.num_periodic_columns(),
        num_quotient_chunks,
        opens_main_next_row: air.opens_trace_next(),
        opens_preprocessed_next_row: air.opens_preprocessed_next(),
        has_randomization,
        ood_pow_bits,
    }
}
