use alloc::vec::Vec;
use core::hash::Hash;

use p3_circuit::ops::binary_encoding::PrimeBinaryEncoding;
use p3_circuit::ops::binary_host::BinaryCircuitHost;
use p3_circuit::ops::{BinaryPoly64Target, BinaryPoly192Target, BinaryTower128Target, ByteHash};
use p3_circuit::{CircuitBuilder, CircuitBuilderError, ExprId};
use p3_field::{ExtensionField, Field, PrimeField64};

#[derive(Clone, Debug)]
pub struct BinaryTower128Challenger {
    hash: ByteHash,
    input_buffer: Vec<ExprId>,
    output_buffer: Vec<ExprId>,
}

#[derive(Debug)]
pub struct BinaryQueryContinuation {
    hash: ByteHash,
    digest: [ExprId; 32],
}

impl BinaryQueryContinuation {
    pub(crate) const fn from_digest(hash: ByteHash, digest: [ExprId; 32]) -> Self {
        Self { hash, digest }
    }

    pub fn resume_with_observation<BF, EF>(
        self,
        circuit: &mut CircuitBuilder<EF>,
        bytes: &[ExprId],
    ) -> Result<BinaryTower128Challenger, CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.resume_with_observation_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, bytes)
    }

    pub fn resume_with_observation_with_host<H, EF>(
        self,
        circuit: &mut CircuitBuilder<EF>,
        bytes: &[ExprId],
    ) -> Result<BinaryTower128Challenger, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        if bytes.is_empty() {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "BinaryQueryContinuation",
                expected: "a nonempty next observation".into(),
                got: 0,
            });
        }
        let mut challenger = BinaryTower128Challenger {
            hash: self.hash,
            input_buffer: self.digest.to_vec(),
            output_buffer: Vec::new(),
        };
        challenger.observe_bytes_with_host::<H, EF>(circuit, bytes)?;
        Ok(challenger)
    }
}

impl BinaryTower128Challenger {
    pub(crate) fn retained_query_digest(
        &self,
    ) -> Result<(ByteHash, [ExprId; 32]), CircuitBuilderError> {
        let digest = self.input_buffer.as_slice().try_into().map_err(|_| {
            CircuitBuilderError::NonPrimitiveOpArity {
                op: "BinaryQueryDigest",
                expected: "32 retained bytes after a query draw".into(),
                got: self.input_buffer.len(),
            }
        })?;
        Ok((self.hash, digest))
    }

    pub(crate) fn select_same_shape<EF: p3_field::Field + Eq + Hash>(
        circuit: &mut CircuitBuilder<EF>,
        branches: &[(ExprId, Self)],
    ) -> Result<Self, CircuitBuilderError> {
        let Some((_, first)) = branches.first() else {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "BinaryChallengerSelect",
                expected: "at least one branch".into(),
                got: 0,
            });
        };
        if branches.iter().any(|(_, branch)| {
            branch.hash != first.hash
                || branch.input_buffer.len() != first.input_buffer.len()
                || branch.output_buffer.len() != first.output_buffer.len()
        }) {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "BinaryChallengerSelect",
                expected: "matching hashes and buffer lengths".into(),
                got: branches.len(),
            });
        }
        let selectors: Vec<_> = branches.iter().map(|(selector, _)| *selector).collect();
        circuit.assert_exactly_one(&selectors)?;
        let mut select = |output: bool, len: usize| {
            (0..len)
                .map(|i| {
                    branches
                        .iter()
                        .fold(ExprId::ZERO, |sum, (selector, branch)| {
                            let byte = if output {
                                branch.output_buffer[i]
                            } else {
                                branch.input_buffer[i]
                            };
                            circuit.mul_add(*selector, byte, sum)
                        })
                })
                .collect()
        };
        let input_buffer = select(false, first.input_buffer.len());
        let output_buffer = select(true, first.output_buffer.len());
        Ok(Self {
            hash: first.hash,
            input_buffer,
            output_buffer,
        })
    }

    pub const fn new(hash: ByteHash) -> Self {
        Self {
            hash,
            input_buffer: Vec::new(),
            output_buffer: Vec::new(),
        }
    }

    pub fn with_initial_limbs<BF, EF>(
        circuit: &mut CircuitBuilder<EF>,
        hash: ByteHash,
        initial: &[ExprId],
    ) -> Result<Self, CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        Self::with_initial_limbs_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, hash, initial)
    }

    pub fn with_initial_limbs_with_host<H, EF>(
        circuit: &mut CircuitBuilder<EF>,
        hash: ByteHash,
        initial: &[ExprId],
    ) -> Result<Self, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(hash)?;
        let bytes = Self::bytes_from_limbs::<H, EF>(circuit, initial)?;
        Ok(Self {
            hash,
            input_buffer: bytes,
            output_buffer: Vec::new(),
        })
    }

    pub fn with_initial_bytes<BF, EF>(
        circuit: &mut CircuitBuilder<EF>,
        hash: ByteHash,
        initial: &[ExprId],
    ) -> Result<Self, CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        Self::with_initial_bytes_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, hash, initial)
    }

    pub fn with_initial_bytes_with_host<H, EF>(
        circuit: &mut CircuitBuilder<EF>,
        hash: ByteHash,
        initial: &[ExprId],
    ) -> Result<Self, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(hash)?;
        for &byte in initial {
            H::decompose_word(circuit, byte, 8)?;
        }
        Ok(Self {
            hash,
            input_buffer: initial.to_vec(),
            output_buffer: Vec::new(),
        })
    }

    pub fn observe_bytes<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        bytes: &[ExprId],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.observe_bytes_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, bytes)
    }

    pub fn observe_bytes_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        bytes: &[ExprId],
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        for &byte in bytes {
            H::decompose_word(circuit, byte, 8)?;
        }
        if !bytes.is_empty() {
            self.output_buffer.clear();
            self.input_buffer.extend_from_slice(bytes);
        }
        Ok(())
    }

    pub fn sample_bytes<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        count: usize,
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_bytes_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, count)
    }

    pub fn sample_bytes_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        count: usize,
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        let result = staged.sample_stream_bytes::<H, EF>(circuit, count)?;
        *self = staged;
        Ok(result)
    }

    pub fn observe_poly64<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        value: &BinaryPoly64Target,
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.observe_poly64_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, value)
    }

    pub fn observe_poly64_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        value: &BinaryPoly64Target,
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let bytes = value
            .bits()
            .as_chunks::<8>()
            .0
            .iter()
            .map(|bits| H::recompose_word(circuit, bits))
            .collect::<Result<Vec<_>, _>>()?;
        self.observe_bytes_with_host::<H, EF>(circuit, &bytes)
    }

    pub fn observe_poly192<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        value: &BinaryPoly192Target,
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.observe_poly192_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, value)
    }

    pub fn observe_poly192_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        value: &BinaryPoly192Target,
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        for coefficient in value.coefficients() {
            staged.observe_poly64_with_host::<H, EF>(circuit, coefficient)?;
        }
        *self = staged;
        Ok(())
    }

    pub fn sample_poly192<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
    ) -> Result<BinaryPoly192Target, CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_poly192_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit)
    }

    pub fn sample_poly192_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
    ) -> Result<BinaryPoly192Target, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        let bytes = staged.sample_bytes_with_host::<H, EF>(circuit, 24)?;
        let coefficients = bytes
            .as_chunks::<8>()
            .0
            .iter()
            .map(|bytes| {
                let mut bits = Vec::with_capacity(64);
                for &byte in bytes {
                    bits.extend(H::decompose_word(circuit, byte, 8)?);
                }
                circuit.binary_poly64_from_bits(bits.try_into().expect("eight bytes have 64 bits"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result = circuit.binary_poly192_from_coefficients(
            coefficients
                .try_into()
                .expect("Poly192 has three coefficients"),
        );
        *self = staged;
        Ok(result)
    }

    pub fn observe<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        value: &BinaryTower128Target,
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.observe_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, value)
    }

    pub fn observe_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        value: &BinaryTower128Target,
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        staged.observe_inner::<H, EF>(circuit, value)?;
        *self = staged;
        Ok(())
    }

    pub fn observe_slice<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        values: &[BinaryTower128Target],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.observe_slice_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, values)
    }

    pub fn observe_slice_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        values: &[BinaryTower128Target],
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        for value in values {
            staged.observe_inner::<H, EF>(circuit, value)?;
        }
        *self = staged;
        Ok(())
    }

    pub fn observe_digest<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        digest: &[ExprId; 16],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.observe_digest_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, digest)
    }

    pub fn observe_digest_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        digest: &[ExprId; 16],
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        let bytes = Self::bytes_from_limbs::<H, EF>(circuit, digest)?;
        staged.output_buffer.clear();
        staged.input_buffer.extend(bytes);
        *self = staged;
        Ok(())
    }

    pub fn sample<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
    ) -> Result<BinaryTower128Target, CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit)
    }

    pub fn sample_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
    ) -> Result<BinaryTower128Target, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        let stream = staged.sample_stream_bytes::<H, EF>(circuit, 16)?;
        let mut bits = Vec::with_capacity(128);
        for byte in stream {
            bits.extend(H::decompose_word(circuit, byte, 8)?);
        }
        let result = circuit.binary128_from_bits(
            bits.try_into()
                .expect("sixteen sampled bytes form one binary tower element"),
        )?;
        *self = staged;
        Ok(result)
    }

    pub fn sample_bits<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        bits: usize,
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_bits_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, bits)
    }

    pub fn sample_bits_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        bits: usize,
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        Self::check_bit_count(bits)?;
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        let result = staged.sample_bits_inner::<H, EF>(circuit, bits)?;
        *self = staged;
        Ok(result)
    }

    pub fn check_witness<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        bits: usize,
        witness: &BinaryTower128Target,
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.check_witness_with_host::<PrimeBinaryEncoding<BF>, EF>(circuit, bits, witness)
    }

    pub fn check_witness_with_host<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        bits: usize,
        witness: &BinaryTower128Target,
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        if bits == 0 {
            return Ok(());
        }
        Self::check_bit_count(bits)?;
        H::check_hash(self.hash)?;
        let mut staged = self.clone();
        staged.observe_inner::<H, EF>(circuit, witness)?;
        for bit in staged.sample_bits_inner::<H, EF>(circuit, bits)? {
            circuit.assert_zero(bit);
        }
        *self = staged;
        Ok(())
    }

    fn observe_inner<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        value: &BinaryTower128Target,
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        let bytes: Vec<_> = value
            .bits()
            .chunks(8)
            .map(|bits| H::recompose_word(circuit, bits))
            .collect::<Result<_, _>>()?;
        self.output_buffer.clear();
        self.input_buffer.extend(bytes);
        Ok(())
    }

    fn sample_bits_inner<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        bits: usize,
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        let stream = self.sample_stream_bytes::<H, EF>(circuit, 8)?;
        let mut result = Vec::with_capacity(bits);
        for byte in stream {
            result.extend(H::decompose_word(circuit, byte, 8)?);
        }
        result.truncate(bits);
        Ok(result)
    }

    fn sample_stream_bytes<H, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        count: usize,
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        let mut stream = Vec::with_capacity(count);
        while stream.len() < count {
            if self.output_buffer.is_empty() {
                let bytes = H::hash_bytes(circuit, self.hash, &self.input_buffer)?.to_vec();
                self.input_buffer.clone_from(&bytes);
                self.output_buffer = bytes;
            }
            stream.push(
                self.output_buffer
                    .pop()
                    .expect("a byte hash refill yields thirty-two digest bytes"),
            );
        }
        Ok(stream)
    }

    fn bytes_from_limbs<H, EF>(
        circuit: &mut CircuitBuilder<EF>,
        limbs: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        H::bytes_from_words(circuit, limbs)
    }

    const fn check_bit_count(bits: usize) -> Result<(), CircuitBuilderError> {
        if bits >= usize::BITS as usize {
            return Err(CircuitBuilderError::BinaryDecompositionTooManyBits {
                expected: usize::BITS as usize - 1,
                n_bits: bits,
            });
        }
        Ok(())
    }
}
