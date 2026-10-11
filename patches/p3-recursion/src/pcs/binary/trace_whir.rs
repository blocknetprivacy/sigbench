use alloc::vec::Vec;
use core::hash::Hash;

use p3_binary_field::{BinaryField128, TowerLevel};
use p3_challenger::{CanObserve, CanSampleUniformBits, FieldChallenger, GrindingChallenger};
use p3_circuit::ops::{BinaryTower128Target, ByteHash};
use p3_circuit::{CircuitBuilder, ExprId};
use p3_field::{ExtensionField, Field, PrimeField64};
use p3_merkle_tree::{MerkleCap, MerkleTreeMmcs};
use p3_multilinear_util::point::Point;
use p3_sumcheck::{OpeningBatch, OpeningProtocol};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use p3_whir::WhirConfig;

use super::trace_native::route;
use super::trace_plan::TracePlan;
use super::trace_routing::{TraceEntry, TraceRouting};
use super::whir_plan::invalid;
use super::{
    BinaryBooleanWhirInputShape, BinaryBooleanWhirProofTargets, BinaryBooleanWhirVerifier,
    NativeBinaryBooleanWhirInput,
};
use crate::verifier::{InputResourceUsage, VerificationError, VerifierLimits};
use crate::{BinaryQueryContinuation, BinaryTower128Challenger};

#[derive(Clone, Debug)]
pub struct BinaryBooleanWhirTraceVerifier {
    routing: TraceRouting<BinaryField128>,
    child: BinaryBooleanWhirVerifier,
    usage: InputResourceUsage,
}

#[derive(Clone, Debug)]
pub struct BinaryBooleanWhirTraceProofTargets {
    pub values: Vec<BinaryTower128Target>,
    pub opening: BinaryBooleanWhirProofTargets,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryBooleanWhirTraceInputShape {
    protocol: OpeningProtocol,
    value_count: usize,
    opening: BinaryBooleanWhirInputShape,
}

impl BinaryBooleanWhirTraceInputShape {
    pub(crate) fn native_decode_shape(
        &self,
    ) -> crate::artifact::binary_native::codec::BooleanTraceDecode<
        crate::artifact::binary_native::codec::WhirDecode,
    > {
        let (ring, packed) = self.opening.native_decode_shape();
        crate::artifact::binary_native::codec::BooleanTraceDecode {
            value_count: self.value_count,
            ring,
            packed,
        }
    }

    pub(crate) fn write_identity(
        &self,
        w: &mut crate::artifact::wire::Writer,
    ) -> Result<(), crate::artifact::ArtifactError> {
        let shapes = self.protocol.table_shapes();
        w.write_vec("binary WHIR trace tables", &shapes, |w, shape| {
            w.write_count("binary WHIR trace table height", shape.num_variables())?;
            w.write_count("binary WHIR trace table width", shape.width())
        })?;
        w.write_count("binary WHIR trace openings", self.protocol.num_openings())?;
        for (table, batch) in self.protocol.iter_openings() {
            w.write_count("binary WHIR trace opening table", table)?;
            for columns in [batch.current(), batch.next()] {
                w.write_vec(
                    "binary WHIR trace opening columns",
                    columns,
                    |w, &column| w.write_count("binary WHIR trace opening column", column),
                )?;
            }
        }
        self.opening.write_identity(w)
    }

    pub fn allocate_targets<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
    ) -> Result<BinaryBooleanWhirTraceProofTargets, VerificationError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        let values = (0..self.value_count)
            .map(|_| {
                let limbs = b.alloc_private_input_array::<8>("binary WHIR trace value");
                Ok(b.binary128_from_limbs::<BF>(limbs)?)
            })
            .collect::<Result<_, VerificationError>>()?;
        Ok(BinaryBooleanWhirTraceProofTargets {
            values,
            opening: self.opening.allocate_targets::<BF, EF>(b)?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct NativeBinaryBooleanWhirTraceInput {
    shape: BinaryBooleanWhirTraceInputShape,
    values: Vec<u128>,
    opening: NativeBinaryBooleanWhirInput,
}

impl NativeBinaryBooleanWhirTraceInput {
    pub const fn shape(&self) -> &BinaryBooleanWhirTraceInputShape {
        &self.shape
    }

    pub fn private_values<EF: Field>(
        &self,
        expected: &BinaryBooleanWhirTraceInputShape,
    ) -> Result<Vec<EF>, VerificationError> {
        if &self.shape != expected {
            return Err(invalid(
                "binary WHIR trace input belongs to another verifier",
            ));
        }
        let mut values = self
            .values
            .iter()
            .flat_map(|&v| (0..8).map(move |i| EF::from_u16((v >> (16 * i)) as u16)))
            .collect::<Vec<_>>();
        values.extend(self.opening.private_values::<EF>(&expected.opening)?);
        Ok(values)
    }
}

impl BinaryBooleanWhirTraceVerifier {
    pub fn new<C>(
        config: &WhirConfig<BinaryField128, BinaryField128, C>,
        protocol: OpeningProtocol,
        hash: ByteHash,
        cap_height: usize,
    ) -> Result<Self, VerificationError>
    where
        C: FieldChallenger<BinaryField128> + GrindingChallenger<Witness = BinaryField128>,
    {
        Self::with_limits(
            config,
            protocol,
            hash,
            cap_height,
            &VerifierLimits::default(),
        )
    }

    pub fn with_limits<C>(
        config: &WhirConfig<BinaryField128, BinaryField128, C>,
        protocol: OpeningProtocol,
        hash: ByteHash,
        cap_height: usize,
        limits: &VerifierLimits,
    ) -> Result<Self, VerificationError>
    where
        C: FieldChallenger<BinaryField128> + GrindingChallenger<Witness = BinaryField128>,
    {
        let n = config.num_variables().checked_add(7).ok_or(
            VerificationError::ResourceArithmeticOverflow {
                component: "binary WHIR trace bit arity",
            },
        )?;
        let plan = TracePlan::new(protocol, n, limits)?;
        let child = BinaryBooleanWhirVerifier::with_limits(
            config,
            plan.specs.clone(),
            hash,
            cap_height,
            limits,
        )?;
        let mut usage = plan.usage;
        usage.merge(limits, child.input_resource_usage())?;
        Ok(Self {
            routing: TraceRouting::new(plan)?,
            child,
            usage,
        })
    }

    pub const fn input_resource_usage(&self) -> InputResourceUsage {
        self.usage
    }

    pub fn input_shape(&self) -> BinaryBooleanWhirTraceInputShape {
        BinaryBooleanWhirTraceInputShape {
            protocol: self.routing.plan.protocol.clone(),
            value_count: self.routing.plan.value_count,
            opening: self.child.input_shape(),
        }
    }

    pub(crate) fn check_targets(
        &self,
        cap: &[Vec<ExprId>],
        points: &[Vec<BinaryTower128Target>],
        proof: &BinaryBooleanWhirTraceProofTargets,
    ) -> Result<(), VerificationError> {
        self.routing
            .check_points(points.iter().map(Vec::len), proof.values.len())?;
        self.child.check_targets(cap, &proof.opening)
    }

    pub fn observe_commitment<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        ch: &mut BinaryTower128Challenger,
        cap: &[Vec<ExprId>],
    ) -> Result<(), VerificationError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.child.observe_commitment::<BF, EF>(b, ch, cap)
    }

    pub fn verify_at<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        ch: BinaryTower128Challenger,
        cap: &[Vec<ExprId>],
        points: &[Vec<BinaryTower128Target>],
        proof: &BinaryBooleanWhirTraceProofTargets,
    ) -> Result<
        (
            Vec<OpeningBatch<BinaryTower128Target>>,
            BinaryTower128Challenger,
        ),
        VerificationError,
    >
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.verify_impl::<BF, EF>(b, TraceEntry::Ready(ch), cap, points, proof)
    }

    pub fn verify_at_after_queries<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        continuation: BinaryQueryContinuation,
        cap: &[Vec<ExprId>],
        points: &[Vec<BinaryTower128Target>],
        proof: &BinaryBooleanWhirTraceProofTargets,
    ) -> Result<
        (
            Vec<OpeningBatch<BinaryTower128Target>>,
            BinaryTower128Challenger,
        ),
        VerificationError,
    >
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.verify_impl::<BF, EF>(
            b,
            TraceEntry::AfterQueries(continuation),
            cap,
            points,
            proof,
        )
    }

    fn verify_impl<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        entry: TraceEntry,
        cap: &[Vec<ExprId>],
        points: &[Vec<BinaryTower128Target>],
        proof: &BinaryBooleanWhirTraceProofTargets,
    ) -> Result<
        (
            Vec<OpeningBatch<BinaryTower128Target>>,
            BinaryTower128Challenger,
        ),
        VerificationError,
    >
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.check_targets(cap, points, proof)?;
        let entry = self.routing.bind::<BF, EF>(
            b,
            entry,
            points,
            &proof.values,
            &proof.opening.reduction.claims,
        )?;
        let ch = match entry {
            TraceEntry::Ready(ch) => {
                self.child
                    .verify_readings::<BF, EF>(b, ch, cap, &proof.opening)?
            }
            TraceEntry::AfterQueries(token) => {
                self.child
                    .verify_readings_after_queries::<BF, EF>(b, token, cap, &proof.opening)?
            }
        };
        Ok((self.routing.evals(&proof.values), ch))
    }

    pub(crate) fn check_native_structure_with_usage<C, H, Co>(
        &self,
        config: &WhirConfig<BinaryField128, BinaryField128, C>,
        mmcs: &MerkleTreeMmcs<BinaryField128, u8, H, Co, 2, 32>,
        commitment: &MerkleCap<BinaryField128, [u8; 32]>,
        points: &[Point<BinaryField128>],
        proof: &super::ByteMerkleBooleanWhirTraceProof<BinaryField128, H, Co>,
        usage: &mut InputResourceUsage,
    ) -> Result<(), VerificationError>
    where
        C: FieldChallenger<BinaryField128> + GrindingChallenger<Witness = BinaryField128>,
        H: CryptographicHasher<BinaryField128, [u8; 32]> + Sync,
        Co: PseudoCompressionFunction<[u8; 32], 2> + Sync,
    {
        self.routing
            .check_points(points.iter().map(Point::num_variables), proof.values.len())?;
        self.child.check_native_structure_with_usage(
            config,
            mmcs,
            commitment,
            &proof.opening,
            usage,
        )
    }

    pub fn import_native<C, Ch, H, Co>(
        &self,
        config: &WhirConfig<BinaryField128, BinaryField128, C>,
        mmcs: &MerkleTreeMmcs<BinaryField128, u8, H, Co, 2, 32>,
        commitment: &MerkleCap<BinaryField128, [u8; 32]>,
        points: &[Point<BinaryField128>],
        proof: &super::ByteMerkleBooleanWhirTraceProof<BinaryField128, H, Co>,
        target_challenger: &mut Ch,
    ) -> Result<NativeBinaryBooleanWhirTraceInput, VerificationError>
    where
        C: FieldChallenger<BinaryField128> + GrindingChallenger<Witness = BinaryField128>,
        H: CryptographicHasher<BinaryField128, [u8; 32]> + Sync,
        Co: PseudoCompressionFunction<[u8; 32], 2> + Sync,
        Ch: Clone
            + FieldChallenger<BinaryField128>
            + CanSampleUniformBits<BinaryField128>
            + GrindingChallenger<Witness = BinaryField128>
            + CanObserve<MerkleCap<BinaryField128, [u8; 32]>>,
    {
        self.check_native_structure_with_usage(
            config,
            mmcs,
            commitment,
            points,
            proof,
            &mut InputResourceUsage::default(),
        )?;
        let mut ch = target_challenger.clone();
        let plan = &self.routing.plan;
        let captured = route(
            plan.num_variables,
            &plan.protocol,
            points,
            &proof.values,
            &mut ch,
        )?;
        let lifted = captured
            .openings
            .iter()
            .map(|o| o.point.clone())
            .collect::<Vec<_>>();
        let readings = captured
            .readings
            .iter()
            .map(|r| (r.current, r.next))
            .collect::<Vec<_>>();
        let opening = self.child.import_native(
            config,
            mmcs,
            commitment,
            &lifted,
            &readings,
            &proof.opening,
            &mut ch,
        )?;
        *target_challenger = ch;
        Ok(NativeBinaryBooleanWhirTraceInput {
            shape: self.input_shape(),
            values: proof.values.iter().map(|v| v.to_repr()).collect(),
            opening,
        })
    }
}
