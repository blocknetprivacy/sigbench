use p3_binary_field::{Poly64, Poly192, TowerLevel};
use p3_field::{Field, PrimeCharacteristicRing};

use super::*;

pub(in crate::artifact::binary_native) trait ScalarWire:
    Field
{
    const WIRE_BYTES: usize;
    const INPUT_LIMBS: usize;
    fn write_le(self, w: &mut Writer) -> Result<(), ArtifactError>;
    fn read_le(r: &mut Reader<'_>) -> Result<Self, ArtifactError>;
}

impl<F: RecursiveBinaryTowerField> ScalarWire for F {
    const WIRE_BYTES: usize = F::RAW_BITS / 8;
    const INPUT_LIMBS: usize = 8;
    fn write_le(self, w: &mut Writer) -> Result<(), ArtifactError> {
        w.write_bytes(&self.raw_coordinates().to_le_bytes()[..Self::WIRE_BYTES])
    }
    fn read_le(r: &mut Reader<'_>) -> Result<Self, ArtifactError> {
        Ok(Self::from_le_byte_iter(
            r.read_bytes(Self::WIRE_BYTES)?.iter().copied(),
        ))
    }
}

impl ScalarWire for Poly64 {
    const WIRE_BYTES: usize = 8;
    const INPUT_LIMBS: usize = 4;
    fn write_le(self, w: &mut Writer) -> Result<(), ArtifactError> {
        w.write_bytes(&self.to_repr().to_le_bytes())
    }
    fn read_le(r: &mut Reader<'_>) -> Result<Self, ArtifactError> {
        Ok(Self::new(u64::from_le_bytes(
            r.read_bytes(8)?.try_into().unwrap(),
        )))
    }
}

impl ScalarWire for Poly192 {
    const WIRE_BYTES: usize = 24;
    const INPUT_LIMBS: usize = 12;
    fn write_le(self, w: &mut Writer) -> Result<(), ArtifactError> {
        for coefficient in self.coefficients() {
            coefficient.write_le(w)?;
        }
        Ok(())
    }
    fn read_le(r: &mut Reader<'_>) -> Result<Self, ArtifactError> {
        let mut coefficients = [Poly64::ZERO; 3];
        for coefficient in &mut coefficients {
            *coefficient = Poly64::read_le(r)?;
        }
        Ok(Self::new(coefficients))
    }
}
