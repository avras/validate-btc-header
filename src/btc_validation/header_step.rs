use std::marker::PhantomData;

use crate::btc_validation::{difficulty_update, hash_target, median, prev_block_hash};

use bellpepper_core::{
    // boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use nova_snark::traits::circuit::StepCircuit;

#[derive(Clone, Debug)]
pub struct block_header <F>
where
    F: PrimeField,
{
    msg_block: [u8; 80],
    prev_timestamps: [u32; 11],
    median: u32,
    marker: PhantomData<F>,
}

impl<F> Default for block_header <F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn default() -> Self {
        Self {
            msg_block: [0u8; 80],
            prev_timestamps: [0u32; 11],
            median: 0u32,
            marker: Default::default(),
        }
    }
}

impl<F> StepCircuit<F> for block_header <F>
where
    F: PrimeField + PrimeFieldBits,
{   
    fn arity(&self) -> usize {
        2
    }

    fn synthesize<CS: ConstraintSystem <F> >(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let header = self.msg_block;
        let prev_hash = &header[4..36];
        // let nTime = &header[68..72];
        let threshold = &header[72..76];
        let mut timestamps = self.prev_timestamps.to_vec();

        let res_median = median::verify_median_timestamp(cs.namespace(|| "median check"), &mut timestamps, self.median).unwrap();

        return Ok((*z).to_vec())
    }
}
