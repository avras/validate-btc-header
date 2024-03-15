use std::marker::PhantomData;

use crate::btc_validation::{difficulty_update, hash_target, median, prev_block_hash};

use bellpepper_core::{
    boolean,
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use bellpepper::gadgets::sha256;
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
        // z contains previous block to hash maybe ??
        // prev. target and t_sum for difficulty update also in z?

        let header = self.msg_block.to_vec();
        
        let mut preimage_vec: Vec<boolean::Boolean> = Vec::new();
        for (i, preimage64) in header[4..36].iter().enumerate() {
            let mut dummy2 = boolean::u64_into_boolean_vec_le(cs.namespace(|| format!("dummy2 {}", i)), Some(*preimage64 as u64)).unwrap();
            dummy2.reverse();
            dummy2 = dummy2[0..8].to_vec();
            preimage_vec.append(&mut dummy2);
        }

        let out_sha256 = sha256::sha256(cs.namespace(|| "SHA 256"), &preimage_vec).unwrap();
        let out_sha256d = sha256::sha256(cs.namespace(|| "SHA 256d"), &out_sha256).unwrap();
        
        let mut threshold = header[73..76].to_vec();
        let exp: usize = (header[72] as usize) - 16 - 3;
        let mut trail_zeros = vec![0u8; exp];
        threshold.append(&mut trail_zeros);

        let target: u128 = threshold.iter()
                            .enumerate()
                            .map(|(i,b)| ((1 << i as u128) * (*b as u128) as u128))
                            .sum();

        // let r2 = verify_current_hash(cs.namespace(|| "trivial"), 
        //                                 hash_u, 
        //                                 hash_l, 
        //                                 target, 
        //                                 0u128).unwrap();

        let mut timestamps = self.prev_timestamps.to_vec();

        let r1 = median::verify_median_timestamp(cs.namespace(|| "median check"), &mut timestamps, self.median).unwrap();

        return Ok((*z).to_vec())
    }
}
