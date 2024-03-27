use std::marker::PhantomData;

use crate::btc_validation::{difficulty_update, median};

use bellpepper_core::{
    boolean,
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use bellpepper::gadgets::sha256;
use crate::mp::bignat::BigNat;
use crate::util::convert::f_to_nat;
// use bellpepper::gadgets::num::{AllocatedNum, Num};
use nova_snark::traits::circuit::StepCircuit;

#[derive(Clone, Debug)]
pub struct BlockHeader <F>
where
    F: PrimeField,
{
    block_head: [u64; 10],
    marker: PhantomData<F>,
}

impl<F> Default for BlockHeader <F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn default() -> Self {
        Self {
            block_head: [0u64; 10],
            marker: Default::default(),
        }
    }
}


impl<F> BlockHeader<F>
where
    F: PrimeField + PrimeFieldBits,
{
    // Produces the intermediate blocks when a message is hashed
    pub fn new_blocks(input: Vec<[u64;10]>) -> Vec<Self> {
        // let block_seq = sha256_msg_block_sequence(input);
        input
            .into_iter()
            .map(|b| BlockHeader {
                block_head: b,
                marker: PhantomData,
            })
            .collect()
    }


    pub fn initial_z_i_scalars() -> Vec<F>
    {
        let mut initial_z = Vec::new();

        // let n = 0x0000000000000b60bc96a44724fd72daf9b92cf8ad00510b5224c6253ac40095;
        let curr_hash = F::from_str_vartime("18283544428642297129396529020735695233361821945456783020785813").unwrap();
        initial_z.push(curr_hash);

        // previous 11 timestamps
        let t1 = F::from_str_vartime("1305191152").unwrap(); //123445
        initial_z.push(t1);
        
        let t2 = F::from_str_vartime("1305191688").unwrap(); //123446
        initial_z.push(t2);
        
        let t3 = F::from_str_vartime("1305193319").unwrap(); //123447
        initial_z.push(t3);
        
        let t4 = F::from_str_vartime("1305194571").unwrap(); //123448
        initial_z.push(t4);
        
        let t5 = F::from_str_vartime("1305194986").unwrap(); //123449
        initial_z.push(t5);
        
        let t6 = F::from_str_vartime("1305195947").unwrap(); //123450
        initial_z.push(t6);
        
        let t7 = F::from_str_vartime("1305197900").unwrap(); //123451
        initial_z.push(t7);
        
        let t8 = F::from_str_vartime("1305199436").unwrap(); //123452
        initial_z.push(t8);
        
        let t9 = F::from_str_vartime("1305200301").unwrap(); //123453
        initial_z.push(t9);
        
        let t10 = F::from_str_vartime("1305200460").unwrap(); //123454
        initial_z.push(t10);
        
        let t11 = F::from_str_vartime("1305200584").unwrap(); //123455
        initial_z.push(t11);

        let target = F::from_str_vartime("171262555713783851185422181139260521316022447660158187451973632").unwrap();
        initial_z.push(target);

        let start_time_epoch = F::from(1304975844u64);
        initial_z.push(start_time_epoch);

        let counter = F::from(480u64);
        initial_z.push(counter);

        let chain_work = F::ZERO;
        initial_z.push(chain_work);

        initial_z
    }
}

impl<F> StepCircuit<F> for BlockHeader <F>
where
    F: PrimeField + PrimeFieldBits,
{   
    fn arity(&self) -> usize {
        16
    }

    fn synthesize<CS: ConstraintSystem <F> >(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let header = self.block_head.to_vec();
        let z_i = (*z).to_vec();
        
        // println!("{}", header[0]);
        // println!("{}", header[1]);
        // println!("{}",header[2]);
        // println!("{}", header[3]);
        // let hash_s = z_i[1].get_value().unwrap();
        // let (_s1000, hash32) = f_to_nat(&hash_s).to_u32_digits();
        // for (_i, h) in hash32.iter().enumerate() {
        //     println!("{}", *h);
        // }
        

        // 1. Check if prevHash from z and prev_hash_from_curr_block are equal 
        //
        // Taking the example of block no. 123456
        // 0x010000009500c43a 25c624520b5100ad f82cb9f9da72fd24 47a496bc600b0000 000000006cd86237 0395dedf1da2841c cda0fc489e3039de 5f1ccddef0e83499 1a65600ea6c8cb4d b3936a1ae3143991
        // here 0x9500c43a25c624520b5100adf82cb9f9da72fd2447a496bc600b000000000000 is the prevhash (0000000000000b60bc96a44724fd72daf9b92cf8ad00510b5224c6253ac40095)

        let mut prev_hash_from_curr_block_vec: Vec<u64> = Vec::new();
        for i in 0..4 {
            let hash_vec = (header[i] % (1 << 32 as u64)) * (1<<32 as u64) + header[i+1] / (1 << 32 as u64);
            prev_hash_from_curr_block_vec.push(hash_vec);
        }

        let mut prev_hash_from_curr_block: Vec<boolean::Boolean> = Vec::new();
        for (i, hash64) in prev_hash_from_curr_block_vec.iter().enumerate() {
            let mut dummy = boolean::u64_into_boolean_vec_le(cs.namespace(|| format!("dummy {}", i)), Some(*hash64)).unwrap();
            dummy.reverse();
            prev_hash_from_curr_block.append(&mut dummy);
        }

        let prev_hash = AllocatedNum::alloc(cs.namespace(|| {"last block hash"}), || {
            let mut sum: F = F::ZERO;

            for (i, b) in prev_hash_from_curr_block.iter().enumerate() {
                let exponent = 16 * (i/8) + 7 - i;
                if exponent >= 128 {
                    let power_127 = F::from_u128(1 << 127);
                    let mut power_2 = if (*b).get_value().unwrap() { F::from_u128(1 << (exponent - 127)) }  else { F::from_u128(0u128) };
                    power_2.mul_assign(&power_127);
                    sum.add_assign(&power_2);
                }
                else {
                    let power_2 = if (*b).get_value().unwrap() { F::from_u128(1 << exponent) } else { F::from_u128(0u128) };
                    sum.add_assign(&power_2);
                } 
            }

            Ok(sum)
        }).unwrap();

        // equality check
        let r_prev_hash = BigNat::equals(cs.namespace(|| {"Is prev. hash from current block equal to the last block hash?"}), &z_i[0], &prev_hash).unwrap();
        assert!(r_prev_hash.get_value().or(Some(true)).unwrap());
        
        // 2. Check if current hash <= target
        //
        // Target computation from threshold
        // Taking the example of block no. 123456
        // 0x010000009500c43a 25c624520b5100ad f82cb9f9da72fd24 47a496bc600b0000 000000006cd86237 0395dedf1da2841c cda0fc489e3039de 5f1ccddef0e83499 1a65600ea6c8cb4d b3936a1ae3143991
        // here 0x1a6a93b3 is the threshold
        let n_bits = header[9] >> 32;
        let b0 = n_bits % 256u64;
        let b3 = n_bits >> 24;
        let b2 = n_bits >> 16 - b3 << 24;
        let b1 = n_bits >> 8 - b3 << 24 - b2 << 16;
        
        let target = AllocatedNum::alloc(cs.namespace(|| "Block target"), || {
            let thresh_mantissa = b1 << 16 + b2 << 8 + b3;
            let exponent = (b0 - 3) as usize;

            let targ: F = if exponent >= 13 {
                let partial_scalar = F::from_u128((thresh_mantissa as u128) << (8 * 13) as u128);
                let mut scale = F::from_u128(1 << (8 * (exponent - 13)) as u128);
                scale.mul_assign(&partial_scalar);

                scale
            }
            else {
                F::from_u128((thresh_mantissa as u128) << 8 * exponent) 
            };

            Ok(targ)
        }).unwrap();

        // Current block hash computation
        let mut preimage_vec: Vec<boolean::Boolean> = Vec::new();
        for (i, preimage64) in header.iter().enumerate() {
            let mut dummy2 = boolean::u64_into_boolean_vec_le(cs.namespace(|| format!("dummy2 {}", i)), Some(*preimage64)).unwrap();
            dummy2.reverse();
            preimage_vec.append(&mut dummy2);
        }

        let out_sha256 = sha256::sha256(cs.namespace(|| "SHA 256"), &preimage_vec).unwrap();
        let out = sha256::sha256(cs.namespace(|| "SHA 256d"), &out_sha256).unwrap();
        
        let curr_hash = AllocatedNum::alloc(cs.namespace(|| {"current block hash"}), || {
            let mut sum: F = F::ZERO;

            for (i, b) in out.iter().enumerate() {
                let exponent = 16 * (i/8) + 7 - i;
                if exponent >= 128 {
                    let power_127 = F::from_u128(1 << 127);
                    let mut power_2 = if (*b).get_value().unwrap() { F::from_u128(1 << (exponent - 127)) }  else { F::from_u128(0u128) };
                    power_2.mul_assign(&power_127);
                    sum.add_assign(&power_2);
                }
                else {
                    let power_2 = if (*b).get_value().unwrap() { F::from_u128(1 << exponent) } else { F::from_u128(0u128) };
                    sum.add_assign(&power_2);
                } 
            }

            Ok(sum)
        }).unwrap();

        // less than check
        let r_curr_hash_targ = median::less_than(cs.namespace(|| "Is PoW consensus achieved?"), &curr_hash, &target, 224usize).unwrap();
        assert!(r_curr_hash_targ.get_value().or(Some(true)).unwrap());

        // 3. Check if timestamp of the current block is greater than the median of previous 11 timestamps
        //
        let mut times_vec: Vec<u32> = Vec::new(); 
        for i in 1..=11 {
            let timestamp = z_i[i].get_value().or(Some(F::ONE)).unwrap();
            let (_s, time32) = f_to_nat(&timestamp).to_u32_digits();
            times_vec.push(time32[0]);
        }

        // compute median
        let median = median::compute_median_timestamp(&mut times_vec);

        // verify median
        let r_median = median::verify_median_timestamp(cs.namespace(|| "median verify"), &mut times_vec, median).unwrap();
        assert!(r_median.get_value().or(Some(true)).unwrap());

        // check if median < current timestamp
        // Taking the example of block no. 123456
        // 0x010000009500c43a 25c624520b5100ad f82cb9f9da72fd24 47a496bc600b0000 000000006cd86237 0395dedf1da2841c cda0fc489e3039de 5f1ccddef0e83499 1a65600ea6c8cb4d b3936a1ae3143991
        // here 0xa6c8cb4d is the current timestamp (supposed to be 0x4dcbc8a6)
        let n_time = header[8] % (1 << 32);
        let b_t0 = n_time % 256u64; // 4d
        let b_t3 = n_time >> 24;  // a6
        let b_t2 = n_time >> 16 - b_t3 << 24; // c8
        let b_t1 = n_time >> 8 - b_t3 << 24 - b_t2 << 16; // cb
        let n_time_endian = b_t0 << 24 + b_t1 << 16 + b_t2 << 8 + b_t1;

        let median_fe = AllocatedNum::alloc(cs.namespace(|| "median"), || Ok(F::from(median as u64))).unwrap();
        let curr_timestamp = AllocatedNum::alloc(cs.namespace(|| "current timestamp"), || Ok(F::from(n_time_endian))).unwrap();
        let r_time = median::less_than(cs.namespace(|| "valid timestamp"), &median_fe, &curr_timestamp, 32usize).unwrap();
        assert!(r_time.get_value().or(Some(true)).unwrap());

        // 4. Total work addition
        //
        let max_target = AllocatedNum::alloc(cs.namespace(|| "maximum target"), || {
            let power_127 = F::from_u128(1 << 127);
            let mut max_thresh = F::from_u128(0xFFFF << 81);
            max_thresh.mul_assign(&power_127);

            Ok(max_thresh)
        }).unwrap();

        let block_work = AllocatedNum::alloc(cs.namespace(|| "work or difficulty"), || {
            let diff = max_target.get_value().unwrap();
            let targ = target.get_value().unwrap();

            let diff_big = f_to_nat(&diff);
            let tar_big = f_to_nat(&targ);
            let work = diff_big / tar_big;

            let (_s2, work_u64) = work.to_u64_digits();

            Ok(F::from(work_u64[0] as u64))
        }).unwrap();

        // Constrain allocation:
        // max_target = target * block_work
        cs.enforce(
            || "max_target = target * block_work",
            |lc| lc + target.get_variable(),
            |lc| lc + block_work.get_variable(),
            |lc| lc + max_target.get_variable(),
        );

        // 5. Target update
        //
        // Either the counter i.e. z_i[14] == 0 or target from z_i is equal to curr_target
        // The counter z_i[14] has value r for (2016q + r)th block

        // Constrain allocation:
        // 0 = (target - z_i[12]) * z_i[14]
        cs.enforce(
            || "0 = (target - z_i[12]) * z_i[14]",
            |lc| lc + target.get_variable() - z_i[12].get_variable(),
            |lc| lc + z_i[14].get_variable(),
            |lc| lc,
        );

        let start_time_epoch = z_i[13].clone();
        let target_calc = difficulty_update::calculate_difficulty_update(cs.namespace(|| "target calculated"), &z_i[12], &z_i[13]).unwrap();
        let bigint_tar = target_calc.value.unwrap_or_default();
        let (_s2_calc, target_u64_calc) = bigint_tar.to_u64_digits();

        let calculated_target = AllocatedNum::alloc(cs.namespace(|| "target updated"), || {
            let exponent = 8 * (b0 - 3) as usize;
            let ls_tar = F::from_u128(((target_u64_calc[0] as u128) + (target_u64_calc[1] as u128) << 64) >> exponent);
            let ms64b = F::from_u128((target_u64_calc[2] as u128) << 64);
            let mut pow_2 = F::from_u128((1 << 64)>>exponent);

            pow_2.mul_assign(&ms64b);
            pow_2.add_assign(&ls_tar);

            let exp_2 = F::from_u128(1u128 << exponent);
            pow_2.mul_assign(&exp_2);

            Ok(pow_2)
        }).unwrap();

        // let _r = BigNat::equals(cs.namespace(|| "verify target update"), &target, &calculated_target).unwrap();
        
        // Either the counter z_i[14] is non-zero or curr_target = calc_target = z_i[12] * t_sum / (2016*10*60)
        let delta_inv = AllocatedNum::alloc(cs.namespace(|| "delta_inv"), || {
            let delta = z_i[14].get_value().unwrap();

            if delta.is_zero().unwrap_u8() == 1 {
                Ok(F::ONE) // we can return any number here, it doesn't matter
            } else {
                Ok(delta.invert().unwrap())
            }
        })?;

        // Allocate `t = z_i[14] * delta_inv`
        // If `z_i[14]` is non-zero, `t` will equal 1
        // If `z_i[14]` is zero, `t` will equal 0

        let t = AllocatedNum::alloc(cs.namespace(|| "t"), || {
            let mut tmp = z_i[14].get_value().unwrap();
            tmp.mul_assign(&(delta_inv.get_value().unwrap()));

            Ok(tmp)
        })?;

        // Constrain allocation:
        // t = z_i[14] * delta_inv
        cs.enforce(
            || "t = z_i[14] * delta_inv",
            |lc| lc + z_i[14].get_variable(),
            |lc| lc + delta_inv.get_variable(),
            |lc| lc + t.get_variable(),
        );

        // Constrain:
        // z_i[14] * (t - 1) == 0
        // This enforces that correct `delta_inv` was provided,
        // and thus `t` is 1 if `z_i[14]` is non zero
        cs.enforce(
            || "z_i[14] * (t - 1) == 0",
            |lc| lc + z_i[14].get_variable(),
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc,
        );

        // Constrain:
        // (curr_target - calc_target) * (t - 1) == 0
        // This enforces that correct `delta_inv` was provided,
        // and thus `t` is 1 if `z_i[14]` is non zero
        cs.enforce(
            || "(curr_target - calc_target) * (t - 1) == 0",
            |lc| lc + target.get_variable() - calculated_target.get_variable(),
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc,
        );

        
        // Either the counter z_i[14] is not equal to 2015 or start_time_epoch = z_i[13]


        // 6. z_out
        //
        // If the counter i.e z_i[14] == 2015, then z_out[14] = 0. Else, z_out[14] = z_i[14] + 1.
        let mut z_out: Vec<AllocatedNum<F>> = Vec::new();
        z_out.push(curr_hash.clone()); // z_out[0]
        cs.enforce(
            || "current SHA256d hash out", 
            |lc| lc,
            |lc| lc,
            |lc| lc + z_out[0].get_variable() - curr_hash.get_variable(),
        );

        
        for i in 1..=10 {
            z_out.push(z_i[i+1].clone()); // z_out[1..=10]

            cs.enforce(
                || format!("timestamp out {}", i), 
                |lc| lc,
                |lc| lc,
                |lc| lc + z_out[i].get_variable() - z_i[i + 1].get_variable(),
            );
        }

        z_out.push(curr_timestamp.clone()); // z_out[11]
        cs.enforce(
            || "current timestamp out", 
            |lc| lc,
            |lc| lc,
            |lc| lc + z_out[11].get_variable() - curr_timestamp.get_variable(),
        );

        z_out.push(target.clone()); // z_out[12]
        cs.enforce(
            || "current target out", 
            |lc| lc,
            |lc| lc,
            |lc| lc + z_out[12].get_variable() - target.get_variable(),
        );

        z_out.push(start_time_epoch.clone()); // z_out[13]
        cs.enforce(
            || "current start time epoch out", 
            |lc| lc,
            |lc| lc,
            |lc| lc + z_out[13].get_variable() - start_time_epoch.get_variable(),
        );

        // z_out[14]
        z_out.push(AllocatedNum::alloc(cs.namespace(|| "target counter"), || {
            let mut prev_ctr = z_i[14].get_value().unwrap();

            prev_ctr.add_assign(F::ONE);
            Ok(prev_ctr)
        }).unwrap());

        cs.enforce(
            || "z_out[14] = z_i[14] + 1", 
            |lc| lc + CS::one() + z_i[14].get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + z_out[14].get_variable(),
        );

        // total work
        // z_out[15]
        z_out.push(AllocatedNum::alloc(cs.namespace(|| "total work"), || {
            let prev_total = z_i[15].get_value().unwrap();
            let mut curr_work = block_work.get_value().unwrap();

            curr_work.add_assign(&prev_total);
            Ok(curr_work)
        }).unwrap());

        cs.enforce(
            || "z_out[15] = z_i[15] + block_work", 
            |lc| lc + block_work.get_variable() + z_i[15].get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + z_out[15].get_variable(),
        );

        Ok(z_out)
    }
}
