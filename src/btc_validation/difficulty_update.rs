use bellpepper_core::ConstraintSystem;
use bellpepper::gadgets::num::AllocatedNum;
use ff::PrimeField;
use crate::btc_validation::median;
use crate::mp::bignat::BigNat;
use crate::util::num;

pub fn verify_difficulty_update<Scalar, CS> 
    (   mut cs: CS, 
        current_target_u: u128,
        current_target_l: u128, 
        prev_target_u: u128,
        prev_target_l: u128,
        sum_timestamps: u32 ) -> ()
where
Scalar: PrimeField,
CS: ConstraintSystem<Scalar>,
{
    let t_sum_num = num::Num::alloc(cs.namespace(|| "Sum of 2016 blocks timestamps"), || Ok(Scalar::from(sum_timestamps as u64))).unwrap();
    let t_sum = BigNat::from_num(cs.namespace(|| "BigNat t_sum"), t_sum_num, 64usize, 2usize).unwrap();

    let target_upper = num::Num::alloc(cs.namespace(|| "Most significant 128 bits of target"), || Ok(Scalar::from_u128(current_target_u))).unwrap();
    let target_lower = num::Num::alloc(cs.namespace(|| "Least significant 128 bits of target"), || Ok(Scalar::from_u128(current_target_l))).unwrap();

    let prev_tar_upper = num::Num::alloc(cs.namespace(|| "Most significant 128 bits of last target"), || Ok(Scalar::from_u128(prev_target_u))).unwrap();
    let prev_tar_lower = num::Num::alloc(cs.namespace(|| "Least significant 128 bits of last target"), || Ok(Scalar::from_u128(prev_target_l))).unwrap();

    let bignat_tar_u = BigNat::from_num(cs.namespace(|| "Upper target in bignat"), target_upper, 64usize, 2usize).unwrap(); 
    let bignat_tar_l = BigNat::from_num(cs.namespace(|| "Lower target in bignat"), target_lower, 64usize, 2usize).unwrap(); 
    let target = bignat_tar_u.concat(&bignat_tar_l).unwrap();

    let bignat_prev_tar_u = BigNat::from_num(cs.namespace(|| "Upper target before update in bignat"), prev_tar_upper, 64usize, 2usize).unwrap(); 
    let bignat_prev_tar_l = BigNat::from_num(cs.namespace(|| "Lower target before update in bignat"), prev_tar_lower, 64usize, 2usize).unwrap();
    let prev_target = bignat_prev_tar_u.concat(&bignat_prev_tar_l).unwrap();

    // To verify if T_old / 4 < T_new < 4 * T_old
    // is the same as verifying 2016 * 10 * 60 / 4 < t_sum < 2016 * 10 * 60 * 4
    let fe_t_sum = AllocatedNum::alloc(cs.namespace(|| "Timestamps sum"), || Ok(Scalar::from(sum_timestamps as u64))).unwrap();

    let t_sum_lower = AllocatedNum::alloc(cs.namespace(|| "Lower acceptable t_sum"), || Ok(Scalar::from(2016 * 10 * 60 / 4 as u64))).unwrap();
    let t_sum_upper = AllocatedNum::alloc(cs.namespace(|| "Upper acceptable t_sum"), || Ok(Scalar::from(2016 * 10 * 60 * 4 as u64))).unwrap();

    let res_lower = median::less_than(&t_sum_lower, &fe_t_sum, 32).unwrap().get_value().unwrap();
    let res_upper = median::less_than(&fe_t_sum, &t_sum_upper, 32).unwrap().get_value().unwrap();
    assert!(res_lower & res_upper);
    
    // To verify if T_new * 2016 * 10 * 60 == t_sum * T_old
    let t_ideal_sum = num::Num::alloc(cs.namespace(|| "2016 * 10 * 60"), || Ok(Scalar::from(2016 * 10 * 60 as u64))).unwrap();
    let t_2016_10_60 = BigNat::from_num(cs.namespace(|| "BigNat t_ideal_sum"), t_ideal_sum, 64usize, 2usize).unwrap();

    let lhs = target.mult(cs.namespace(|| "T_new * 2016 * 10 * 60"), &t_2016_10_60).unwrap();
    let rhs = prev_target.mult(cs.namespace(|| "T_old * t_sum"), &t_sum).unwrap();

    lhs.equal(cs.namespace(|| "difficulty update verified"), &rhs).unwrap()
}

#[cfg(test)]
mod tests {
    use crate::btc_validation::difficulty_update::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use crate::util::scalar::Fr;

    #[test]
    fn test_trivial_difficulty() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let tar_u: u128 = 2 << 97 as u128;
        let tar_l: u128 = 2 << 97 as u128;
        let prev_tar_u: u128 = 2 << 96 as u128;
        let prev_tar_l: u128 = 2 << 96 as u128;
        let t_sum: u32 = 2016 * 10 * 60 * 2 as u32;

        let _ = verify_difficulty_update(cs.namespace(|| "trivial"), 
                                        tar_u, 
                                        tar_l, 
                                        prev_tar_u, 
                                        prev_tar_l, 
                                        t_sum);
        
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_btc_header_difficulty() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        // previous difficulty 50646206431058 (798000th block)
        // difficulty 53911173001054 (800000th block)
        // updated at block 798336 = 2016 * 396
        // therefore blocks 2016 * 395 to (2016 * 396 - 1) had difficulty = previous difficulty
        // hence t_sum = sum of timestamps of blocks 796320 (2016 * 395) to 798335
        
        // nbits of 800000th block = 0x17053894
        // so target = 0x05 38940000000000000000000000000000
        // nbits of 798000th block = 0x17058ebe
        // so target = 0x05 8ebe0000000000000000000000000000
        let tar_u: u128 = 0x05 as u128;
        let tar_l: u128 = 0x38940000000000000000000000000000 as u128;
        let prev_tar_u: u128 = 0x05 as u128;
        let prev_tar_l: u128 = 0x8ebe0000000000000000000000000000 as u128;

        // Block 798336 timestamp 2023-07-12 07:59:39 GMT +5.5
        // Block 798335 timestamp 2023-07-12 07:57:41 GMT +5.5
        // Block 796320 timestamp 2023-06-29 04:18:35 GMT +5.5
        // Block 796319 timestamp 2023-06-29 04:16:06 GMT +5.5
        // Difference is 13 days, 3 hrs, 39 min, 6 sec
        // t_sum = 13 * 24 * 3600 + 3 * 3600 + 39 * 60 + 6 
        let t_sum: u32 = (13 * 24 * 3600 + 3 * 3600 + 39 * 60 + 6) as u32;
        let _ = verify_difficulty_update(cs.namespace(|| "trivial"), 
                                        tar_u, 
                                        tar_l, 
                                        prev_tar_u, 
                                        prev_tar_l, 
                                        t_sum);
        
        assert!(cs.is_satisfied());
    }
}