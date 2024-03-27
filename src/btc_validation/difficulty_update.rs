use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper::gadgets::num::AllocatedNum;
use ff::PrimeField;
use crate::btc_validation::median;
use crate::mp::bignat::BigNat;
use crate::util::num;
// use crate::util::convert::nat_to_f;
// use bellpepper_nonnative::mp::bignat::Polynomial;

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

    let res_lower = median::less_than(cs.namespace(|| "res_lower"), &t_sum_lower, &fe_t_sum, 32).unwrap().get_value().unwrap();
    let res_upper = median::less_than(cs.namespace(|| "res_upper"), &fe_t_sum, &t_sum_upper, 32).unwrap().get_value().unwrap();
    assert!(res_lower & res_upper);
    
    // // To verify if T_new * 2016 * 10 * 60 == t_sum * T_old
    // let t_ideal_sum = num::Num::alloc(cs.namespace(|| "2016 * 10 * 60"), || Ok(Scalar::from(2016 * 10 * 60 as u64))).unwrap();
    // let t_2016_10_60 = BigNat::from_num(cs.namespace(|| "BigNat t_ideal_sum"), t_ideal_sum, 64usize, 2usize).unwrap();

    // let lhs = target.mult(cs.namespace(|| "T_new * 2016 * 10 * 60"), &t_2016_10_60).unwrap();
    // let rhs = prev_target.mult(cs.namespace(|| "T_old * t_sum"), &t_sum).unwrap();

    // lhs.equal(cs.namespace(|| "difficulty update verified"), &rhs).unwrap()
    let t_ideal_sum = num::Num::alloc(cs.namespace(|| "2016 * 10 * 60"), || Ok(Scalar::from(2016 * 10 * 60 as u64))).unwrap();
    let t_2016_10_60 = BigNat::from_num(cs.namespace(|| "BigNat t_ideal_sum"), t_ideal_sum, 64usize, 2usize).unwrap();
    
    let (t_new, _t) =  prev_target.mult_mod(cs.namespace(|| "T_new compute"), &t_sum, &t_2016_10_60).unwrap();
    target.equal(cs.namespace(|| "computation equal to next target"), &t_new).unwrap()
}

pub fn calculate_difficulty_update<Scalar, CS> 
    (   mut cs: CS, 
        prev_target: &AllocatedNum<Scalar>,
        sum_timestamps: &AllocatedNum<Scalar> ) -> Result<BigNat<Scalar>, SynthesisError>
        //AllocatedNum<Scalar>
where
Scalar: PrimeField,
CS: ConstraintSystem<Scalar>,
{
    let t_sum_num = num::Num::from((*sum_timestamps).clone());
    let t_sum = BigNat::from_num(cs.namespace(|| "BigNat time sum"), t_sum_num, 64usize, 1usize).unwrap();

    let prev_tar = num::Num::from((*prev_target).clone());
    let prev_targ = BigNat::from_num(cs.namespace(|| "BigNat previous target"), prev_tar, 64usize, 4usize).unwrap();

    // let target = num::Num::from(*curr_target);
    // let _bignat_tar = BigNat::from_num(cs.namespace(|| "BigNat curr_target"), target, 64usize, 2usize).unwrap();

    // To verify if T_old / 4 < T_new < 4 * T_old
    // is the same as verifying 2016 * 10 * 60 / 4 < t_sum < 2016 * 10 * 60 * 4
    let t_sum_lower = AllocatedNum::alloc(cs.namespace(|| "Lower acceptable t sum"), || Ok(Scalar::from(2016 * 10 * 60 / 4 as u64))).unwrap();
    let t_sum_upper = AllocatedNum::alloc(cs.namespace(|| "Upper acceptable t sum"), || Ok(Scalar::from(2016 * 10 * 60 * 4 as u64))).unwrap();

    let res_lower = median::less_than(cs.namespace(|| "res lower"), &t_sum_lower, sum_timestamps, 32)?;
    let res_upper = median::less_than(cs.namespace(|| "res upper"), sum_timestamps, &t_sum_upper, 32)?;
    assert!(res_lower.get_value().or(Some(true)).unwrap() & res_upper.get_value().or(Some(true)).unwrap());

    let t_ideal_sum = num::Num::alloc(cs.namespace(|| "2016 * 10 * 60 or 2 weeks"), || Ok(Scalar::from(2016 * 10 * 60 as u64))).unwrap();
    let t_2016_10_60 = BigNat::from_num(cs.namespace(|| "BigNat t ideal sum"), t_ideal_sum, 128usize, 1usize).unwrap();
    
    let (t_new, _t) =  prev_targ.mult_mod(cs.namespace(|| "T new compute"), &t_sum, &t_2016_10_60).unwrap();
    // let target_num = Polynomial::from(t_new);
    // let _new_target = AllocatedNum::alloc(cs.namespace(|| "Updated target calculated"), || {
    //     let target_value = t_new.value.unwrap();
    //     let tar_field = nat_to_f(&target_value).unwrap();

    //     Ok(tar_field)
    // }).unwrap();

    // // Constrain the value of new_target
    // cs.enforce(
    //     || "current SHA256d hash out", 
    //     |lc| lc,
    //     |lc| lc,
    //     |lc| lc + new_target.get_variable() - t_new,
    // );

    // &t_new
    Ok(t_new)
}

#[cfg(test)]
mod tests {
    use std::ops::{AddAssign, MulAssign};

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
        // let tar_u: u128 = 0x05 as u128;
        // let tar_l: u128 = 0x38940000000000000000000000000000 as u128;
        // let tar_l: u128 = 0x3894871D1837E9E504B6B1D1837E9E50 as u128;
        // calc. target = 0x5 3894871D1837E9E504B6B1D1837E9E50
        // let prev_tar_u: u128 = 0x05 as u128;
        // let prev_tar_l: u128 = 0x8ebe0000000000000000000000000000 as u128;
        let prev_tar_u = 0;
        let prev_tar_l = 0x058ebe as u128;
        let tar_u = 0u128;
        let tar_l: u128 = 0x053894 as u128;


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

    #[test]
    fn test_calc_new_target() {
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
        let prev_tar_u: u128 = 0x05 as u128;
        let prev_tar_l: u128 = 0x8ebe0000000000000000000000000000 as u128;
        let prev_target = AllocatedNum::alloc(cs.namespace(|| "780k block target"), || {
            let targ_u = Fr::from_u128(prev_tar_u *2u128);
            let targ_l = Fr::from_u128(prev_tar_l);

            let mut pow_2 = Fr::from_u128(1 << 127);

            pow_2.mul_assign(&targ_u);
            pow_2.add_assign(&targ_l);

            Ok(pow_2)
        }).unwrap();

        // Block 798336 timestamp 2023-07-12 07:59:39 GMT +5.5
        // Block 798335 timestamp 2023-07-12 07:57:41 GMT +5.5
        // Block 796320 timestamp 2023-06-29 04:18:35 GMT +5.5
        // Block 796319 timestamp 2023-06-29 04:16:06 GMT +5.5
        // Difference is 13 days, 3 hrs, 39 min, 6 sec
        // t_sum = 13 * 24 * 3600 + 3 * 3600 + 39 * 60 + 6 
        let t_sum: u32 = (13 * 24 * 3600 + 3 * 3600 + 39 * 60 + 6) as u32;
        let time_sum = AllocatedNum::alloc(cs.namespace(|| "sum of timestamps"), || {Ok(Fr::from(t_sum as u64))}).unwrap();

        let tar_u: u128 = 0x05 as u128;
        let tar_l: u128 = 0x38940000000000000000000000000000 as u128;
        let _curr_target = AllocatedNum::alloc(cs.namespace(|| "800k block target"), || {
            let targ_u = Fr::from_u128(tar_u *2u128);
            let targ_l = Fr::from_u128(tar_l);

            let mut pow_2 = Fr::from_u128(1 << 127);

            pow_2.mul_assign(&targ_u);
            pow_2.add_assign(&targ_l);

            Ok(pow_2)
        }).unwrap();

        let new_target = calculate_difficulty_update(cs.namespace(|| "calculates difficulty"), &prev_target, &time_sum).unwrap();
        let bigint_tar = new_target.value.unwrap();
        let (_s2, target_u64) = bigint_tar.to_u64_digits();
        // println!("{}", target_u64[2]);
        // //5
        // println!("{}", target_u64[1]);
        // //3894871D1837E9E5
        // println!("{}", target_u64[0]);
        // //04B6B1D1837E9E50

        assert_eq!(target_u64[2], 5);
        assert_eq!(target_u64[1], 0x3894871D1837E9E5);
        assert_eq!(target_u64[0], 0x04B6B1D1837E9E50);
    }
}