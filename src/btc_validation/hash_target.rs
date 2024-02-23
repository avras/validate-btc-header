use bellpepper::gadgets::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper::gadgets::num::AllocatedNum;
use ff::PrimeField;
// use crate::util::num;
use crate::{btc_validation::median, mp::bignat::BigNat};

pub fn verify_current_hash<Scalar, CS> 
(   mut cs: CS, 
    block_hash_u: u128,
    block_hash_l: u128, 
    target_u: u128,
    target_l: u128 ) -> Result<Boolean, SynthesisError>
where
Scalar: PrimeField,
CS: ConstraintSystem<Scalar>,
{
    let hash_u = AllocatedNum::alloc(cs.namespace(|| "Most significant 128 bits of hash"), || Ok(Scalar::from_u128(block_hash_u))).unwrap();
    let hash_l = AllocatedNum::alloc(cs.namespace(|| "Least significant 128 bits of hash"), || Ok(Scalar::from_u128(block_hash_l))).unwrap();

    let target_upper = AllocatedNum::alloc(cs.namespace(|| "Most significant 128 bits of target"), || Ok(Scalar::from_u128(target_u))).unwrap();
    let target_lower = AllocatedNum::alloc(cs.namespace(|| "Least significant 128 bits of target"), || Ok(Scalar::from_u128(target_l))).unwrap();

    let res_upper_lt = median::less_than(&hash_u, &target_upper, 126usize).unwrap();
    let res_upper_eq = BigNat::equals(cs.namespace(|| "Upper 128 bits equality check"), &hash_u, &target_upper).unwrap();
    let res_lower_lt = median::less_than(&hash_l, &target_lower, 126usize).unwrap();

    let partial_res = Boolean::and(cs.namespace(|| "Upper 128 bits equal and lower hash bits less than target lower bits"), &res_upper_eq, &res_lower_lt).unwrap();
    return Boolean::or(cs.namespace(|| "Is hash less than target"), &res_upper_lt, &partial_res);
}

#[cfg(test)]
mod tests {
    use crate::btc_validation::hash_target::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use crate::util::scalar::Fr;

    #[test]
    fn test_hash_target() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        // Block no. 4
        // 0x000000004ebadb55ee9096c9a2f8880e 09da59c0d68b1c228da88e48844a1485
        let hash_u: u128 = 0x000000004ebadb55ee9096c9a2f8880e;
        let hash_l: u128 = 0x09da59c0d68b1c228da88e48844a1485;

        // nbits = 0x1d00ffff
        // so target = 0x00ffff00000000000000000000 00000000000000000000000000000000
        let tar_u: u128 = 0x00ffff00000000000000000000;
        let tar_l: u128 = 0x00;
        let r2 = verify_current_hash(cs.namespace(|| "trivial"), 
                                        hash_u, 
                                        hash_l, 
                                        tar_u, 
                                        tar_l).unwrap();
        
        assert_eq!(r2.get_value().unwrap(), true);
    }
}