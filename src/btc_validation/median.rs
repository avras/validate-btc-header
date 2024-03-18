use bellpepper::gadgets::boolean::AllocatedBit;
use bellpepper::gadgets::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper::gadgets::num::{AllocatedNum, Num};
use ff::PrimeField;
use crate::BitAccess;
use crate::OptionExt;
use crate::mp::bignat::BigNat;

pub fn compute_median_timestamp (prev_timestamps: &mut Vec<u32>) -> u32
{
    prev_timestamps.sort();
    return prev_timestamps[prev_timestamps.len()/2];
}

pub fn verify_median_timestamp<Scalar, CS> (mut cs: CS, timestamp_array: &mut Vec<u32>, median: u32) -> Result<Boolean, SynthesisError>
where
Scalar: PrimeField,
CS: ConstraintSystem<Scalar>,
{
    let fe_median = AllocatedNum::alloc(cs.namespace(|| "median"), || Ok(Scalar::from(median as u64))).unwrap();

    let mut fe_timestamps = vec![];
    let mut fe_temp: AllocatedNum<Scalar>;
    for (i, stamp) in timestamp_array.iter().enumerate() {
        fe_temp = AllocatedNum::alloc(cs.namespace(|| format!("timestamp {}", i)), || Ok(Scalar::from(*stamp as u64))).unwrap();
        fe_timestamps.push(fe_temp);
    }

    let mut n_median_occurrences = Num::zero();
    let mut sign_diff = AllocatedNum::alloc(cs.namespace(|| "sign_diff"), || Ok(Scalar::from(0u64))).unwrap();

    for (i, fe_time) in fe_timestamps.iter().enumerate() {
        // n_median_occurrences += 1 if median == timestamp else no change
        let res_eq = BigNat::equals(cs.namespace(|| format!("check equal for time {}", i)), &fe_median, fe_time).unwrap();
        n_median_occurrences = n_median_occurrences.add_bool_with_coeff(CS::one(), &res_eq, Scalar::ONE);

        let res_lt = less_than(cs.namespace(|| format!("res_lt {}", i)), &fe_median, fe_time, 32).unwrap();

        // delta_sign is the signum of (median - timestamp)
        let delta_sign = AllocatedNum::alloc(cs.namespace(|| format!("signum {}", i)), || {
            let eq = Scalar::from(res_eq.get_value().unwrap() as u64);
            let lt = Scalar::from(res_lt.get_value().unwrap() as u64);
            
            // let signum: i64 = (1 - eq) * (1 - 2 * lt);
            let mut eq_opd = Scalar::ONE;
            eq_opd.sub_assign(&eq);
            let mut mult_res = Scalar::ONE;
            mult_res.sub_assign(&lt);
            mult_res.sub_assign(&lt);

            mult_res.mul_assign(&eq_opd);
            Ok(mult_res)
            // Ok(Scalar::from(signum))
        }).unwrap();
        
        let eq_bit = AllocatedBit::alloc(cs.namespace(|| format!("equality {}", i)), Some(res_eq.get_value().unwrap())).unwrap();
        let lt_bit_mul2 = AllocatedNum::alloc(cs.namespace(|| format!("less than {}", i)), || Ok(Scalar::from(2*(res_lt.get_value().unwrap() as u64)))).unwrap();
        // Constrain:
        // (1 - res_eq) * (1 - 2 * res_lt) == delta_sign
        cs.enforce(
            || format!("(1 - res_eq) * (1 - 2 * res_lt) == delta_sign {}", i),
            |lc| lc + CS::one() - eq_bit.get_variable(),
            |lc| lc + CS::one() - lt_bit_mul2.get_variable(),
            |lc| lc + delta_sign.get_variable(),
        );

        // sign_diff += signum(median - timestamp)
        sign_diff = sign_diff.add(cs.namespace(|| format!("sign_diff increment {}", i)), &delta_sign).unwrap();
    }
    // absolute value of sign_diff needs to be obtained
    let const_12 = AllocatedNum::alloc(cs.namespace(|| "max positive sign_diff"), || Ok(Scalar::from(12u64))).unwrap();
    let is_positive = less_than(cs.namespace(|| "is_pos"), &sign_diff, &const_12, 32usize).unwrap();
    let neg_sign_diff = AllocatedNum::alloc(cs.namespace(|| "Negative of sign_diff"), || {
        let sign_val = sign_diff.get_value().unwrap();
        let mut zero_val = Scalar::ZERO;
        zero_val.sub_assign(&sign_val);
        Ok(zero_val)
    }).unwrap();
    // Constrain:
    // (sign_diff + neg_sign_diff) * 1 == 0
    cs.enforce(
        || "(sign_diff + neg_sign_diff) * 1 == 0",
        |lc| lc + sign_diff.get_variable() + neg_sign_diff.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc,
    );

    let (abs_sign_diff, _dummy) = AllocatedNum::conditionally_reverse(cs.namespace(|| "absolute value"), &sign_diff, &neg_sign_diff, &is_positive).unwrap();

    let const_1 = AllocatedNum::alloc(cs.namespace(|| "increment by 1"), || Ok(Scalar::ONE)).unwrap();
    let lhs = abs_sign_diff.add(cs.namespace(|| "LHS of inequality"), &const_1).unwrap();
    // lhs = abs(sign_diff) + 1

    let fe_median_occ = AllocatedNum::alloc(cs.namespace(|| "fe_median"), || Ok(n_median_occurrences.get_value().unwrap())).unwrap();

    // let r_eq = BigNat::equals(cs.namespace(|| "verify median"), &lhs, &fe_median_occ).unwrap();
    // let r_lt = less_than(cs.namespace(|| "lt"), &lhs, &fe_median_occ, 5).unwrap();
    // Boolean::or(cs.namespace(|| "less than or equal to check"), &r_eq, &r_lt)
    leq(cs.namespace(|| "median leq"), &lhs, &fe_median_occ, 32usize)
}

/// Takes two allocated numbers (a, b) and returns
/// allocated boolean variable with value `true`
/// if the `a` and `b` are such that a is strictly less than b, 
/// `false` otherwise.
pub fn less_than <Scalar, CS> (
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    n_bits: usize,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let zero_shifted_cmp = AllocatedNum::alloc(cs.namespace(|| "zero shift"), || {
        let mut cmp_val = a.get_value().unwrap();
        let b_value = b.get_value().unwrap();

        // Accomodating n_bits > 128 (i.e a and b atleast 128 bits)
        let zero_shift = if n_bits <= 126 { 
            Scalar::from_u128(2 << n_bits) 
        } 
        else { 
            let shift1 = Scalar::from_u128(2 << (n_bits - 126));
            let mut shift2 = Scalar::from_u128(2 << 126);
            shift2.mul_assign(&shift1);
            shift2
        };

        cmp_val.add_assign(&zero_shift);
        cmp_val.sub_assign(&b_value);

        Ok(cmp_val)
    }).unwrap();

    let n_bit_zero_cmp = AllocatedNum::alloc(cs.namespace(|| "n_bits zero cmp"), ||{
        let mut exponent = Scalar::ONE;
        let sc_two = Scalar::ONE + Scalar::ONE;
        let cmp = zero_shifted_cmp.get_value();

        let mut summ = Scalar::ZERO;
        for i in 0..=n_bits{
            let mut bit_i = if *cmp.grab()?.get_bit(i).grab()? {
                Scalar::ONE
            } else {
                Scalar::ZERO
            };
            bit_i.mul_assign(&exponent);
            summ.add_assign(&bit_i);
            exponent.mul_assign(&sc_two);
        }

        Ok(summ)
    }).unwrap();

    BigNat::equals(cs.namespace(|| "check fits in n_bits"), &zero_shifted_cmp, &n_bit_zero_cmp)

    // let _ = zero_shifted_cmp.fits_in_bits(cs.namespace(|| "check if fits"), n_bits + 1);
    // let boolean_r = cs.is_satisfied();
    // let r = AllocatedBit::alloc(cs.namespace(|| "r"), Some(boolean_r))?;

    // Ok(Boolean::from(r))

}

/// Takes two allocated numbers (a, b) and returns
/// allocated boolean variable with value `true`
/// if the `a` and `b` are such that a is less than or equal to b, 
/// `false` otherwise.
pub fn leq <Scalar, CS> (
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    n_bits: usize,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let zero_shifted_cmp = AllocatedNum::alloc(cs.namespace(|| "zero shift leq"), || {
        let mut cmp_val = a.get_value().unwrap();
        let mut b_value = b.get_value().unwrap();
        b_value.add_assign(Scalar::ONE);

        // Accomodating n_bits > 128 (i.e a and b atleast 128 bits)
        let zero_shift = if n_bits <= 126 { 
            Scalar::from_u128(2 << n_bits) 
        } 
        else { 
            let shift1 = Scalar::from_u128(2 << (n_bits - 126));
            let mut shift2 = Scalar::from_u128(2 << 126);
            shift2.mul_assign(&shift1);
            shift2
        };

        cmp_val.add_assign(&zero_shift);
        cmp_val.sub_assign(&b_value);

        Ok(cmp_val)
    }).unwrap();

    let n_bit_zero_cmp = AllocatedNum::alloc(cs.namespace(|| "n_bits zero cmp leq"), ||{
        let mut exponent = Scalar::ONE;
        let sc_two = Scalar::ONE + Scalar::ONE;
        let cmp = zero_shifted_cmp.get_value();

        let mut summ = Scalar::ZERO;
        for i in 0..=n_bits{
            let mut bit_i = if *cmp.grab()?.get_bit(i).grab()? {
                Scalar::ONE
            } else {
                Scalar::ZERO
            };
            bit_i.mul_assign(&exponent);
            summ.add_assign(&bit_i);
            exponent.mul_assign(&sc_two);
        }

        Ok(summ)
    }).unwrap();

    BigNat::equals(cs.namespace(|| "check fits in n_bits leq"), &zero_shifted_cmp, &n_bit_zero_cmp)
}

#[cfg(test)]
mod tests {
    use crate::btc_validation::median::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use crate::util::{scalar::Fr, num};

    #[test]
    fn test_median_compute() {
        let mut timestamps: Vec<u32> = vec![11,2,3,4,7,5,8,6,10,9,1];
        let median: u32 = compute_median_timestamp(&mut timestamps);

        assert_eq!(median, 6);
    }

    #[test]
    fn test_median_verify() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut timestamps: Vec<u32> = vec![11,2,3,4,6,6,8,6,10,9,1];
        // let mut timestamps: Vec<u32> = vec![11,11,11,11,11,11,11,11,11,11,11,11];
        let median: u32 = compute_median_timestamp(&mut timestamps);

        let r = verify_median_timestamp(cs.namespace(|| "verify median"), &mut timestamps, median).unwrap().get_value().unwrap();
        assert!(r);
    }

    #[test]
    fn test_equals() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let c = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from(4u64))).unwrap();
        let d = AllocatedNum::alloc(cs.namespace(|| "d"), || Ok(Fr::from(4u64))).unwrap();
        let r2 = BigNat::equals(cs.namespace(|| "check equal"), &c, &d).unwrap().get_value().unwrap();

        assert_eq!(r2, true);
    }

    #[test]
    fn test_fits_in_bits() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let val = num::Num::alloc(cs.namespace(|| "value to check fit"), || Ok(Fr::from(2<<30))).unwrap();
        let n_bits: usize = 32;

        let _ = val.fits_in_bits(cs.namespace(|| "check if fits in bits"), n_bits);
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_less_than() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let c = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from(11u64))).unwrap();
        let d = AllocatedNum::alloc(cs.namespace(|| "d"), || Ok(Fr::from(14u64))).unwrap();
        let n_bits: usize = 32;
        let r2 = less_than(cs.namespace(|| "r2"), &c, &d, n_bits).unwrap().get_value().unwrap();

        assert_eq!(r2, true);
    }

    #[test]
    fn test_less_than_equal() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let c = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from(11u64))).unwrap();
        let d = AllocatedNum::alloc(cs.namespace(|| "d"), || Ok(Fr::from(14u64))).unwrap();
        let n_bits: usize = 32;
        let r2 = leq(cs.namespace(|| "r2"), &c, &d, n_bits).unwrap().get_value().unwrap();

        assert_eq!(r2, true);
    }
}