use bellpepper::gadgets::boolean::AllocatedBit;
use bellpepper::gadgets::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError, test_cs::TestConstraintSystem};
use bellpepper::gadgets::num::{AllocatedNum, Num};
use ff::PrimeField;
use crate::util::num;

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
        let res_eq = equals(cs.namespace(|| format!("check equal for time {}", i)), &fe_median, fe_time).unwrap(); //.get_value().unwrap();
        // n_median_occurrences += result as u32;
        n_median_occurrences = n_median_occurrences.add_bool_with_coeff(CS::one(), &res_eq, Scalar::ONE);

        let res_lt = less_than(&fe_median, fe_time, 32).unwrap();

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

        sign_diff = sign_diff.add(cs.namespace(|| format!("sign_diff increment {}", i)), &delta_sign).unwrap();
    }
    // absolute value needs to be obtained
    let const_12 = AllocatedNum::alloc(cs.namespace(|| "max positive sign_diff"), || Ok(Scalar::from(12u64))).unwrap();
    let is_positive = less_than(&sign_diff, &const_12, 5usize).unwrap();
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

    let fe_median = AllocatedNum::alloc(cs.namespace(|| "fe_median"), || Ok(n_median_occurrences.get_value().unwrap())).unwrap();

    equals(cs.namespace(|| "verify median"), &lhs, &fe_median)   
}

/// Takes two allocated numbers (a, b) and returns
/// allocated boolean variable with value `true`
/// if the `a` and `b` are such that a is strictly less than b, 
/// `false` otherwise.
pub fn less_than <Scalar> (
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    n_bits: usize,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
{
    let mut cs = TestConstraintSystem::<Scalar>::new();

    let zero_shifted_cmp = num::Num::alloc(cs.namespace(|| "zero shift"), || {
        let mut cmp_val = a.get_value().unwrap();
        let b_value = b.get_value().unwrap();
        let zero_shift = Scalar::from(2 << n_bits);
        cmp_val.add_assign(&zero_shift);
        cmp_val.sub_assign(&b_value);

        Ok(cmp_val)
    }).unwrap();

    let _ = zero_shifted_cmp.fits_in_bits(cs.namespace(|| "check if fits"), n_bits + 1);
    let boolean_r = cs.is_satisfied();
    let r = AllocatedBit::alloc(cs.namespace(|| "r"), Some(boolean_r))?;

    Ok(Boolean::from(r))
}

// from bignat.rs

    /// Takes two allocated numbers (a, b) and returns
    /// allocated boolean variable with value `true`
    /// if the `a` and `b` are equal, `false` otherwise.
    pub fn equals<Scalar, CS>(
        mut cs: CS,
        a: &AllocatedNum<Scalar>,
        b: &AllocatedNum<Scalar>,
    ) -> Result<Boolean, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        // Allocate and constrain `r`: result boolean bit.
        // It equals `true` if `a` equals `b`, `false` otherwise

        let r_value = match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => Some(a == b),
            _ => None,
        };

        let r = AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

        let delta = AllocatedNum::alloc(cs.namespace(|| "delta"), || {
            let a_value = a.get_value().unwrap();
            let b_value = b.get_value().unwrap();

            let mut delta = a_value;
            delta.sub_assign(&b_value);

            Ok(delta)
        })?;

        //
        cs.enforce(
            || "delta = (a - b)",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + delta.get_variable(),
        );

        let delta_inv = AllocatedNum::alloc(cs.namespace(|| "delta_inv"), || {
            let delta = delta.get_value().unwrap();

            if delta.is_zero().unwrap_u8() == 1 {
                Ok(Scalar::ONE) // we can return any number here, it doesn't matter
            } else {
                Ok(delta.invert().unwrap())
            }
        })?;

        // Allocate `t = delta * delta_inv`
        // If `delta` is non-zero (a != b), `t` will equal 1
        // If `delta` is zero (a == b), `t` cannot equal 1

        let t = AllocatedNum::alloc(cs.namespace(|| "t"), || {
            let mut tmp = delta.get_value().unwrap();
            tmp.mul_assign(&(delta_inv.get_value().unwrap()));

            Ok(tmp)
        })?;

        // Constrain allocation:
        // t = (a - b) * delta_inv
        cs.enforce(
            || "t = (a - b) * delta_inv",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + delta_inv.get_variable(),
            |lc| lc + t.get_variable(),
        );

        // Constrain:
        // (a - b) * (t - 1) == 0
        // This enforces that correct `delta_inv` was provided,
        // and thus `t` is 1 if `(a - b)` is non zero (a != b )
        cs.enforce(
            || "(a - b) * (t - 1) == 0",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc,
        );

        // Constrain:
        // (a - b) * r == 0
        // This enforces that `r` is zero if `(a - b)` is non-zero (a != b)
        cs.enforce(
            || "(a - b) * r == 0",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + r.get_variable(),
            |lc| lc,
        );

        // Constrain:
        // (t - 1) * (r - 1) == 0
        // This enforces that `r` is one if `t` is not one (a == b)
        cs.enforce(
            || "(t - 1) * (r - 1) == 0",
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc + r.get_variable() - CS::one(),
            |lc| lc,
        );

        Ok(Boolean::from(r))
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
        let cs = TestConstraintSystem::<Fr>::new();
        // let mut timestamps: Vec<u32> = vec![11,2,3,4,7,6,8,6,10,9,1];
        let mut timestamps: Vec<u32> = vec![111,52,93,74,27,26,28,26,10,49,51];
        let median: u32 = compute_median_timestamp(&mut timestamps);

        let r = verify_median_timestamp(cs, &mut timestamps, median).unwrap().get_value().unwrap();
        assert_eq!(r, true);
    }

    #[test]
    fn test_equals() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let c = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from(4u64))).unwrap();
        let d = AllocatedNum::alloc(cs.namespace(|| "d"), || Ok(Fr::from(4u64))).unwrap();
        let r2 = equals(cs.namespace(|| "check equal"), &c, &d).unwrap().get_value().unwrap();

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
        let r2 = less_than(&c, &d, n_bits).unwrap().get_value().unwrap();

        assert_eq!(r2, true);
    }
}