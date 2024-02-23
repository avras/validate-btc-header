use bellpepper::gadgets::boolean;
use bellpepper::gadgets::boolean::Boolean;
use bellpepper::gadgets::sha256;
use bellpepper_core::ConstraintSystem;
use ff::PrimeField;

pub fn check_prev_hash<Scalar, CS> 
(   mut cs: CS, 
    prev_block: &Vec<u64>, 
    prev_hash: &Vec<u64> ) -> ()
where
Scalar: PrimeField,
CS: ConstraintSystem<Scalar>,
{
    let mut hash_vec: Vec<Boolean> = Vec::new();
    for (i, hash64) in prev_hash.iter().enumerate() {
        let mut dummy = boolean::u64_into_boolean_vec_le(cs.namespace(|| format!("dummy {}", i)), Some(*hash64)).unwrap();
        dummy.reverse();
        hash_vec.append(&mut dummy);
    }

    let mut preimage_vec: Vec<Boolean> = Vec::new();
    for (i, preimage64) in prev_block.iter().enumerate() {
        let mut dummy2 = boolean::u64_into_boolean_vec_le(cs.namespace(|| format!("dummy2 {}", i)), Some(*preimage64)).unwrap();
        dummy2.reverse();
        preimage_vec.append(&mut dummy2);
    }

    let out_sha256 = sha256::sha256(cs.namespace(|| "SHA 256"), &preimage_vec).unwrap();
    let out = sha256::sha256(cs.namespace(|| "SHA 256d"), &out_sha256).unwrap();

    for (i, (hash_iter, out_iter)) in hash_vec.iter().zip(out.iter()).enumerate() {
        let _ = Boolean::enforce_equal(cs.namespace(|| format!("bit {}", i)), hash_iter, out_iter);
    }
}

#[cfg(test)]
mod tests {
    use crate::btc_validation::prev_block_hash::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use crate::util::scalar::Fr;

    #[test]
    fn test_hash_previous() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        // Block no. 123456
        // 0x010000009500c43a 25c624520b5100ad f82cb9f9da72fd24 47a496bc600b0000 000000006cd86237 0395dedf1da2841c cda0fc489e3039de 5f1ccddef0e83499 1a65600ea6c8cb4d b3936a1ae3143991
        // hash 1 = cac383cdf62f68ef aa8064e35f6fc4df c8aa74610c6580ed 1729000000000000
        // hash 2 = 0000000000002917 ed80650c6174aac8 dfc46f5fe36480aa ef682ff6cd83c3ca

        let hash_vec: Vec<u64> = vec![0xcac383cdf62f68ef, 0xaa8064e35f6fc4df, 0xc8aa74610c6580ed, 0x1729000000000000];
        // let hash2: Vec<u64> = vec![0x1729000000000000, 0xc8aa74610c6580ed, 0xaa8064e35f6fc4df, 0xcac383cdf62f68ef];
        let preimage: Vec<u64> = vec![0x010000009500c43a, 0x25c624520b5100ad, 0xf82cb9f9da72fd24, 0x47a496bc600b0000, 0x000000006cd86237, 0x0395dedf1da2841c, 0xcda0fc489e3039de, 0x5f1ccddef0e83499, 0x1a65600ea6c8cb4d, 0xb3936a1ae3143991];

        let _ = check_prev_hash(cs.namespace(|| "prev_hash"), 
                                        &preimage, 
                                        &hash_vec);
        
        assert!(cs.is_satisfied());
    }
}