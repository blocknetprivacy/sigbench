use crate::faraday_fold::rec::FriShape;

pub const TARGET_BITS: f64 = 112.0;

pub const FUNDS_SHAPE: FriShape = FriShape { log_blowup: 4, max_log_arity: 4, num_queries: 106 };

pub fn unique_decoding_query_bits(log_blowup: usize, num_queries: usize, query_pow_bits: usize) -> f64 {
    let rho = 1.0 / (1u64 << log_blowup) as f64;
    let delta = (1.0 - rho) / 2.0;
    num_queries as f64 * -(1.0 - delta).log2() + query_pow_bits as f64
}

pub fn check_funds_shape(shape: FriShape, query_pow_bits: usize) -> Result<(), String> {
    let bits = unique_decoding_query_bits(shape.log_blowup, shape.num_queries, query_pow_bits);
    if bits >= TARGET_BITS {
        Ok(())
    } else {
        Err(format!("{shape:?}: {bits:.1} bits in unique decoding < {TARGET_BITS} (not funds-grade)"))
    }
}

pub fn assert_funds_shape(shape: FriShape, query_pow_bits: usize) {
    if shape != FUNDS_SHAPE || query_pow_bits != crate::faraday_fold::rec::QUERY_POW_BITS {
        panic!("{shape:?} with {query_pow_bits} grinding bits is not the consensus shape {FUNDS_SHAPE:?} (not funds-grade)");
    }
    if let Err(e) = check_funds_shape(shape, query_pow_bits) {
        panic!("{e}");
    }
}
