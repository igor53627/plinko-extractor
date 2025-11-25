use aes::cipher::{BlockEncrypt, KeyInit, generic_array::GenericArray};
use aes::Aes128;
use sha2::{Sha256, Digest};

pub type PrfKey128 = [u8; 16];

pub struct Iprf {
    key: PrfKey128,
    cipher: Aes128,
    domain: u64,
    range: u64,
    _tree_depth: usize,
}

const INV_TWO_TO_53: f64 = 1.0 / (1u64 << 53) as f64;

impl Iprf {
    pub fn new(key: PrfKey128, n: u64, m: u64) -> Self {
        let tree_depth = (m as f64).log2().ceil() as usize;
        let cipher = Aes128::new(&GenericArray::from(key));
        
        Self {
            key,
            cipher,
            domain: n,
            range: m,
            _tree_depth: tree_depth,
        }
    }

    pub fn forward(&self, x: u64) -> u64 {
        if x >= self.domain {
            return 0;
        }
        self.trace_ball(x, self.domain, self.range)
    }

    fn trace_ball(&self, x_prime: u64, n: u64, m: u64) -> u64 {
        if m == 1 {
            return 0;
        }

        let mut low = 0u64;
        let mut high = m - 1;
        let mut ball_count = n;
        let mut ball_index = x_prime;

        while low < high {
            let mid = (low + high) / 2;
            let left_bins = mid - low + 1;
            let total_bins = high - low + 1;

            let p = left_bins as f64 / total_bins as f64;
            
            let node_id = encode_node(low, high, n);
            let prf_output = self.prf_eval(node_id);
            
            // Map to (0, 1)
            let uniform = ((prf_output >> 11) as f64 + 0.5) * INV_TWO_TO_53;
            
            let left_count = self.binomial_inverse_cdf(ball_count, p, uniform);

            if ball_index < left_count {
                // Ball goes left
                high = mid;
                ball_count = left_count;
            } else {
                // Ball goes right
                low = mid + 1;
                ball_index -= left_count;
                ball_count -= left_count;
            }
        }
        low
    }

    fn binomial_inverse_cdf(&self, n: u64, p: f64, u: f64) -> u64 {
        if u <= 0.0 { return 0; }
        if u >= 1.0 { return n; }
        if p == 0.0 { return 0; }
        if p == 1.0 { return n; }
        if n == 0 { return 0; }

        if n > 100 {
            return self.normal_approx_binomial(n, p, u);
        }

        let mut cum_prob = 0.0;
        let q = 1.0 - p;
        let mut prob = q.powf(n as f64);
        cum_prob += prob;

        if u <= cum_prob {
            return 0;
        }

        for k in 0..n {
            prob = prob * (n - k) as f64 / (k + 1) as f64 * p / q;
            cum_prob += prob;
            if u <= cum_prob {
                return k + 1;
            }
        }
        n
    }

    fn normal_approx_binomial(&self, n: u64, p: f64, u: f64) -> u64 {
        let mean = n as f64 * p;
        let variance = n as f64 * p * (1.0 - p);
        let stddev = variance.sqrt();

        let u_clamped = u.clamp(0.001, 0.999);
        let z = inv_normal_cdf(u_clamped);
        let result = mean + z * stddev;

        if result < 0.0 { return 0; }
        if result > n as f64 { return n; }
        
        result.round() as u64
    }

    fn prf_eval(&self, x: u64) -> u64 {
        let mut input = [0u8; 16];
        input[8..16].copy_from_slice(&x.to_be_bytes()); // Put x in last 8 bytes (BigEndian per Go code)
        
        let mut block = GenericArray::from(input);
        self.cipher.encrypt_block(&mut block);
        
        u64::from_be_bytes(block[0..8].try_into().unwrap())
    }
}

fn encode_node(low: u64, high: u64, n: u64) -> u64 {
    let mut hasher = Sha256::new();
    hasher.update(&low.to_be_bytes());
    hasher.update(&high.to_be_bytes());
    hasher.update(&n.to_be_bytes());
    let result = hasher.finalize();
    u64::from_be_bytes(result[0..8].try_into().unwrap())
}

fn inv_normal_cdf(p: f64) -> f64 {
    if p <= 0.0 || p >= 1.0 {
        if p <= 0.0 { return -10.0; }
        if p >= 1.0 { return 10.0; }
    }

    const A0: f64 = 2.50662823884;
    const A1: f64 = -18.61500062529;
    const A2: f64 = 41.39119773534;
    const A3: f64 = -25.44106049637;
    const B0: f64 = -8.47351093090;
    const B1: f64 = 23.08336743743;
    const B2: f64 = -21.06224101826;
    const B3: f64 = 3.13082909833;

    let y = p - 0.5;
    if y.abs() < 0.42 {
        let r = y * y;
        return y * (((A3 * r + A2) * r + A1) * r + A0) / ((((B3 * r + B2) * r + B1) * r + B0) * r + 1.0);
    }

    if y > 0.0 { 2.0 } else { -2.0 }
}
