//! Quantum noise channels implemented via Monte Carlo Kraus operator sampling.
//!
//! QTS supports arbitrary unitary application via `apply_matrix`. We model
//! noise as stochastic application of Kraus operators — at each noise step,
//! one Kraus operator is sampled proportional to its weight and applied as
//! a single-qubit matrix.

use num_complex::Complex;
use rand::Rng;

/// A quantum noise channel applied to individual qubits.
#[derive(Debug, Clone, Copy)]
pub enum NoiseChannel {
    /// Depolarizing channel: with probability p, applies a random Pauli.
    /// Kraus: {√(1-p)·I, √(p/3)·X, √(p/3)·Y, √(p/3)·Z}
    Depolarizing { p: f64 },

    /// Dephasing (phase-flip) channel: with probability p, applies Z.
    /// Kraus: {√(1-p)·I, √p·Z}
    Dephasing { p: f64 },

    /// Amplitude damping: models energy relaxation (T1 decay).
    /// Kraus: {[[1,0],[0,√(1-γ)]], [[0,√γ],[0,0]]}
    AmplitudeDamping { gamma: f64 },
}

/// A single-qubit 2x2 matrix stored as [row0col0, row0col1, row1col0, row1col1].
pub type Matrix2x2 = [Complex<f64>; 4];

/// Kraus operator with its sampling probability.
#[derive(Debug, Clone)]
pub struct KrausOperator {
    pub matrix: Matrix2x2,
    pub probability: f64,
}

impl NoiseChannel {
    /// Generate the Kraus operators for this channel.
    pub fn kraus_operators(&self) -> Vec<KrausOperator> {
        let zero = Complex::new(0.0, 0.0);
        let one = Complex::new(1.0, 0.0);
        let neg_one = Complex::new(-1.0, 0.0);
        let i = Complex::new(0.0, 1.0);
        let neg_i = Complex::new(0.0, -1.0);

        match *self {
            NoiseChannel::Depolarizing { p } => {
                let p = p.clamp(0.0, 1.0);
                let sqrt_id = Complex::new((1.0 - p).sqrt(), 0.0);
                let sqrt_p3 = Complex::new((p / 3.0).sqrt(), 0.0);

                vec![
                    // √(1-p) · I
                    KrausOperator {
                        matrix: [sqrt_id, zero, zero, sqrt_id],
                        probability: 1.0 - p,
                    },
                    // √(p/3) · X
                    KrausOperator {
                        matrix: [zero, sqrt_p3, sqrt_p3, zero],
                        probability: p / 3.0,
                    },
                    // √(p/3) · Y
                    KrausOperator {
                        matrix: [zero, neg_i * sqrt_p3, i * sqrt_p3, zero],
                        probability: p / 3.0,
                    },
                    // √(p/3) · Z
                    KrausOperator {
                        matrix: [sqrt_p3, zero, zero, neg_one * sqrt_p3],
                        probability: p / 3.0,
                    },
                ]
            }
            NoiseChannel::Dephasing { p } => {
                let p = p.clamp(0.0, 1.0);
                let sqrt_id = Complex::new((1.0 - p).sqrt(), 0.0);
                let sqrt_p = Complex::new(p.sqrt(), 0.0);

                vec![
                    // √(1-p) · I
                    KrausOperator {
                        matrix: [sqrt_id, zero, zero, sqrt_id],
                        probability: 1.0 - p,
                    },
                    // √p · Z
                    KrausOperator {
                        matrix: [sqrt_p, zero, zero, neg_one * sqrt_p],
                        probability: p,
                    },
                ]
            }
            NoiseChannel::AmplitudeDamping { gamma } => {
                let gamma = gamma.clamp(0.0, 1.0);
                let sqrt_1mg = Complex::new((1.0 - gamma).sqrt(), 0.0);
                let sqrt_g = Complex::new(gamma.sqrt(), 0.0);

                vec![
                    // K0 = [[1,0],[0,√(1-γ)]]
                    KrausOperator {
                        matrix: [one, zero, zero, sqrt_1mg],
                        probability: 1.0 - gamma / 2.0,
                    },
                    // K1 = [[0,√γ],[0,0]]
                    KrausOperator {
                        matrix: [zero, sqrt_g, zero, zero],
                        probability: gamma / 2.0,
                    },
                ]
            }
        }
    }

    /// Sample a Kraus operator according to the channel's probability distribution.
    pub fn sample<R: Rng>(&self, rng: &mut R) -> Matrix2x2 {
        let operators = self.kraus_operators();
        let r: f64 = rng.gen();
        let mut cumulative = 0.0;
        for op in &operators {
            cumulative += op.probability;
            if r < cumulative {
                return op.matrix;
            }
        }
        // Fallback to last operator (handles floating-point edge case)
        operators.last().unwrap().matrix
    }
}

/// Apply a noise channel to a single qubit within a QTS circuit.
///
/// This samples one Kraus operator and applies it as a 2x2 matrix gate
/// using QTS's `apply_matrix` interface. The builder and register are
/// consumed and returned following QTS's ownership pattern.
pub fn apply_noise_to_qubit<R: Rng>(
    builder: &mut QuantumTimeSandwich::builder::LocalBuilder<f64>,
    register: QuantumTimeSandwich::builder::Qudit,
    channel: &NoiseChannel,
    rng: &mut R,
) -> QuantumTimeSandwich::builder::Qudit {
    use QuantumTimeSandwich::prelude::UnitaryBuilder;

    let matrix = channel.sample(rng);
    builder.apply_matrix(register, matrix).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn depolarizing_kraus_probabilities_sum_to_one() {
        let channel = NoiseChannel::Depolarizing { p: 0.1 };
        let ops = channel.kraus_operators();
        let total: f64 = ops.iter().map(|o| o.probability).sum();
        assert!((total - 1.0).abs() < 1e-10);
    }

    #[test]
    fn dephasing_kraus_probabilities_sum_to_one() {
        let channel = NoiseChannel::Dephasing { p: 0.2 };
        let ops = channel.kraus_operators();
        let total: f64 = ops.iter().map(|o| o.probability).sum();
        assert!((total - 1.0).abs() < 1e-10);
    }

    #[test]
    fn amplitude_damping_kraus_probabilities_sum_to_one() {
        let channel = NoiseChannel::AmplitudeDamping { gamma: 0.3 };
        let ops = channel.kraus_operators();
        let total: f64 = ops.iter().map(|o| o.probability).sum();
        assert!((total - 1.0).abs() < 1e-10);
    }

    #[test]
    fn zero_noise_is_identity() {
        let channel = NoiseChannel::Depolarizing { p: 0.0 };
        let ops = channel.kraus_operators();
        // Only the identity operator should have non-zero probability
        assert!((ops[0].probability - 1.0).abs() < 1e-10);
        // Verify it's the identity matrix
        let m = &ops[0].matrix;
        assert!((m[0].re - 1.0).abs() < 1e-10);
        assert!((m[3].re - 1.0).abs() < 1e-10);
        assert!(m[1].norm() < 1e-10);
        assert!(m[2].norm() < 1e-10);
    }

    #[test]
    fn kraus_completeness_depolarizing() {
        // Verify sum of K†K = I for depolarizing channel
        let channel = NoiseChannel::Depolarizing { p: 0.15 };
        let ops = channel.kraus_operators();
        let zero = Complex::new(0.0, 0.0);
        let mut sum = [zero; 4]; // 2x2 accumulator

        for op in &ops {
            let k = &op.matrix;
            // K†K: (k†)_ij * k_jl
            // k† = conjugate transpose
            let kd = [k[0].conj(), k[2].conj(), k[1].conj(), k[3].conj()];
            // Matrix multiply kd * k
            sum[0] += kd[0] * k[0] + kd[1] * k[2];
            sum[1] += kd[0] * k[1] + kd[1] * k[3];
            sum[2] += kd[2] * k[0] + kd[3] * k[2];
            sum[3] += kd[2] * k[1] + kd[3] * k[3];
        }

        assert!((sum[0].re - 1.0).abs() < 1e-10, "sum[0,0] = {:?}", sum[0]);
        assert!(sum[1].norm() < 1e-10, "sum[0,1] = {:?}", sum[1]);
        assert!(sum[2].norm() < 1e-10, "sum[1,0] = {:?}", sum[2]);
        assert!((sum[3].re - 1.0).abs() < 1e-10, "sum[1,1] = {:?}", sum[3]);
    }

    #[test]
    fn sampling_returns_valid_operator() {
        let channel = NoiseChannel::Depolarizing { p: 0.5 };
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let m = channel.sample(&mut rng);
            // Every sampled matrix should have at least one non-zero entry
            let norm: f64 = m.iter().map(|c| c.norm_sqr()).sum();
            assert!(norm > 0.0);
        }
    }
}
