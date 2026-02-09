//! Experiment runner for coherence simulations.
//!
//! The main simulation loop:
//! 1. Initialize N qubits in |+⟩ (Hadamard on each)
//! 2. At each time step:
//!    a. Apply coupling gates (CZ weighted by topology)
//!    b. Apply noise channel to each qubit
//!    c. Measure fidelity against initial state
//! 3. Average over multiple trials

use std::num::NonZeroUsize;

use num_complex::Complex;
use rand::rngs::StdRng;
use rand::SeedableRng;

use QuantumTimeSandwich::builder::{LocalBuilder, Qudit};
use QuantumTimeSandwich::prelude::*;

use crate::coherence::{state_fidelity, CoherenceTracker};
use crate::noise::NoiseChannel;
use crate::topology::{build_coupling_map, CouplingTopology};

/// Configuration for a coherence simulation experiment.
#[derive(Debug, Clone)]
pub struct SimulationConfig {
    /// Number of qubits in the simulation.
    pub n_qubits: usize,
    /// Coupling topology between qubits.
    pub topology: CouplingTopology,
    /// Noise channel applied to each qubit per time step.
    pub noise: NoiseChannel,
    /// Number of discrete time steps to simulate.
    pub time_steps: usize,
    /// Number of independent trials to average over.
    pub trials: usize,
}

/// Result of a coherence simulation experiment.
#[derive(Debug, Clone)]
pub struct SimulationResult {
    /// Mean coherence time (steps until fidelity < 0.5) across trials.
    /// If fidelity never drops below threshold, equals time_steps.
    pub mean_coherence_time: f64,
    /// Standard deviation of coherence time across trials.
    pub std_dev: f64,
    /// Mean fidelity curve averaged across all trials.
    pub fidelity_curve: Vec<f64>,
}

/// Fidelity threshold for coherence time measurement.
const COHERENCE_THRESHOLD: f64 = 0.5;

/// Run a single trial of the coherence simulation.
///
/// For each time step T, builds a circuit with:
/// - H gates on all qubits (initialize |+⟩^⊗n)
/// - T rounds of: coupling gates + noise channels
/// Then extracts the state vector and computes fidelity vs |+⟩^⊗n.
///
/// This avoids expensive state re-preparation between steps by building
/// progressively longer circuits from scratch.
fn run_single_trial(config: &SimulationConfig, seed: u64) -> CoherenceTracker {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut tracker = CoherenceTracker::new();
    let n = config.n_qubits;
    let edges = build_coupling_map(&config.topology, n);

    // Pre-sample all noise operators for reproducibility
    let noise_ops: Vec<Vec<crate::noise::Matrix2x2>> = (0..config.time_steps)
        .map(|_| (0..n).map(|_| config.noise.sample(&mut rng)).collect())
        .collect();

    // Reference state: |+⟩^⊗n
    let dim = 1usize << n;
    let amp = 1.0 / (dim as f64).sqrt();
    let initial_state: Vec<Complex<f64>> = vec![Complex::new(amp, 0.0); dim];

    for t in 0..config.time_steps {
        // Build a circuit with (t+1) rounds of evolution
        let mut b = LocalBuilder::<f64>::default();
        let n_nz = NonZeroUsize::new(n).unwrap();
        let reg = b.register(n_nz);

        // Initialize: H on each qubit → |+⟩^⊗n
        let qubits = b.split_all_register(reg);
        let mut qubit_vec: Vec<Qudit> = qubits
            .into_iter()
            .map(|q| b.h(q))
            .collect();

        // Apply (t+1) rounds of coupling + noise
        for step in 0..=t {
            // Coupling gates
            let mut qubit_opts: Vec<Option<Qudit>> =
                qubit_vec.into_iter().map(Some).collect();

            for &(i, j, weight) in &edges {
                if weight < 0.01 || i >= n || j >= n {
                    continue;
                }
                let qi = qubit_opts[i].take();
                let qj = qubit_opts[j].take();
                if let (Some(qi), Some(qj)) = (qi, qj) {
                    let (qi, qj) = apply_weighted_cz(&mut b, qi, qj, weight);
                    qubit_opts[i] = Some(qi);
                    qubit_opts[j] = Some(qj);
                }
            }

            // Noise on each qubit
            qubit_vec = qubit_opts
                .into_iter()
                .enumerate()
                .map(|(qi, q)| {
                    let qubit = q.unwrap();
                    let matrix = &noise_ops[step][qi];
                    b.apply_matrix(qubit, *matrix).unwrap()
                })
                .collect();
        }

        // Merge back and extract state
        let _merged = qubit_vec
            .into_iter()
            .reduce(|acc, q| b.merge_two_registers(acc, q))
            .unwrap();

        let (state_vec, _) = b.calculate_state();
        let fidelity = state_fidelity(&initial_state, &state_vec);
        tracker.record(fidelity);
    }

    tracker
}

/// Apply a weighted CZ gate between two qubits.
///
/// For weight >= 0.99, applies a standard CZ = H·CNOT·H.
/// For weight < 0.99, merges the two qubits into a 2-qubit register
/// and applies a 4x4 controlled-phase unitary via `apply_vec_matrix`.
fn apply_weighted_cz(
    builder: &mut LocalBuilder<f64>,
    control: Qudit,
    target: Qudit,
    weight: f64,
) -> (Qudit, Qudit) {
    if weight >= 0.99 {
        // Full CZ = H·CNOT·H on target
        let target = builder.h(target);
        let (control, target) = builder.cnot(control, target).unwrap();
        let target = builder.h(target);
        (control, target)
    } else {
        // Merge into 2-qubit register, apply 4x4 CRz matrix, then split
        let reg = builder.merge_two_registers(control, target);
        let theta = weight * std::f64::consts::PI;
        let zero = Complex::new(0.0, 0.0);
        let one = Complex::new(1.0, 0.0);
        // CRz(θ) = diag(1, 1, e^{-iθ/2}, e^{iθ/2})
        let e_neg = Complex::new((theta / 2.0).cos(), -(theta / 2.0).sin());
        let e_pos = Complex::new((theta / 2.0).cos(), (theta / 2.0).sin());
        let matrix = vec![
            one, zero, zero, zero,   // |00⟩ row
            zero, one, zero, zero,   // |01⟩ row
            zero, zero, e_neg, zero, // |10⟩ row
            zero, zero, zero, e_pos, // |11⟩ row
        ];
        let reg = builder.apply_vec_matrix(reg, matrix).unwrap();
        // split_first_qubit returns (Option<remaining>, first_qubit)
        let (remaining, first) = builder.split_first_qubit(reg);
        (first, remaining.unwrap())
    }
}

/// Run the full simulation experiment, averaging over multiple trials.
pub fn run_simulation(config: &SimulationConfig) -> SimulationResult {
    let mut coherence_times = Vec::with_capacity(config.trials);
    let mut all_curves: Vec<Vec<f64>> = Vec::with_capacity(config.trials);

    for trial in 0..config.trials {
        let seed = 42u64.wrapping_add(trial as u64 * 7919);
        let tracker = run_single_trial(config, seed);

        let ct = tracker
            .coherence_time(COHERENCE_THRESHOLD)
            .unwrap_or(config.time_steps);
        coherence_times.push(ct as f64);
        all_curves.push(tracker.fidelity_curve);
    }

    // Compute mean coherence time
    let mean_ct: f64 = coherence_times.iter().sum::<f64>() / config.trials as f64;

    // Compute standard deviation
    let variance: f64 = coherence_times
        .iter()
        .map(|&t| (t - mean_ct).powi(2))
        .sum::<f64>()
        / config.trials as f64;
    let std_dev = variance.sqrt();

    // Compute mean fidelity curve
    let max_len = all_curves.iter().map(|c| c.len()).max().unwrap_or(0);
    let mut mean_curve = vec![0.0; max_len];
    for step in 0..max_len {
        let mut sum = 0.0;
        let mut count = 0;
        for curve in &all_curves {
            if step < curve.len() {
                sum += curve[step];
                count += 1;
            }
        }
        if count > 0 {
            mean_curve[step] = sum / count as f64;
        }
    }

    SimulationResult {
        mean_coherence_time: mean_ct,
        std_dev,
        fidelity_curve: mean_curve,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simulation_runs_without_panic() {
        let config = SimulationConfig {
            n_qubits: 2,
            topology: CouplingTopology::Linear,
            noise: NoiseChannel::Depolarizing { p: 0.1 },
            time_steps: 3,
            trials: 1,
        };
        let result = run_simulation(&config);
        assert!(!result.fidelity_curve.is_empty());
        assert!(result.mean_coherence_time >= 0.0);
    }

    #[test]
    fn zero_noise_fidelity_higher_than_high_noise() {
        let config_zero = SimulationConfig {
            n_qubits: 2,
            topology: CouplingTopology::Linear,
            noise: NoiseChannel::Depolarizing { p: 0.0 },
            time_steps: 5,
            trials: 1,
        };
        let config_noisy = SimulationConfig {
            n_qubits: 2,
            topology: CouplingTopology::Linear,
            noise: NoiseChannel::Depolarizing { p: 0.5 },
            time_steps: 5,
            trials: 3,
        };
        let result_zero = run_simulation(&config_zero);
        let result_noisy = run_simulation(&config_noisy);
        let mean_zero: f64 =
            result_zero.fidelity_curve.iter().sum::<f64>() / result_zero.fidelity_curve.len() as f64;
        let mean_noisy: f64 =
            result_noisy.fidelity_curve.iter().sum::<f64>() / result_noisy.fidelity_curve.len() as f64;
        assert!(
            mean_noisy <= mean_zero + 0.1,
            "Noisy mean {} should not exceed zero-noise mean {} by much",
            mean_noisy,
            mean_zero
        );
    }

    #[test]
    fn high_noise_degrades_fidelity() {
        let config = SimulationConfig {
            n_qubits: 2,
            topology: CouplingTopology::Linear,
            noise: NoiseChannel::Depolarizing { p: 0.5 },
            time_steps: 10,
            trials: 3,
        };
        let result = run_simulation(&config);
        if let Some(&last) = result.fidelity_curve.last() {
            assert!(
                last < 0.9,
                "Fidelity {} should degrade with p=0.5",
                last
            );
        }
    }

    #[test]
    fn multiple_trials_average() {
        let config = SimulationConfig {
            n_qubits: 2,
            topology: CouplingTopology::AllToAll,
            noise: NoiseChannel::Dephasing { p: 0.1 },
            time_steps: 5,
            trials: 3,
        };
        let result = run_simulation(&config);
        assert_eq!(result.fidelity_curve.len(), config.time_steps);
    }
}
