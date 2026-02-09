//! Monte Carlo simulation: random errors, greedy decoder, threshold estimation.
//!
//! The error model: each edge independently suffers an X error with probability p
//! and a Z error with probability p (independent depolarizing noise on each qubit).
//!
//! The greedy decoder pairs nearest syndromes and applies correction chains along
//! shortest paths. This gives a threshold of ~7-8% (vs ~10.3% for MWPM).
//!
//! A logical error occurs when the combined error+correction chain has odd parity
//! along a non-contractible cycle of the torus.

use rand::Rng;

use crate::lattice::ToricLattice;
use crate::syndrome::{Syndrome, has_any_logical_error};

/// Configuration for a Monte Carlo threshold experiment.
#[derive(Debug, Clone)]
pub struct SimConfig {
    /// Lattice size N (N×N torus with 2N² qubits).
    pub n: usize,
    /// Physical error probability per edge (X and Z independent).
    pub p_error: f64,
    /// Number of Monte Carlo trials.
    pub trials: usize,
}

/// Result of a Monte Carlo threshold experiment.
#[derive(Debug, Clone)]
pub struct SimResult {
    /// Lattice size.
    pub n: usize,
    /// Physical error rate.
    pub p_error: f64,
    /// Number of trials.
    pub trials: usize,
    /// Number of logical failures (after decoding).
    pub logical_failures: usize,
    /// Logical error rate = failures / trials.
    pub logical_error_rate: f64,
}

/// Apply random independent X and Z errors to each edge with probability p.
pub fn apply_random_errors<R: Rng>(lattice: &mut ToricLattice, p: f64, rng: &mut R) {
    let num_edges = lattice.num_edges();
    for idx in 0..num_edges {
        let edge = lattice.index_to_edge(idx);
        if rng.gen::<f64>() < p {
            lattice.apply_x_error(edge);
        }
        if rng.gen::<f64>() < p {
            lattice.apply_z_error(edge);
        }
    }
}

/// Greedy minimum-weight decoder for e-particles (Z errors).
///
/// Greedily pairs the closest e-particles and applies Z correction chains
/// along shortest paths. All pairs are matched in a single pass to avoid
/// oscillation from re-measurement.
pub fn greedy_decode_z(lattice: &mut ToricLattice) {
    let syn = Syndrome::measure(lattice);
    let locs = syn.e_particles();
    if locs.len() < 2 {
        return;
    }

    // Greedy matching: repeatedly pick the closest unpaired pair
    let mut used = vec![false; locs.len()];
    let mut pairs = Vec::new();

    for _ in 0..locs.len() / 2 {
        let mut best_dist = usize::MAX;
        let mut best = (0, 0);
        for i in 0..locs.len() {
            if used[i] { continue; }
            for j in (i + 1)..locs.len() {
                if used[j] { continue; }
                let d = lattice.vertex_distance(locs[i], locs[j]);
                if d < best_dist {
                    best_dist = d;
                    best = (i, j);
                }
            }
        }
        used[best.0] = true;
        used[best.1] = true;
        pairs.push((locs[best.0], locs[best.1]));
    }

    // Apply all corrections
    for (a, b) in pairs {
        let path = lattice.shortest_path(a, b);
        for edge in &path {
            lattice.apply_z_error(*edge);
        }
    }
}

/// Greedy minimum-weight decoder for m-particles (X errors).
///
/// Same algorithm as greedy_decode_z but for plaquette syndromes.
/// Uses dual-lattice paths: connecting plaquettes crosses the swapped edge types.
pub fn greedy_decode_x(lattice: &mut ToricLattice) {
    let syn = Syndrome::measure(lattice);
    let locs = syn.m_particles();
    if locs.len() < 2 {
        return;
    }

    let mut used = vec![false; locs.len()];
    let mut pairs = Vec::new();

    for _ in 0..locs.len() / 2 {
        let mut best_dist = usize::MAX;
        let mut best = (0, 0);
        for i in 0..locs.len() {
            if used[i] { continue; }
            for j in (i + 1)..locs.len() {
                if used[j] { continue; }
                let d = lattice.vertex_distance(locs[i], locs[j]);
                if d < best_dist {
                    best_dist = d;
                    best = (i, j);
                }
            }
        }
        used[best.0] = true;
        used[best.1] = true;
        pairs.push((locs[best.0], locs[best.1]));
    }

    for (a, b) in pairs {
        let path = lattice.dual_shortest_path(a, b);
        for edge in &path {
            lattice.apply_x_error(*edge);
        }
    }
}

/// Run both decoders (Z then X), iterating until all syndromes are removed.
///
/// A single pass may leave residual syndromes when correction chains overlap
/// existing errors. We iterate with a maximum bound to guarantee termination.
pub fn greedy_decode(lattice: &mut ToricLattice) {
    for _ in 0..lattice.size() * 2 {
        greedy_decode_z(lattice);
        greedy_decode_x(lattice);
        let syn = Syndrome::measure(lattice);
        if syn.is_clean() {
            return;
        }
    }
}

/// Run a single Monte Carlo trial.
///
/// Returns true if a logical error remains after decoding.
pub fn run_trial<R: Rng>(n: usize, p: f64, rng: &mut R) -> bool {
    let mut lattice = ToricLattice::new(n);
    apply_random_errors(&mut lattice, p, rng);
    greedy_decode(&mut lattice);
    has_any_logical_error(&lattice)
}

/// Run a full threshold experiment.
pub fn run_experiment(config: &SimConfig) -> SimResult {
    let mut rng = rand::thread_rng();
    let mut failures = 0;

    for _ in 0..config.trials {
        if run_trial(config.n, config.p_error, &mut rng) {
            failures += 1;
        }
    }

    SimResult {
        n: config.n,
        p_error: config.p_error,
        trials: config.trials,
        logical_failures: failures,
        logical_error_rate: failures as f64 / config.trials as f64,
    }
}

/// Run a threshold sweep across multiple error rates for a given lattice size.
pub fn threshold_sweep(n: usize, error_rates: &[f64], trials: usize) -> Vec<SimResult> {
    error_rates
        .iter()
        .map(|&p| {
            run_experiment(&SimConfig {
                n,
                p_error: p,
                trials,
            })
        })
        .collect()
}

/// Estimate the threshold by finding where logical error rate crosses 50%.
///
/// Returns the approximate threshold error rate, or None if not found.
pub fn estimate_threshold(results: &[SimResult]) -> Option<f64> {
    for window in results.windows(2) {
        let (a, b) = (&window[0], &window[1]);
        if a.logical_error_rate < 0.5 && b.logical_error_rate >= 0.5 {
            // Linear interpolation
            let frac = (0.5 - a.logical_error_rate)
                / (b.logical_error_rate - a.logical_error_rate);
            return Some(a.p_error + frac * (b.p_error - a.p_error));
        }
    }
    None
}

/// Run a threshold comparison across multiple lattice sizes.
pub fn compare_thresholds(
    sizes: &[usize],
    error_rates: &[f64],
    trials: usize,
) -> Vec<Vec<SimResult>> {
    sizes
        .iter()
        .map(|&n| threshold_sweep(n, error_rates, trials))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_error_rate_no_logical_errors() {
        let result = run_experiment(&SimConfig {
            n: 4,
            p_error: 0.0,
            trials: 100,
        });
        assert_eq!(
            result.logical_failures, 0,
            "Zero error rate should produce zero logical errors"
        );
    }

    #[test]
    fn test_high_error_rate_many_failures() {
        let result = run_experiment(&SimConfig {
            n: 4,
            p_error: 0.40,
            trials: 100,
        });
        // At 40% error rate, greedy decoder should fail often
        assert!(
            result.logical_error_rate > 0.1,
            "High error rate should produce many logical failures, got {}",
            result.logical_error_rate
        );
    }

    #[test]
    fn test_decoder_removes_all_syndromes() {
        let mut rng = rand::thread_rng();
        for _ in 0..20 {
            let mut lat = ToricLattice::new(6);
            apply_random_errors(&mut lat, 0.05, &mut rng);
            greedy_decode(&mut lat);
            let syn = Syndrome::measure(&lat);
            assert!(
                syn.is_clean(),
                "Decoder should remove all syndromes (got {} e, {} m)",
                syn.num_e_particles(),
                syn.num_m_particles()
            );
        }
    }

    #[test]
    fn test_threshold_sweep_monotonic() {
        let rates = vec![0.01, 0.05, 0.10, 0.15, 0.20];
        let results = threshold_sweep(4, &rates, 200);

        // Logical error rate should generally increase with physical error rate
        // (not strictly monotonic due to noise, but first should be < last)
        assert!(
            results.first().unwrap().logical_error_rate
                < results.last().unwrap().logical_error_rate,
            "Logical error rate should increase with physical error rate"
        );
    }

    #[test]
    fn test_random_errors_density() {
        let mut lat = ToricLattice::new(10);
        let mut rng = rand::thread_rng();
        apply_random_errors(&mut lat, 0.5, &mut rng);

        let x_count = lat.x_errors().iter().filter(|&&e| e).count();
        let z_count = lat.z_errors().iter().filter(|&&e| e).count();
        let total = lat.num_edges();

        // At p=0.5, expect ~50% errors. Allow wide range due to randomness.
        assert!(
            x_count > total / 4 && x_count < 3 * total / 4,
            "X error density at p=0.5 should be near 50%, got {}/{}",
            x_count,
            total
        );
        assert!(
            z_count > total / 4 && z_count < 3 * total / 4,
            "Z error density at p=0.5 should be near 50%, got {}/{}",
            z_count,
            total
        );
    }

    #[test]
    fn test_syndrome_always_even_after_random_errors() {
        let mut rng = rand::thread_rng();
        for _ in 0..50 {
            let mut lat = ToricLattice::new(6);
            apply_random_errors(&mut lat, 0.1, &mut rng);
            let syn = Syndrome::measure(&lat);
            assert_eq!(
                syn.num_e_particles() % 2,
                0,
                "e-particle count must be even"
            );
            assert_eq!(
                syn.num_m_particles() % 2,
                0,
                "m-particle count must be even"
            );
        }
    }

    #[test]
    fn test_estimate_threshold() {
        let results = vec![
            SimResult { n: 4, p_error: 0.05, trials: 100, logical_failures: 10, logical_error_rate: 0.10 },
            SimResult { n: 4, p_error: 0.10, trials: 100, logical_failures: 40, logical_error_rate: 0.40 },
            SimResult { n: 4, p_error: 0.15, trials: 100, logical_failures: 60, logical_error_rate: 0.60 },
        ];
        let threshold = estimate_threshold(&results);
        assert!(threshold.is_some());
        let t = threshold.unwrap();
        assert!(t > 0.10 && t < 0.15, "Threshold should be between 0.10 and 0.15, got {}", t);
    }
}
