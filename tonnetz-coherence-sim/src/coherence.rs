//! Coherence measurement and tracking.
//!
//! Provides fidelity computation between quantum states and time-series
//! tracking of coherence decay. Connects to the topological-coherence
//! crate's spectral gap for theoretical bound comparison.

use num_complex::Complex;

/// Compute the state fidelity |⟨a|b⟩|² between two state vectors.
///
/// Both vectors must have the same length (2^n amplitudes).
/// Returns a value in [0, 1] where 1 means identical states.
pub fn state_fidelity(a: &[Complex<f64>], b: &[Complex<f64>]) -> f64 {
    assert_eq!(a.len(), b.len(), "State vectors must have equal length");
    let inner: Complex<f64> = a.iter().zip(b.iter()).map(|(ai, bi)| ai.conj() * bi).sum();
    inner.norm_sqr()
}

/// Tracks fidelity measurements over time steps.
#[derive(Debug, Clone)]
pub struct CoherenceTracker {
    /// Fidelity at each time step.
    pub fidelity_curve: Vec<f64>,
}

impl CoherenceTracker {
    /// Create a new tracker.
    pub fn new() -> Self {
        Self {
            fidelity_curve: Vec::new(),
        }
    }

    /// Record a fidelity measurement for the current time step.
    pub fn record(&mut self, fidelity: f64) {
        self.fidelity_curve.push(fidelity);
    }

    /// Find the coherence time: the first time step where fidelity drops
    /// below the given threshold. Returns `None` if fidelity never drops
    /// below threshold.
    pub fn coherence_time(&self, threshold: f64) -> Option<usize> {
        self.fidelity_curve
            .iter()
            .position(|&f| f < threshold)
    }

    /// Return the number of recorded time steps.
    pub fn len(&self) -> usize {
        self.fidelity_curve.len()
    }

    /// Check if no measurements have been recorded.
    pub fn is_empty(&self) -> bool {
        self.fidelity_curve.is_empty()
    }

    /// Mean fidelity across all recorded steps.
    pub fn mean_fidelity(&self) -> f64 {
        if self.fidelity_curve.is_empty() {
            return 0.0;
        }
        let sum: f64 = self.fidelity_curve.iter().sum();
        sum / self.fidelity_curve.len() as f64
    }
}

impl Default for CoherenceTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Theoretical coherence decay rate from Tonnetz spectral gap.
///
/// For a grid of size N, the spectral gap λ₁ = 2 - 2cos(2π/N).
/// Coherence decays as exp(-λ₁ * t) on the torus, giving a √N
/// advantage for the toroidal topology.
pub fn theoretical_decay_rate(grid_size: usize) -> f64 {
    let n = grid_size as f64;
    2.0 - 2.0 * (2.0 * std::f64::consts::PI / n).cos()
}

/// Theoretical coherence time: t such that exp(-λ₁ * t) = threshold.
/// Returns t = -ln(threshold) / λ₁.
pub fn theoretical_coherence_time(grid_size: usize, threshold: f64) -> f64 {
    let lambda = theoretical_decay_rate(grid_size);
    if lambda <= 0.0 {
        return f64::INFINITY;
    }
    -threshold.ln() / lambda
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fidelity_of_identical_states() {
        let state = vec![
            Complex::new(1.0 / 2.0_f64.sqrt(), 0.0),
            Complex::new(1.0 / 2.0_f64.sqrt(), 0.0),
        ];
        let f = state_fidelity(&state, &state);
        assert!((f - 1.0).abs() < 1e-10);
    }

    #[test]
    fn fidelity_of_orthogonal_states() {
        let a = vec![Complex::new(1.0, 0.0), Complex::new(0.0, 0.0)];
        let b = vec![Complex::new(0.0, 0.0), Complex::new(1.0, 0.0)];
        let f = state_fidelity(&a, &b);
        assert!(f.abs() < 1e-10);
    }

    #[test]
    fn fidelity_symmetric() {
        let a = vec![
            Complex::new(0.6, 0.0),
            Complex::new(0.0, 0.8),
        ];
        let b = vec![
            Complex::new(1.0 / 2.0_f64.sqrt(), 0.0),
            Complex::new(1.0 / 2.0_f64.sqrt(), 0.0),
        ];
        let f1 = state_fidelity(&a, &b);
        let f2 = state_fidelity(&b, &a);
        assert!((f1 - f2).abs() < 1e-10);
    }

    #[test]
    fn coherence_tracker_finds_time() {
        let mut tracker = CoherenceTracker::new();
        tracker.record(1.0);
        tracker.record(0.9);
        tracker.record(0.7);
        tracker.record(0.4);
        tracker.record(0.2);

        assert_eq!(tracker.coherence_time(0.5), Some(3));
        assert_eq!(tracker.coherence_time(0.1), None); // 0.2 >= 0.1, never drops below
        assert_eq!(tracker.coherence_time(0.3), Some(4)); // 0.2 < 0.3 at step 4
    }

    #[test]
    fn coherence_tracker_none_if_never_drops() {
        let mut tracker = CoherenceTracker::new();
        tracker.record(1.0);
        tracker.record(0.95);
        tracker.record(0.9);
        assert_eq!(tracker.coherence_time(0.5), None);
    }

    #[test]
    fn mean_fidelity() {
        let mut tracker = CoherenceTracker::new();
        tracker.record(1.0);
        tracker.record(0.5);
        assert!((tracker.mean_fidelity() - 0.75).abs() < 1e-10);
    }

    #[test]
    fn theoretical_decay_rate_positive() {
        for n in [4, 8, 12, 16] {
            let rate = theoretical_decay_rate(n);
            assert!(rate > 0.0, "Rate should be positive for grid_size={}", n);
        }
    }

    #[test]
    fn theoretical_coherence_time_increases_with_grid() {
        // Larger grid → smaller spectral gap → longer coherence time
        let t4 = theoretical_coherence_time(4, 0.5);
        let t8 = theoretical_coherence_time(8, 0.5);
        let t16 = theoretical_coherence_time(16, 0.5);
        assert!(t8 > t4, "t8={} should > t4={}", t8, t4);
        assert!(t16 > t8, "t16={} should > t8={}", t16, t8);
    }
}
