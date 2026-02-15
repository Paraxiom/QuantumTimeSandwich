//! Toroidal lattice geometry and spectral analysis on T².
//!
//! The 2-torus T² = (Z/NZ)² with 4-connected nearest-neighbor lattice.
//! Physical size L means lattice spacing ℓ = L/N.
//!
//! # Spectral gap
//!
//! The Laplacian on the N×N torus has eigenvalues:
//!   λ_{j,k} = 4 - 2cos(2πj/N) - 2cos(2πk/N)
//!
//! The spectral gap (smallest nonzero eigenvalue) is:
//!   λ₁ = 2 - 2cos(2π/N) ≈ 2π²/N² for large N
//!
//! This gap controls:
//! - Heat kernel decay rate on the lattice
//! - Random walk mixing time: t_mix ~ 1/λ₁
//! - Coherence time under noise: τ ~ -ln(ε)/λ₁
//! - Minimum resolvable energy in vacuum field theory on T²

use crate::units::{PI, C};

/// A toroidal lattice with physical embedding.
#[derive(Debug, Clone)]
pub struct TorusLattice {
    /// Lattice dimension (N×N grid on T²)
    pub n: usize,
    /// Physical size of the torus (meters)
    pub length: f64,
}

impl TorusLattice {
    pub fn new(n: usize, length: f64) -> Self {
        Self { n, length }
    }

    /// Lattice spacing ℓ = L/N (meters)
    pub fn lattice_spacing(&self) -> f64 {
        self.length / self.n as f64
    }

    /// Total number of sites on T²
    pub fn num_sites(&self) -> usize {
        self.n * self.n
    }

    /// Spectral gap: λ₁ = 2 - 2cos(2π/N)
    pub fn spectral_gap(&self) -> f64 {
        2.0 - 2.0 * (2.0 * PI / self.n as f64).cos()
    }

    /// Full Laplacian spectrum.
    /// Returns all N² eigenvalues sorted ascending.
    pub fn spectrum(&self) -> Vec<f64> {
        let n = self.n;
        let mut eigenvalues = Vec::with_capacity(n * n);
        for j in 0..n {
            for k in 0..n {
                let lam = 4.0
                    - 2.0 * (2.0 * PI * j as f64 / n as f64).cos()
                    - 2.0 * (2.0 * PI * k as f64 / n as f64).cos();
                eigenvalues.push(lam);
            }
        }
        eigenvalues.sort_by(|a, b| a.partial_cmp(b).unwrap());
        eigenvalues
    }

    /// Distinct eigenvalues with multiplicities.
    pub fn spectrum_with_multiplicities(&self) -> Vec<(f64, usize)> {
        let spec = self.spectrum();
        let mut result: Vec<(f64, usize)> = Vec::new();
        let eps = 1e-10;
        for &lam in &spec {
            if let Some(last) = result.last_mut() {
                if (lam - last.0).abs() < eps {
                    last.1 += 1;
                    continue;
                }
            }
            result.push((lam, 1));
        }
        result
    }

    /// Physical mode frequencies ω_{n₁,n₂} = (2πc/L)√(n₁² + n₂²).
    /// Returns nonzero frequencies sorted ascending.
    pub fn mode_frequencies(&self) -> Vec<f64> {
        let n = self.n as i64;
        let half = n / 2;
        let omega_unit = 2.0 * PI * C / self.length;
        let mut freqs = Vec::new();
        for n1 in -half..=half {
            for n2 in -half..=half {
                if n1 == 0 && n2 == 0 {
                    continue;
                }
                let r2 = (n1 * n1 + n2 * n2) as f64;
                freqs.push(omega_unit * r2.sqrt());
            }
        }
        freqs.sort_by(|a, b| a.partial_cmp(b).unwrap());
        freqs
    }

    /// Minimum nonzero mode frequency (Hz).
    /// ω_min = 2πc/L — the fundamental mode.
    pub fn omega_min(&self) -> f64 {
        2.0 * PI * C / self.length
    }

    /// Maximum mode frequency (UV cutoff from lattice, Hz).
    /// ω_max = πc/ℓ = πcN/L
    pub fn omega_max(&self) -> f64 {
        PI * C * self.n as f64 / self.length
    }

    /// Mixing time estimate: t_mix ~ 1/λ₁ (in lattice time units).
    /// Physical mixing time: t_mix × (L/(2πc)) for relativistic field.
    pub fn mixing_time_lattice(&self) -> f64 {
        1.0 / self.spectral_gap()
    }

    /// Physical mixing time for a relativistic field on T² (seconds).
    pub fn mixing_time_physical(&self) -> f64 {
        self.mixing_time_lattice() * self.length / (2.0 * PI * C)
    }

    /// Toroidal distance between two lattice sites (lattice units).
    pub fn distance(&self, i: (usize, usize), j: (usize, usize)) -> usize {
        let n = self.n;
        let dx = {
            let d = (i.0 as isize - j.0 as isize).unsigned_abs();
            d.min(n - d)
        };
        let dy = {
            let d = (i.1 as isize - j.1 as isize).unsigned_abs();
            d.min(n - d)
        };
        dx + dy
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spectral_gap_4x4() {
        let t = TorusLattice::new(4, 1.0);
        let gap = t.spectral_gap();
        let expected = 2.0 - 2.0 * (PI / 2.0).cos(); // 2 - 0 = 2
        assert!((gap - expected).abs() < 1e-12);
    }

    #[test]
    fn spectral_gap_decreases_with_n() {
        let g4 = TorusLattice::new(4, 1.0).spectral_gap();
        let g8 = TorusLattice::new(8, 1.0).spectral_gap();
        let g16 = TorusLattice::new(16, 1.0).spectral_gap();
        assert!(g4 > g8);
        assert!(g8 > g16);
    }

    #[test]
    fn spectrum_starts_at_zero() {
        let t = TorusLattice::new(6, 1.0);
        let spec = t.spectrum();
        assert!(spec[0].abs() < 1e-12);
    }

    #[test]
    fn spectrum_second_eigenvalue_is_gap() {
        let t = TorusLattice::new(8, 1.0);
        let spec = t.spectrum();
        let gap = t.spectral_gap();
        assert!((spec[1] - gap).abs() < 1e-10);
    }

    #[test]
    fn toroidal_distance_wraps() {
        let t = TorusLattice::new(8, 1.0);
        assert_eq!(t.distance((0, 0), (7, 0)), 1); // wraps
        assert_eq!(t.distance((0, 0), (4, 4)), 8); // max distance
        assert_eq!(t.distance((3, 3), (3, 3)), 0);
    }
}

// ─── Kani formal verification harnesses ─────────────────────────────────────
//
// Kani's CBMC backend models cos/sin non-deterministically, so we split proofs:
//   - Pure integer / pointer / panic-freedom proofs: use symbolic inputs
//   - Value properties of transcendental outputs: use concrete N values
//
#[cfg(kani)]
mod kani_proofs {
    use super::*;

    // ── Pure integer proofs (fully symbolic) ────────────────────────────────

    /// Prove num_sites == n*n for any N.
    #[kani::proof]
    #[kani::unwind(2)]
    fn num_sites_is_n_squared() {
        let n: usize = kani::any();
        kani::assume(n >= 1 && n <= 256);
        let t = TorusLattice::new(n, 1.0);
        assert_eq!(t.num_sites(), n * n);
    }

    /// Prove distance is symmetric: d(i,j) == d(j,i).
    #[kani::proof]
    #[kani::unwind(2)]
    fn distance_symmetric() {
        let n: usize = kani::any();
        kani::assume(n >= 2 && n <= 64);
        let t = TorusLattice::new(n, 1.0);

        let i0: usize = kani::any();
        let i1: usize = kani::any();
        let j0: usize = kani::any();
        let j1: usize = kani::any();
        kani::assume(i0 < n && i1 < n && j0 < n && j1 < n);

        assert_eq!(t.distance((i0, i1), (j0, j1)), t.distance((j0, j1), (i0, i1)));
    }

    /// Prove distance to self is zero.
    #[kani::proof]
    #[kani::unwind(2)]
    fn distance_to_self_zero() {
        let n: usize = kani::any();
        kani::assume(n >= 1 && n <= 64);
        let t = TorusLattice::new(n, 1.0);

        let i0: usize = kani::any();
        let i1: usize = kani::any();
        kani::assume(i0 < n && i1 < n);

        assert_eq!(t.distance((i0, i1), (i0, i1)), 0);
    }

    /// Prove distance is bounded by N (Manhattan max on N×N torus).
    #[kani::proof]
    #[kani::unwind(2)]
    fn distance_bounded() {
        let n: usize = kani::any();
        kani::assume(n >= 2 && n <= 64);
        let t = TorusLattice::new(n, 1.0);

        let i0: usize = kani::any();
        let i1: usize = kani::any();
        let j0: usize = kani::any();
        let j1: usize = kani::any();
        kani::assume(i0 < n && i1 < n && j0 < n && j1 < n);

        let d = t.distance((i0, i1), (j0, j1));
        // Max Manhattan distance on N-torus is N (N/2 per axis)
        assert!(d <= n);
    }

    // ── Panic-freedom proofs (symbolic, no value assertions on cos output) ──

    /// Prove spectral_gap never panics for any valid N and length.
    /// Note: does NOT assert value because cos() is non-deterministic in CBMC.
    #[kani::proof]
    #[kani::unwind(2)]
    fn spectral_gap_no_panic() {
        let n: usize = kani::any();
        kani::assume(n >= 1 && n <= 256);
        let t = TorusLattice::new(n, 1.0);
        let _gap = t.spectral_gap(); // no panic
    }

    /// Prove lattice_spacing never panics (pure f64 division).
    #[kani::proof]
    #[kani::unwind(2)]
    fn lattice_spacing_no_panic() {
        let n: usize = kani::any();
        kani::assume(n >= 1 && n <= 256);
        let length: f64 = kani::any();
        kani::assume(length > 1e-30 && length.is_finite() && length < 1e10);
        let t = TorusLattice::new(n, length);
        let _spacing = t.lattice_spacing(); // no panic
    }

    /// Prove mixing_time_lattice never panics.
    #[kani::proof]
    #[kani::unwind(2)]
    fn mixing_time_no_panic() {
        let n: usize = kani::any();
        kani::assume(n >= 2 && n <= 256);
        let t = TorusLattice::new(n, 1.0);
        let _mix = t.mixing_time_lattice(); // no panic (divides by spectral_gap)
    }

    // NOTE: Value properties of spectral_gap (positivity, monotonicity, bounds)
    // depend on cos() which CBMC models non-deterministically. These properties
    // are instead verified by the 47 unit tests in this crate, including
    // cross-validation against full numerical eigendecomposition (spectral.rs).
    // See: spectral_gap_4x4, spectral_gap_decreases_with_n,
    //      spectrum_second_eigenvalue_is_gap, torus_spectrum_matches_analytic.
}
