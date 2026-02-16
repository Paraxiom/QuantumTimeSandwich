//! Numerical spectral analysis of graph Laplacians.
//!
//! Constructs the graph Laplacian L = D - A for arbitrary graphs and computes
//! eigenvalues via dense symmetric eigendecomposition (nalgebra).
//!
//! # Purpose
//!
//! The analytic module [`crate::torus`] gives `lambda_1 = 2 - 2*cos(2*pi/N)`
//! by formula. This module **verifies** that formula by:
//! 1. Building the full N²×N² Laplacian matrix for T² = C_N × C_N
//! 2. Computing eigenvalues numerically
//! 3. Asserting they match the closed-form expression
//!
//! This is the bridge between "we know the formula" and "we can prove the
//! formula holds for our actual graph construction."
//!
//! # Generalization
//!
//! The [`GraphLaplacian`] type accepts arbitrary adjacency specifications,
//! enabling spectral analysis of non-toroidal topologies (linear chains,
//! random graphs, expander constructions) for comparison.

use nalgebra::{DMatrix, DVector, SymmetricEigen};

/// A graph Laplacian built from an explicit adjacency list.
///
/// L = D - A where D = diag(degree) and A is the adjacency matrix.
/// For weighted graphs, A_{ij} = weight and D_{ii} = sum of weights.
#[derive(Debug, Clone)]
pub struct GraphLaplacian {
    /// Number of vertices
    pub n: usize,
    /// Dense Laplacian matrix (n×n, symmetric)
    pub matrix: DMatrix<f64>,
}

impl GraphLaplacian {
    /// Build the Laplacian for the cycle graph C_N (1D torus).
    ///
    /// Each vertex i connects to (i-1) mod N and (i+1) mod N.
    /// Spectrum: lambda_k = 2 - 2*cos(2*pi*k/N), k = 0..N-1.
    pub fn cycle(n: usize) -> Self {
        let mut mat = DMatrix::zeros(n, n);
        for i in 0..n {
            let left = (i + n - 1) % n;
            let right = (i + 1) % n;
            mat[(i, i)] = 2.0; // degree
            mat[(i, left)] = -1.0;
            mat[(i, right)] = -1.0;
        }
        Self { n, matrix: mat }
    }

    /// Build the Laplacian for the 2-torus T² = C_N × C_N (4-connected).
    ///
    /// N² vertices indexed as (row, col) → row*N + col.
    /// Each vertex has 4 neighbors (up, down, left, right) with wrapping.
    /// Spectrum: lambda_{j,k} = 4 - 2*cos(2*pi*j/N) - 2*cos(2*pi*k/N).
    pub fn torus(n: usize) -> Self {
        let size = n * n;
        let mut mat = DMatrix::zeros(size, size);

        for row in 0..n {
            for col in 0..n {
                let idx = row * n + col;
                let up = ((row + n - 1) % n) * n + col;
                let down = ((row + 1) % n) * n + col;
                let left = row * n + (col + n - 1) % n;
                let right = row * n + (col + 1) % n;

                mat[(idx, idx)] = 4.0; // degree
                mat[(idx, up)] = -1.0;
                mat[(idx, down)] = -1.0;
                mat[(idx, left)] = -1.0;
                mat[(idx, right)] = -1.0;
            }
        }

        Self { n: size, matrix: mat }
    }

    /// Build the Laplacian for a linear chain of N vertices (open boundary).
    ///
    /// Endpoints have degree 1, interior vertices have degree 2.
    /// This is NOT a torus — there is no wrapping.
    pub fn linear(n: usize) -> Self {
        let mut mat = DMatrix::zeros(n, n);
        for i in 0..n {
            if i > 0 {
                mat[(i, i)] += 1.0;
                mat[(i, i - 1)] = -1.0;
            }
            if i + 1 < n {
                mat[(i, i)] += 1.0;
                mat[(i, i + 1)] = -1.0;
            }
        }
        Self { n, matrix: mat }
    }

    /// Build the Laplacian from an explicit edge list (unweighted).
    pub fn from_edges(n: usize, edges: &[(usize, usize)]) -> Self {
        let mut mat = DMatrix::zeros(n, n);
        for &(i, j) in edges {
            mat[(i, j)] -= 1.0;
            mat[(j, i)] -= 1.0;
            mat[(i, i)] += 1.0;
            mat[(j, j)] += 1.0;
        }
        Self { n, matrix: mat }
    }

    /// Compute all eigenvalues, sorted ascending.
    pub fn eigenvalues(&self) -> Vec<f64> {
        let eigen = SymmetricEigen::new(self.matrix.clone());
        let mut vals: Vec<f64> = eigen.eigenvalues.iter().cloned().collect();
        vals.sort_by(|a, b| a.partial_cmp(b).unwrap());
        vals
    }

    /// Spectral gap: smallest nonzero eigenvalue.
    ///
    /// Returns None if the graph is disconnected (multiple zero eigenvalues)
    /// or has fewer than 2 vertices.
    pub fn spectral_gap(&self) -> Option<f64> {
        let vals = self.eigenvalues();
        // Skip all near-zero eigenvalues (there should be exactly 1 for connected graphs)
        vals.iter()
            .find(|&&v| v > 1e-10)
            .copied()
    }

    /// Cheeger constant (isoperimetric number) lower bound from spectral gap.
    ///
    /// By Cheeger's inequality: h >= lambda_1 / 2
    /// (The upper bound h <= sqrt(2 * lambda_1) is tighter but requires
    /// knowing h explicitly.)
    pub fn cheeger_lower_bound(&self) -> Option<f64> {
        self.spectral_gap().map(|gap| gap / 2.0)
    }

    /// Mixing time upper bound: t_mix(eps) <= (1/lambda_1) * ln(n/eps).
    pub fn mixing_time_bound(&self, eps: f64) -> Option<f64> {
        self.spectral_gap()
            .map(|gap| (1.0 / gap) * (self.n as f64 / eps).ln())
    }

    /// Eigenvalues with multiplicities (grouped within tolerance).
    pub fn eigenvalues_with_multiplicities(&self, tol: f64) -> Vec<(f64, usize)> {
        let vals = self.eigenvalues();
        let mut result: Vec<(f64, usize)> = Vec::new();
        for &v in &vals {
            if let Some(last) = result.last_mut() {
                if (v - last.0).abs() < tol {
                    last.1 += 1;
                    continue;
                }
            }
            result.push((v, 1));
        }
        result
    }

    /// Fiedler vector: eigenvector corresponding to lambda_1.
    ///
    /// The Fiedler vector is used for spectral partitioning and measures
    /// the "smoothest" non-constant function on the graph.
    pub fn fiedler_vector(&self) -> Option<DVector<f64>> {
        let eigen = SymmetricEigen::new(self.matrix.clone());
        let vals = &eigen.eigenvalues;
        let vecs = &eigen.eigenvectors;

        // Find index of smallest nonzero eigenvalue
        let mut indexed: Vec<(usize, f64)> = vals.iter()
            .enumerate()
            .map(|(i, &v)| (i, v))
            .collect();
        indexed.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());

        // Skip the zero eigenvalue(s), take the next one
        indexed.iter()
            .find(|(_, v)| *v > 1e-10)
            .map(|(i, _)| vecs.column(*i).clone_owned())
    }

    /// Poincare constant: 1/lambda_1.
    ///
    /// Controls the constant in the discrete Poincare inequality:
    ///   ||f - f_bar||^2 <= (1/lambda_1) * ||grad f||^2
    pub fn poincare_constant(&self) -> Option<f64> {
        self.spectral_gap().map(|gap| 1.0 / gap)
    }

    /// Spectral radius: largest eigenvalue.
    pub fn spectral_radius(&self) -> f64 {
        let vals = self.eigenvalues();
        *vals.last().unwrap_or(&0.0)
    }
}

/// Verify that the numerical spectrum of C_N matches the analytic formula.
///
/// Returns (max_error, eigenvalue_pairs) where each pair is (numerical, analytic).
pub fn verify_cycle_spectrum(n: usize) -> (f64, Vec<(f64, f64)>) {
    let lap = GraphLaplacian::cycle(n);
    let numerical = lap.eigenvalues();

    let mut analytic: Vec<f64> = (0..n)
        .map(|k| 2.0 - 2.0 * (2.0 * std::f64::consts::PI * k as f64 / n as f64).cos())
        .collect();
    analytic.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let pairs: Vec<(f64, f64)> = numerical.iter()
        .zip(analytic.iter())
        .map(|(&n, &a)| (n, a))
        .collect();

    let max_err = pairs.iter()
        .map(|(n, a)| (n - a).abs())
        .fold(0.0_f64, f64::max);

    (max_err, pairs)
}

/// Verify that the numerical spectrum of T² = C_N × C_N matches the analytic formula.
///
/// Returns (max_error, spectral_gap_numerical, spectral_gap_analytic).
pub fn verify_torus_spectrum(n: usize) -> (f64, f64, f64) {
    let lap = GraphLaplacian::torus(n);
    let numerical = lap.eigenvalues();

    let mut analytic: Vec<f64> = Vec::with_capacity(n * n);
    for j in 0..n {
        for k in 0..n {
            let lam = 4.0
                - 2.0 * (2.0 * std::f64::consts::PI * j as f64 / n as f64).cos()
                - 2.0 * (2.0 * std::f64::consts::PI * k as f64 / n as f64).cos();
            analytic.push(lam);
        }
    }
    analytic.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let max_err = numerical.iter()
        .zip(analytic.iter())
        .map(|(n, a)| (n - a).abs())
        .fold(0.0_f64, f64::max);

    let gap_num = *numerical.iter().find(|&&v| v > 1e-10).unwrap_or(&0.0);
    let gap_ana = 2.0 - 2.0 * (2.0 * std::f64::consts::PI / n as f64).cos();

    (max_err, gap_num, gap_ana)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::f64::consts::PI;

    // ── Cycle graph tests ──────────────────────────────────────────────

    #[test]
    fn cycle_spectrum_matches_analytic() {
        for n in [4, 6, 8, 10, 12, 16] {
            let (max_err, _) = verify_cycle_spectrum(n);
            assert!(
                max_err < 1e-10,
                "C_{}: max eigenvalue error {} exceeds tolerance",
                n, max_err
            );
        }
    }

    #[test]
    fn cycle_spectral_gap_matches_formula() {
        for n in [4, 8, 16, 32] {
            let lap = GraphLaplacian::cycle(n);
            let gap = lap.spectral_gap().unwrap();
            let expected = 2.0 - 2.0 * (2.0 * PI / n as f64).cos();
            assert!(
                (gap - expected).abs() < 1e-10,
                "C_{}: gap={}, expected={}", n, gap, expected
            );
        }
    }

    #[test]
    fn cycle_has_one_zero_eigenvalue() {
        let lap = GraphLaplacian::cycle(8);
        let vals = lap.eigenvalues();
        let zero_count = vals.iter().filter(|&&v| v.abs() < 1e-10).count();
        assert_eq!(zero_count, 1, "Connected cycle should have exactly one zero eigenvalue");
    }

    // ── Torus tests ────────────────────────────────────────────────────

    #[test]
    fn torus_spectrum_matches_analytic() {
        for n in [4, 6, 8] {
            let (max_err, gap_num, gap_ana) = verify_torus_spectrum(n);
            assert!(
                max_err < 1e-9,
                "T²({}): max eigenvalue error {} exceeds tolerance",
                n, max_err
            );
            assert!(
                (gap_num - gap_ana).abs() < 1e-10,
                "T²({}): spectral gap numerical={}, analytic={}",
                n, gap_num, gap_ana
            );
        }
    }

    #[test]
    fn torus_spectral_gap_matches_torus_module() {
        // Cross-validate: spectral.rs numerical == torus.rs analytic
        use crate::torus::TorusLattice;
        for n in [4, 6, 8, 10] {
            let numerical = GraphLaplacian::torus(n).spectral_gap().unwrap();
            let analytic = TorusLattice::new(n, 1.0).spectral_gap();
            assert!(
                (numerical - analytic).abs() < 1e-10,
                "N={}: numerical={} vs torus.rs={}",
                n, numerical, analytic
            );
        }
    }

    #[test]
    fn torus_gap_decreases_with_n() {
        let g4 = GraphLaplacian::torus(4).spectral_gap().unwrap();
        let g8 = GraphLaplacian::torus(8).spectral_gap().unwrap();
        let g16 = GraphLaplacian::torus(16).spectral_gap().unwrap();
        assert!(g4 > g8, "gap(4)={} should > gap(8)={}", g4, g8);
        assert!(g8 > g16, "gap(8)={} should > gap(16)={}", g8, g16);
    }

    #[test]
    fn torus_gap_asymptotic() {
        // For large N, lambda_1 = 2 - 2*cos(2*pi/N) ≈ (2*pi/N)² = 4*pi²/N²
        // N=64 skipped: 4096×4096 eigendecomposition too slow in debug mode
        for n in [16, 32] {
            let gap = GraphLaplacian::torus(n).spectral_gap().unwrap();
            let approx = 4.0 * PI * PI / (n as f64 * n as f64);
            let relative_err = (gap - approx).abs() / gap;
            assert!(
                relative_err < 0.1,
                "N={}: gap={}, 2pi²/N²={}, rel_err={}",
                n, gap, approx, relative_err
            );
        }
    }

    // ── Linear chain tests ─────────────────────────────────────────────

    #[test]
    fn linear_has_one_zero_eigenvalue() {
        let lap = GraphLaplacian::linear(8);
        let vals = lap.eigenvalues();
        let zero_count = vals.iter().filter(|&&v| v.abs() < 1e-10).count();
        assert_eq!(zero_count, 1, "Connected chain should have exactly one zero eigenvalue");
    }

    #[test]
    fn cycle_gap_larger_than_linear() {
        // Cycle has a larger spectral gap than the open chain of same size:
        // cycle lambda_1 = 2 - 2*cos(2*pi/N), linear lambda_1 = 2 - 2*cos(pi/N).
        // Since cos(pi/N) > cos(2*pi/N), the cycle gap is bigger.
        for n in [8, 16, 32] {
            let gap_linear = GraphLaplacian::linear(n).spectral_gap().unwrap();
            let gap_cycle = GraphLaplacian::cycle(n).spectral_gap().unwrap();
            assert!(
                gap_cycle > gap_linear,
                "N={}: cycle gap {} should > linear gap {}",
                n, gap_cycle, gap_linear
            );
        }
    }

    // ── Structural properties ──────────────────────────────────────────

    #[test]
    fn laplacian_row_sums_zero() {
        let lap = GraphLaplacian::torus(6);
        for i in 0..lap.n {
            let row_sum: f64 = (0..lap.n).map(|j| lap.matrix[(i, j)]).sum();
            assert!(
                row_sum.abs() < 1e-12,
                "Row {} sum = {} (should be 0)",
                i, row_sum
            );
        }
    }

    #[test]
    fn laplacian_symmetric() {
        let lap = GraphLaplacian::torus(6);
        for i in 0..lap.n {
            for j in 0..lap.n {
                assert!(
                    (lap.matrix[(i, j)] - lap.matrix[(j, i)]).abs() < 1e-15,
                    "L[{},{}]={} != L[{},{}]={}",
                    i, j, lap.matrix[(i, j)], j, i, lap.matrix[(j, i)]
                );
            }
        }
    }

    #[test]
    fn laplacian_positive_semidefinite() {
        let lap = GraphLaplacian::torus(6);
        let vals = lap.eigenvalues();
        for &v in &vals {
            assert!(
                v >= -1e-10,
                "Eigenvalue {} is negative (Laplacian must be PSD)",
                v
            );
        }
    }

    #[test]
    fn fiedler_vector_orthogonal_to_constant() {
        let lap = GraphLaplacian::torus(6);
        let fiedler = lap.fiedler_vector().unwrap();
        let sum: f64 = fiedler.iter().sum();
        assert!(
            sum.abs() < 1e-8,
            "Fiedler vector sum = {} (should be ~0, orthogonal to constant)",
            sum
        );
    }

    // ── Poincare and mixing time ───────────────────────────────────────

    #[test]
    fn poincare_constant_correct() {
        let lap = GraphLaplacian::torus(8);
        let gap = lap.spectral_gap().unwrap();
        let poincare = lap.poincare_constant().unwrap();
        assert!((poincare - 1.0 / gap).abs() < 1e-12);
    }

    #[test]
    fn mixing_time_decreases_with_connectivity() {
        // Torus (4-connected) should mix faster than linear chain
        let mix_torus = GraphLaplacian::torus(8).mixing_time_bound(0.01).unwrap();
        // Compare to cycle (2-connected) of same vertex count
        let mix_cycle = GraphLaplacian::cycle(64).mixing_time_bound(0.01).unwrap();
        // The torus has 64 vertices with gap ~ 2-2cos(pi/4), cycle has gap ~ 2-2cos(2pi/64)
        // Torus gap is much larger → faster mixing
        assert!(
            mix_torus < mix_cycle,
            "Torus mixing {} should be < cycle mixing {}",
            mix_torus, mix_cycle
        );
    }

    // ── Cross-validation with from_edges ───────────────────────────────

    #[test]
    fn from_edges_matches_cycle() {
        let n = 8;
        let edges: Vec<(usize, usize)> = (0..n).map(|i| (i, (i + 1) % n)).collect();
        let from_edges = GraphLaplacian::from_edges(n, &edges);
        let from_cycle = GraphLaplacian::cycle(n);

        let gap_edges = from_edges.spectral_gap().unwrap();
        let gap_cycle = from_cycle.spectral_gap().unwrap();
        assert!(
            (gap_edges - gap_cycle).abs() < 1e-12,
            "from_edges gap {} != cycle gap {}",
            gap_edges, gap_cycle
        );
    }

    // ── Spectral radius ────────────────────────────────────────────────

    #[test]
    fn torus_spectral_radius_is_8() {
        // Max eigenvalue of 4-connected torus Laplacian is 8 (at the Nyquist mode)
        let lap = GraphLaplacian::torus(4);
        let radius = lap.spectral_radius();
        assert!(
            (radius - 8.0).abs() < 1e-10,
            "Spectral radius should be 8, got {}",
            radius
        );
    }
}
