//! Bridge from physical T₂ to logical error rate via the toric code.
//!
//! Converts T₂ coherence time to a physical error probability, then runs
//! Monte Carlo toric code simulations to determine the logical error rate.

use toric_code_sim::prelude::*;

/// Default gate time for CNT system (ns).
pub const DEFAULT_GATE_TIME_NS: f64 = 100.0;

/// Snapshot of a single toric code trial for visualization.
#[derive(Clone, Debug)]
pub struct LatticeSnapshot {
    pub n: usize,
    /// X errors on each edge (length = 2*n*n).
    pub x_errors: Vec<bool>,
    /// Z errors on each edge (length = 2*n*n).
    pub z_errors: Vec<bool>,
    /// Vertex syndrome locations (e-particles).
    pub e_particles: Vec<(usize, usize)>,
    /// Plaquette syndrome locations (m-particles).
    pub m_particles: Vec<(usize, usize)>,
}

/// Chart data for threshold curves.
#[derive(Clone, Debug)]
pub struct ChartData {
    /// (p, logical_error_rate) per lattice size.
    pub curves: Vec<ThresholdCurve>,
    /// Current operating point p.
    pub operating_p: f64,
}

#[derive(Clone, Debug)]
pub struct ThresholdCurve {
    pub n: usize,
    pub points: Vec<(f64, f64)>,
}

/// Convert T₂ (ns) to physical error probability.
pub fn t2_to_p(t2_ns: f64, gate_time_ns: f64) -> f64 {
    if t2_ns <= 0.0 {
        return 1.0;
    }
    (gate_time_ns / t2_ns).min(0.5)
}

/// Run a single trial and capture a snapshot for visualization.
pub fn capture_snapshot(n: usize, p: f64) -> LatticeSnapshot {
    let mut lattice = ToricLattice::new(n);
    let mut rng = rand::thread_rng();
    apply_random_errors(&mut lattice, p, &mut rng);

    let syndrome = Syndrome::measure(&lattice);

    LatticeSnapshot {
        n,
        x_errors: lattice.x_errors().to_vec(),
        z_errors: lattice.z_errors().to_vec(),
        e_particles: syndrome.e_particles(),
        m_particles: syndrome.m_particles(),
    }
}

/// Run MC experiment at a single (n, p) point.
pub fn run_mc(n: usize, p: f64, trials: usize) -> SimResult {
    run_experiment(&SimConfig {
        n,
        p_error: p,
        trials,
    })
}

/// Recompute syndromes from a snapshot's error arrays (for interactive edits).
///
/// Returns (e_particles, m_particles) where:
/// - e-particle at vertex (r,c) if Z-parity of 4 adjacent edges is odd
/// - m-particle at plaquette (r,c) if X-parity of 4 boundary edges is odd
pub fn recompute_syndromes(snap: &LatticeSnapshot) -> (Vec<(usize, usize)>, Vec<(usize, usize)>) {
    let n = snap.n;
    let mut e_particles = Vec::new();
    let mut m_particles = Vec::new();

    for r in 0..n {
        for c in 0..n {
            // Vertex syndrome: Z errors on 4 adjacent edges
            let z = |idx: usize| snap.z_errors.get(idx).copied().unwrap_or(false);
            let z_count = z(r * n + c) as u8           // h-edge right
                + z(r * n + (c + n - 1) % n) as u8     // h-edge left
                + z(n * n + r * n + c) as u8            // v-edge down
                + z(n * n + ((r + n - 1) % n) * n + c) as u8; // v-edge up
            if z_count % 2 == 1 {
                e_particles.push((r, c));
            }

            // Plaquette syndrome: X errors on 4 boundary edges
            let x = |idx: usize| snap.x_errors.get(idx).copied().unwrap_or(false);
            let x_count = x(r * n + c) as u8           // h-edge top
                + x(((r + 1) % n) * n + c) as u8       // h-edge bottom
                + x(n * n + r * n + c) as u8            // v-edge left
                + x(n * n + r * n + (c + 1) % n) as u8; // v-edge right
            if x_count % 2 == 1 {
                m_particles.push((r, c));
            }
        }
    }

    (e_particles, m_particles)
}

/// Quick single-size sweep for responsive UI.
pub fn quick_sweep(n: usize, p_operating: f64, trials: usize) -> ChartData {
    let rates: Vec<f64> = (1..=20).map(|i| i as f64 * 0.01).collect();
    let results = threshold_sweep(n, &rates, trials);
    let curve = ThresholdCurve {
        n,
        points: results
            .iter()
            .map(|r| (r.p_error, r.logical_error_rate))
            .collect(),
    };

    ChartData {
        curves: vec![curve],
        operating_p: p_operating,
    }
}
