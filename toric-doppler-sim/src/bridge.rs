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
    #[allow(dead_code)]
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

/// Sweep threshold for multiple lattice sizes.
#[allow(dead_code)]
pub fn sweep_threshold(sizes: &[usize], error_rates: &[f64], trials: usize) -> ChartData {
    let curves = sizes
        .iter()
        .map(|&n| {
            let results = threshold_sweep(n, error_rates, trials);
            ThresholdCurve {
                n,
                points: results
                    .iter()
                    .map(|r| (r.p_error, r.logical_error_rate))
                    .collect(),
            }
        })
        .collect();

    ChartData {
        curves,
        operating_p: 0.0,
    }
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
