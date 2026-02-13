//! Monte Carlo drift simulation for toroidal logit bias hallucination reduction.
//!
//! Demonstrates how the same spectral gap λ₁ = 2 - 2cos(2π/N) that protects
//! qubits and stabilizes vacuum states also suppresses semantic drift in LLMs.
//! Random walks on T² with/without toroidal mask constraints show how the mask
//! prevents long-distance jumps in the latent space.

use rand::distributions::WeightedIndex;
use rand::prelude::*;
use topological_coherence::{sinkhorn_knopp, SparseMask, MaskType, ToroidalMask};

/// Configuration for a drift simulation run.
#[derive(Debug, Clone)]
pub struct DriftConfig {
    /// Tonnetz grid size (slider 4–24).
    pub grid_n: usize,
    /// Random walk length (100–5000).
    pub num_steps: usize,
    /// Mask type: Hard/Soft/Hybrid.
    pub mask_type: MaskType,
    /// Locality radius (1.0–8.0).
    pub radius: f32,
    /// Decay rate (0.1–2.0).
    pub alpha: f32,
    /// Distance > threshold counts as drift (1–8).
    pub drift_threshold: usize,
}

impl Default for DriftConfig {
    fn default() -> Self {
        Self {
            grid_n: 12,
            num_steps: 1000,
            mask_type: MaskType::Hybrid,
            radius: 2.0,
            alpha: 0.5,
            drift_threshold: 3,
        }
    }
}

/// Results from a drift Monte Carlo run.
#[derive(Debug, Clone)]
pub struct DriftResult {
    pub toroidal_drift_rate: f32,
    pub baseline_drift_rate: f32,
    pub random_drift_rate: f32,
    /// Normalized [0,1)² positions for visualization (max 200 points).
    pub toroidal_path: Vec<(f32, f32)>,
    pub baseline_path: Vec<(f32, f32)>,
    pub spectral_gap: f32,
    /// baseline / toroidal drift rate.
    pub reduction_factor: f32,
}

/// N×N mask values from a reference position, for heatmap display.
#[derive(Debug, Clone)]
pub struct MaskHeatmap {
    pub grid_n: usize,
    /// N×N grid of mask values (row-major).
    pub values: Vec<Vec<f32>>,
    pub ref_pos: (usize, usize),
}

/// Hardcoded TruthfulQA benchmark entry from the published paper.
#[derive(Debug, Clone)]
pub struct BenchmarkEntry {
    pub model: &'static str,
    pub baseline: f32,
    pub toroidal: f32,
    pub delta_pp: f32,
}

// ─── New result types for advanced simulations ─────────────────────────────

/// Sinkhorn convergence data: error per iteration.
#[derive(Debug, Clone)]
pub struct SinkhornConvergence {
    pub points: Vec<[f64; 2]>,
    pub final_error: f32,
    pub converged_at: usize,
}

/// Multi-scale drift comparison across grid sizes.
#[derive(Debug, Clone)]
pub struct MultiScaleEntry {
    pub scale: usize,
    pub toroidal_rate: f32,
    pub baseline_rate: f32,
    pub reduction: f32,
    pub spectral_gap: f32,
}

/// Sparsity sweep entry for one threshold.
#[derive(Debug, Clone)]
pub struct SparsitySweepEntry {
    pub threshold: f32,
    pub sparsity: f32,
    pub nnz: usize,
    pub memory_bytes: usize,
    pub dense_memory: usize,
}

/// Phase transition entry: drift rate at one radius.
#[derive(Debug, Clone)]
pub struct PhaseTransitionEntry {
    pub radius: f32,
    pub drift_rate: f32,
    pub reduction: f32,
}

/// Adjacency loss entry: separation at one radius.
#[derive(Debug, Clone)]
pub struct AdjacencyEntry {
    pub radius: f32,
    pub loss: f32,
    pub pos_mean_dist: f32,
    pub neg_mean_dist: f32,
}

/// Bundled drift analysis results.
#[derive(Debug, Clone)]
pub struct DriftAnalysisResult {
    pub multi_scale: Vec<MultiScaleEntry>,
    pub phase_transition: Vec<PhaseTransitionEntry>,
    pub adjacency: Vec<AdjacencyEntry>,
}

/// Bundled mask analysis results.
#[derive(Debug, Clone)]
pub struct MaskAnalysisResult {
    pub sinkhorn: SinkhornConvergence,
    pub sparsity: Vec<SparsitySweepEntry>,
}

// ─── Helper: build mask from config ────────────────────────────────────────

fn build_mask(config: &DriftConfig) -> ToroidalMask {
    let n2 = config.grid_n * config.grid_n;
    match config.mask_type {
        MaskType::HardCutoff => ToroidalMask::hard_cutoff(n2, config.radius, config.grid_n),
        MaskType::SoftExponential => ToroidalMask::soft_exponential(n2, config.alpha, config.grid_n),
        MaskType::Hybrid => ToroidalMask::with_grid(n2, config.radius, config.alpha, config.grid_n),
    }
}

/// Compute spectral gap at runtime: λ₁ = 2 - 2cos(2π/N).
pub fn spectral_gap_runtime(n: usize) -> f32 {
    2.0 - 2.0 * (2.0 * std::f32::consts::PI / n as f32).cos()
}

/// Toroidal L1 (Manhattan) distance with wraparound.
pub fn toroidal_distance(a: (usize, usize), b: (usize, usize), n: usize) -> usize {
    let dx = {
        let d = (a.0 as isize - b.0 as isize).unsigned_abs();
        d.min(n - d)
    };
    let dy = {
        let d = (a.1 as isize - b.1 as isize).unsigned_abs();
        d.min(n - d)
    };
    dx + dy
}

/// Run 3 random walks: toroidal-masked, baseline (uniform), and random (linear).
pub fn simulate_drift(config: &DriftConfig) -> DriftResult {
    let n = config.grid_n;
    let n2 = n * n;
    let spectral_gap = spectral_gap_runtime(n);
    let mut rng = rand::thread_rng();

    // Build the toroidal mask for sampling weights
    let mask = build_mask(config);

    let max_path_pts = 200usize;
    let stride = (config.num_steps / max_path_pts).max(1);

    // ── Toroidal walk ──
    let mut toroidal_drifts = 0usize;
    let mut toroidal_path = Vec::with_capacity(max_path_pts);
    let mut pos = rng.gen_range(0..n2);
    toroidal_path.push(idx_to_norm(pos, n));

    for step in 0..config.num_steps {
        // Compute mask weights from current position to all positions
        let weights: Vec<f32> = (0..n2)
            .map(|j| mask.value(pos, j).max(1e-9))
            .collect();
        if let Ok(dist) = WeightedIndex::new(&weights) {
            let next = dist.sample(&mut rng);
            let cur_coords = (pos / n, pos % n);
            let next_coords = (next / n, next % n);
            if toroidal_distance(cur_coords, next_coords, n) > config.drift_threshold {
                toroidal_drifts += 1;
            }
            pos = next;
        }
        if (step + 1) % stride == 0 && toroidal_path.len() < max_path_pts {
            toroidal_path.push(idx_to_norm(pos, n));
        }
    }

    // ── Baseline walk (uniform over all positions) ──
    let mut baseline_drifts = 0usize;
    let mut baseline_path = Vec::with_capacity(max_path_pts);
    pos = rng.gen_range(0..n2);
    baseline_path.push(idx_to_norm(pos, n));

    for step in 0..config.num_steps {
        let next = rng.gen_range(0..n2);
        let cur_coords = (pos / n, pos % n);
        let next_coords = (next / n, next % n);
        if toroidal_distance(cur_coords, next_coords, n) > config.drift_threshold {
            baseline_drifts += 1;
        }
        pos = next;
        if (step + 1) % stride == 0 && baseline_path.len() < max_path_pts {
            baseline_path.push(idx_to_norm(pos, n));
        }
    }

    // ── Random walk (linear index, no wrapping — unconstrained latent space) ──
    let mut random_drifts = 0usize;
    pos = rng.gen_range(0..n2);
    for _ in 0..config.num_steps {
        let next = rng.gen_range(0..n2);
        let cur_coords = (pos / n, pos % n);
        let next_coords = (next / n, next % n);
        // Use Euclidean-style distance (no wraparound) for unconstrained space
        let dx = (cur_coords.0 as isize - next_coords.0 as isize).unsigned_abs();
        let dy = (cur_coords.1 as isize - next_coords.1 as isize).unsigned_abs();
        if dx + dy > config.drift_threshold {
            random_drifts += 1;
        }
        pos = next;
    }

    let steps = config.num_steps as f32;
    let toroidal_drift_rate = toroidal_drifts as f32 / steps;
    let baseline_drift_rate = baseline_drifts as f32 / steps;
    let random_drift_rate = random_drifts as f32 / steps;
    let reduction_factor = if toroidal_drift_rate > 1e-9 {
        baseline_drift_rate / toroidal_drift_rate
    } else {
        f32::INFINITY
    };

    DriftResult {
        toroidal_drift_rate,
        baseline_drift_rate,
        random_drift_rate,
        toroidal_path,
        baseline_path,
        spectral_gap,
        reduction_factor,
    }
}

/// Generate mask heatmap: N×N grid of mask values from a reference position.
pub fn generate_mask_heatmap(config: &DriftConfig, ref_pos: (usize, usize)) -> MaskHeatmap {
    let n = config.grid_n;

    let mask = build_mask(config);

    let ref_idx = ref_pos.0 * n + ref_pos.1;
    let values: Vec<Vec<f32>> = (0..n)
        .map(|row| {
            (0..n)
                .map(|col| mask.value(ref_idx, row * n + col))
                .collect()
        })
        .collect();

    MaskHeatmap {
        grid_n: n,
        values,
        ref_pos,
    }
}

/// Spectral decay curves: for each grid size N, generate e^(-λ₁·t) over [0, t_max].
pub fn spectral_decay_curves(
    grid_sizes: &[usize],
    t_max: f32,
    steps: usize,
) -> Vec<(usize, Vec<[f64; 2]>)> {
    grid_sizes
        .iter()
        .map(|&n| {
            let gap = spectral_gap_runtime(n);
            let curve: Vec<[f64; 2]> = (0..=steps)
                .map(|i| {
                    let t = t_max * i as f32 / steps as f32;
                    [t as f64, (-gap * t).exp() as f64]
                })
                .collect();
            (n, curve)
        })
        .collect()
}

/// Hardcoded TruthfulQA benchmark results from the published paper.
pub fn benchmark_data() -> Vec<BenchmarkEntry> {
    vec![
        BenchmarkEntry { model: "Qwen 0.5B", baseline: 16.9, toroidal: 17.1, delta_pp: 0.2 },
        BenchmarkEntry { model: "Qwen 1.5B", baseline: 32.2, toroidal: 32.8, delta_pp: 0.6 },
        BenchmarkEntry { model: "Qwen 7B", baseline: 75.6, toroidal: 77.7, delta_pp: 2.1 },
        BenchmarkEntry { model: "Mistral 7B", baseline: 74.4, toroidal: 77.2, delta_pp: 2.8 },
    ]
}

/// Convert linear index to normalized [0,1)² coordinate.
fn idx_to_norm(idx: usize, n: usize) -> (f32, f32) {
    let row = idx / n;
    let col = idx % n;
    (row as f32 / n as f32, col as f32 / n as f32)
}

// ─── Advanced simulation functions ─────────────────────────────────────────

/// Run bundled drift analysis: multi-scale, phase transition, and adjacency.
pub fn simulate_drift_analysis(config: &DriftConfig) -> DriftAnalysisResult {
    let n = config.grid_n;
    let mut rng = rand::thread_rng();

    // ── 1. Multi-scale: compare drift rates across grid sizes ──
    let multi_scale: Vec<MultiScaleEntry> = [6usize, 12, 24]
        .iter()
        .map(|&scale| {
            let mut cfg = config.clone();
            cfg.grid_n = scale;
            cfg.num_steps = 500;
            let result = simulate_drift(&cfg);
            MultiScaleEntry {
                scale,
                toroidal_rate: result.toroidal_drift_rate,
                baseline_rate: result.baseline_drift_rate,
                reduction: result.reduction_factor,
                spectral_gap: result.spectral_gap,
            }
        })
        .collect();

    // ── 2. Phase transition: sweep radius, measure drift rate ──
    let max_r = n as f32 / 2.0;
    let mut phase_transition = Vec::new();
    let mut r = 1.0f32;
    while r <= max_r {
        let mut cfg = config.clone();
        cfg.radius = r;
        cfg.num_steps = 500;
        let result = simulate_drift(&cfg);
        let reduction = if result.toroidal_drift_rate > 1e-9 {
            result.baseline_drift_rate / result.toroidal_drift_rate
        } else {
            f32::INFINITY
        };
        phase_transition.push(PhaseTransitionEntry {
            radius: r,
            drift_rate: result.toroidal_drift_rate,
            reduction,
        });
        r += 0.5;
    }

    // ── 3. Adjacency loss: separation quality at each radius ──
    let n2 = n * n;
    let mut adjacency = Vec::new();
    let mut r = 1.0f32;
    while r <= max_r {
        let mut cfg = config.clone();
        cfg.radius = r;
        let mask = build_mask(&cfg);

        let num_pairs = 500usize;
        let mut pos_sum = 0.0f32;
        let mut neg_sum = 0.0f32;

        for _ in 0..num_pairs {
            // Positive pair: pick a position, then pick a neighbor within distance 2
            let a = rng.gen_range(0..n2);
            let a_r = a / n;
            let a_c = a % n;
            let offset_r = rng.gen_range(0..=2usize);
            let offset_c = 2 - offset_r;
            let b_r = (a_r + offset_r) % n;
            let b_c = (a_c + offset_c) % n;
            let b = b_r * n + b_c;
            pos_sum += mask.value(a, b);

            // Negative pair: random positions
            let c = rng.gen_range(0..n2);
            let d = rng.gen_range(0..n2);
            neg_sum += mask.value(c, d);
        }

        let pos_mean = pos_sum / num_pairs as f32;
        let neg_mean = neg_sum / num_pairs as f32;
        let loss = pos_mean - 0.5 * neg_mean;

        adjacency.push(AdjacencyEntry {
            radius: r,
            loss,
            pos_mean_dist: pos_mean,
            neg_mean_dist: neg_mean,
        });
        r += 0.5;
    }

    DriftAnalysisResult {
        multi_scale,
        phase_transition,
        adjacency,
    }
}

/// Run bundled mask analysis: Sinkhorn convergence and sparsity sweep.
pub fn simulate_mask_analysis(config: &DriftConfig) -> MaskAnalysisResult {
    let mask = build_mask(config);
    let dense = mask.generate();

    // ── 1. Sinkhorn convergence ──
    let max_iters = 50;
    let mut points = Vec::with_capacity(max_iters);
    let mut converged_at = max_iters;
    let mut final_error = 1.0f32;

    for iter in 1..=max_iters {
        let ds = sinkhorn_knopp(dense.clone(), iter);
        let n = ds.len();
        let mut max_err = 0.0f32;
        for row in &ds {
            let row_sum: f32 = row.iter().sum();
            let err = (row_sum - 1.0).abs();
            if err > max_err {
                max_err = err;
            }
        }
        for j in 0..n {
            let col_sum: f32 = ds.iter().map(|row| row[j]).sum();
            let err = (col_sum - 1.0).abs();
            if err > max_err {
                max_err = err;
            }
        }
        points.push([iter as f64, max_err as f64]);
        if max_err < 0.01 && converged_at == max_iters {
            converged_at = iter;
        }
        final_error = max_err;
    }

    let sinkhorn = SinkhornConvergence {
        points,
        final_error,
        converged_at,
    };

    // ── 2. Sparsity sweep ──
    let seq_len = config.grid_n * config.grid_n;
    let dense_memory = seq_len * seq_len * 4;
    let thresholds = [0.001f32, 0.01, 0.05, 0.1, 0.2, 0.3, 0.5];
    let sparsity: Vec<SparsitySweepEntry> = thresholds
        .iter()
        .map(|&threshold| {
            let sparse = SparseMask::from_dense(&dense, threshold);
            SparsitySweepEntry {
                threshold,
                sparsity: sparse.sparsity(),
                nnz: sparse.nnz(),
                memory_bytes: sparse.memory_bytes(),
                dense_memory,
            }
        })
        .collect();

    MaskAnalysisResult { sinkhorn, sparsity }
}
