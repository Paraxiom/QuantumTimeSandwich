//! # Torus Validation Example
//!
//! Demonstrates and validates three torus representations:
//! 1. **ContinuousTorus** — mantissa wraparound via `fract()`
//! 2. **RingBufferTorus** — discrete T² via modular arithmetic
//! 3. **Tonnetz** — the reference implementation from topological-coherence
//!
//! Validates:
//! - Distance equivalence between all three representations
//! - Spectral gap agreement (analytic, numerical, Tonnetz)
//! - Ring buffer neighbor correctness
//!
//! Run: `cargo run --example torus_validation`

use tonnetz_coherence_sim::torus::{
    ContinuousTorus, RingBufferTorus,
    validate_distance_equivalence,
    validate_continuous_discrete_equivalence,
    validate_spectral_gap,
};
use topological_coherence::Tonnetz;

fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║           T² TORUS VALIDATION — Three Representations      ║");
    println!("║                                                            ║");
    println!("║  ContinuousTorus  (fract())  ↔  RingBufferTorus  ↔  Tonnetz  ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!();

    // ── Part 1: Continuous Torus via Mantissa ────────────────────────────

    println!("━━━ Part 1: Continuous Torus (mantissa wraparound) ━━━");
    println!();

    let test_points = [
        (3.7, 5.2),
        (-0.3, -1.8),
        (0.0, 0.0),
        (1.0, 1.0),
        (100.123, -42.876),
    ];

    println!("  {:>12}  {:>12}  →  {:>8}  {:>8}", "input x", "input y", "θ", "φ");
    println!("  {:─>12}  {:─>12}     {:─>8}  {:─>8}", "", "", "", "");
    for (x, y) in &test_points {
        let p = ContinuousTorus::new(*x, *y);
        println!("  {:>12.3}  {:>12.3}  →  {:>8.5}  {:>8.5}", x, y, p.theta, p.phi);
    }
    println!();

    // Demonstrate wraparound distance
    println!("  Distance wraparound:");
    let a = ContinuousTorus::new(0.9, 0.0);
    let b = ContinuousTorus::new(0.1, 0.0);
    let d = ContinuousTorus::distance(&a, &b);
    println!("    d(0.9, 0.1) on S¹ = {:.3}  (wraps, not 0.8)", d);

    let a2 = ContinuousTorus::new(0.0, 0.0);
    let b2 = ContinuousTorus::new(0.5, 0.5);
    let d2 = ContinuousTorus::distance(&a2, &b2);
    println!("    max L1 distance on T² = {:.3}  (at antipodal point)", d2);
    println!();

    // ── Part 2: Ring Buffer ↔ Tonnetz Distance Equivalence ──────────────

    println!("━━━ Part 2: Distance Equivalence (Ring Buffer ↔ Tonnetz) ━━━");
    println!();

    let grids = [
        ("4×4", validate_eq_4()),
        ("6×6", validate_eq_6()),
        ("8×8", validate_eq_8()),
        ("12×12", validate_eq_12()),
    ];

    println!("  {:>8}  {:>12}  {:>8}", "Grid", "Pairs Checked", "Result");
    println!("  {:─>8}  {:─>12}  {:─>8}", "", "", "");
    for (label, result) in &grids {
        let n: usize = label.split('×').next().unwrap().parse().unwrap();
        let pairs = n * n * n * n;
        let status = if result.is_ok() { "PASS" } else { "FAIL" };
        println!("  {:>8}  {:>12}  {:>8}", label, pairs, status);
    }
    println!();

    // ── Part 3: Continuous ↔ Discrete Distance Equivalence ──────────────

    println!("━━━ Part 3: Continuous ↔ Discrete Equivalence ━━━");
    println!();

    let cont_grids = [
        ("4×4", validate_cont_4()),
        ("8×8", validate_cont_8()),
        ("12×12", validate_cont_12()),
    ];

    println!("  {:>8}  {:>8}", "Grid", "Result");
    println!("  {:─>8}  {:─>8}", "", "");
    for (label, result) in &cont_grids {
        let status = if result.is_ok() { "PASS" } else { "FAIL" };
        println!("  {:>8}  {:>8}", label, status);
    }
    println!();

    // Show a sample of distances for 4×4 grid
    println!("  Sample distances (4×4 grid, row=0 col=0 to all):");
    println!("  {:>6}  {:>6}  {:>10}  {:>10}  {:>12}", "row", "col", "RingBuffer", "Tonnetz", "Continuous×N");
    println!("  {:─>6}  {:─>6}  {:─>10}  {:─>10}  {:─>12}", "", "", "", "", "");
    for r in 0..4 {
        for c in 0..4 {
            let ring_d = RingBufferTorus::<4>::distance((0, 0), (r, c));
            let tonnetz_d = Tonnetz::<4>::distance((0, 0), (r, c));
            let a = ContinuousTorus::from_discrete(0, 0, 4);
            let b = ContinuousTorus::from_discrete(r, c, 4);
            let cont_d = ContinuousTorus::distance(&a, &b) * 4.0;
            println!(
                "  {:>6}  {:>6}  {:>10}  {:>10}  {:>12.6}",
                r, c, ring_d, tonnetz_d, cont_d
            );
        }
    }
    println!();

    // ── Part 4: Spectral Gap Validation ─────────────────────────────────

    println!("━━━ Part 4: Spectral Gap Validation ━━━");
    println!();
    println!("  {:>6}  {:>14}  {:>14}  {:>14}  {:>8}",
             "N", "Analytic", "Numerical", "Tonnetz(f32)", "Match");
    println!("  {:─>6}  {:─>14}  {:─>14}  {:─>14}  {:─>8}", "", "", "", "", "");

    print_spectral_row::<4>();
    print_spectral_row::<6>();
    print_spectral_row::<8>();
    print_spectral_row::<12>();
    print_spectral_row::<16>();
    print_spectral_row::<24>();
    println!();

    let gap_results = [
        ("4×4", validate_spectral_gap::<4>()),
        ("8×8", validate_spectral_gap::<8>()),
        ("12×12", validate_spectral_gap::<12>()),
    ];
    for (label, result) in &gap_results {
        match result {
            Ok(()) => println!("  Spectral gap validation {}: PASS", label),
            Err(e) => println!("  Spectral gap validation {}: FAIL — {}", label, e),
        }
    }
    println!();

    // ── Part 5: Ring Buffer Neighbor Verification ───────────────────────

    println!("━━━ Part 5: Ring Buffer Neighbors (4×4 grid) ━━━");
    println!();
    println!("  {:>10}  {:>30}", "Position", "Neighbors [up, down, left, right]");
    println!("  {:─>10}  {:─>30}", "", "");

    let test_positions = [(0, 0), (0, 3), (3, 0), (3, 3), (1, 2)];
    for (r, c) in &test_positions {
        let nbrs = RingBufferTorus::<4>::neighbors(*r, *c);
        println!(
            "  ({:>1},{:>1})       [{:?}, {:?}, {:?}, {:?}]",
            r, c, nbrs[0], nbrs[1], nbrs[2], nbrs[3]
        );
    }
    println!();

    // ── Summary ─────────────────────────────────────────────────────────

    let all_pass = grids.iter().all(|(_, r)| r.is_ok())
        && cont_grids.iter().all(|(_, r)| r.is_ok())
        && gap_results.iter().all(|(_, r)| r.is_ok());

    println!("╔══════════════════════════════════════════════════════════════╗");
    if all_pass {
        println!("║  ALL VALIDATIONS PASSED                                    ║");
        println!("║                                                            ║");
        println!("║  fract() implements S¹ = R/Z                               ║");
        println!("║  (fract(), fract()) implements T² = S¹ x S¹               ║");
        println!("║  i % N implements discrete S¹ = Z/NZ                       ║");
        println!("║  RingBufferTorus<N> = Tonnetz<N> (verified for all pairs)  ║");
        println!("║  Spectral gaps match across all representations            ║");
    } else {
        println!("║  SOME VALIDATIONS FAILED — see output above                ║");
    }
    println!("╚══════════════════════════════════════════════════════════════╝");
}

// Helper functions to call generic validate functions with specific N values

fn validate_eq_4() -> Result<(), String> { validate_distance_equivalence::<4>() }
fn validate_eq_6() -> Result<(), String> { validate_distance_equivalence::<6>() }
fn validate_eq_8() -> Result<(), String> { validate_distance_equivalence::<8>() }
fn validate_eq_12() -> Result<(), String> { validate_distance_equivalence::<12>() }

fn validate_cont_4() -> Result<(), String> { validate_continuous_discrete_equivalence::<4>() }
fn validate_cont_8() -> Result<(), String> { validate_continuous_discrete_equivalence::<8>() }
fn validate_cont_12() -> Result<(), String> { validate_continuous_discrete_equivalence::<12>() }

fn print_spectral_row<const N: usize>() {
    let analytic = RingBufferTorus::<N>::spectral_gap_analytic();
    let numerical = RingBufferTorus::<N>::spectral_gap_numerical();
    let tonnetz = Tonnetz::<N>::spectral_gap() as f64;
    let matches = (analytic - tonnetz).abs() < 1e-5 && (numerical - analytic).abs() < 1e-10;
    println!(
        "  {:>6}  {:>14.10}  {:>14.10}  {:>14.10}  {:>8}",
        N, analytic, numerical, tonnetz,
        if matches { "YES" } else { "NO" }
    );
}
