//! Full demonstration of the toric code anyon simulator.
//!
//! Shows:
//! 1. Anyon creation and movement
//! 2. Braiding e around m → phase -1
//! 3. Trivial braid → phase +1
//! 4. Logical operators and anticommutation
//! 5. Error correction threshold sweep

use toric_code_sim::prelude::*;

fn main() {
    println!("╔══════════════════════════════════════════════════════╗");
    println!("║       Kitaev Toric Code — Anyon Braiding Demo       ║");
    println!("║       Pauli Frame Simulation on T²                  ║");
    println!("╚══════════════════════════════════════════════════════╝");
    println!();

    demo_anyon_creation();
    demo_braiding();
    demo_logical_operators();
    demo_threshold_sweep();
}

fn demo_anyon_creation() {
    println!("═══ 1. Anyon Creation and Fusion ═══");
    println!();

    let mut lat = ToricLattice::new(6);
    println!("Created 6×6 toric lattice ({} qubits on edges)", lat.num_edges());

    // Create e-particle pair
    let e_edge = Edge { dir: EdgeDir::Horizontal, row: 2, col: 2 };
    let (e1, e2) = create_e_pair(&mut lat, e_edge);
    let syn = Syndrome::measure(&lat);
    println!(
        "Z error on h-edge(2,2) → e-particles at {:?} and {:?} ({} total)",
        e1, e2, syn.num_e_particles()
    );

    // Create m-particle pair
    let m_edge = Edge { dir: EdgeDir::Vertical, row: 3, col: 4 };
    let (m1, m2) = create_m_pair(&mut lat, m_edge);
    let syn = Syndrome::measure(&lat);
    println!(
        "X error on v-edge(3,4) → m-particles at {:?} and {:?} ({} total)",
        m1, m2, syn.num_m_particles()
    );

    // Fusion rules
    println!();
    println!("Fusion rules:");
    println!("  e × e = {:?}", fuse(AnyonType::E, AnyonType::E));
    println!("  m × m = {:?}", fuse(AnyonType::M, AnyonType::M));
    println!("  e × m = {:?}", fuse(AnyonType::E, AnyonType::M));

    // Demonstrate e×e → vacuum
    let mut lat2 = ToricLattice::new(6);
    let (a, b) = create_e_pair(&mut lat2, e_edge);
    move_e_to(&mut lat2, b, a);
    let syn = Syndrome::measure(&lat2);
    println!(
        "  e×e fusion check: syndromes clean = {} ✓",
        syn.is_clean()
    );
    println!();
}

fn demo_braiding() {
    println!("═══ 2. Braiding Statistics ═══");
    println!();

    // Trivial braid
    let phase = trivial_braid_demo(8);
    println!(
        "Trivial braid (e loop, no m inside): phase = {:+.0}  {}",
        phase,
        if (phase - 1.0).abs() < 1e-10 { "✓" } else { "✗" }
    );

    // Nontrivial braid
    let phase = nontrivial_braid_demo(8);
    println!(
        "Nontrivial braid (e around m):       phase = {:+.0}  {}",
        phase,
        if (phase - (-1.0)).abs() < 1e-10 { "✓" } else { "✗" }
    );

    // Crossing count explanation
    let mut lat = ToricLattice::new(8);
    let m_edge = Edge { dir: EdgeDir::Horizontal, row: 3, col: 3 };
    create_m_pair(&mut lat, m_edge);
    let e_edge = Edge { dir: EdgeDir::Horizontal, row: 2, col: 2 };
    create_e_pair(&mut lat, e_edge);
    let crossings_before = count_crossings(&lat);

    // Braid
    let _phase = braid_e_around_m(&mut lat, (2, 3), (3, 3));
    let crossings_after = count_crossings(&lat);

    println!();
    println!("Pauli frame mechanics:");
    println!("  X∧Z crossings before braid: {}", crossings_before);
    println!("  X∧Z crossings after braid:  {}", crossings_after);
    println!("  Δcrossings mod 2 = {} → phase = (-1)^{} = {:+.0}",
        (crossings_after as isize - crossings_before as isize).unsigned_abs() % 2,
        (crossings_after as isize - crossings_before as isize).unsigned_abs() % 2,
        if (crossings_after as isize - crossings_before as isize).unsigned_abs() % 2 == 1 { -1.0 } else { 1.0 }
    );
    println!("  (XZ = -ZX on same qubit → each overlap flips sign)");
    println!();
}

fn demo_logical_operators() {
    println!("═══ 3. Logical Operators ═══");
    println!();

    let n = 6;

    // Z₁ logical operator (non-contractible horizontal Z loop)
    let mut lat = ToricLattice::new(n);
    apply_logical_z1(&mut lat);
    let syn = Syndrome::measure(&lat);
    println!(
        "Logical Z₁ (horizontal Z loop): syndromes = {}, logical error = {}",
        if syn.is_clean() { "none ✓" } else { "PRESENT ✗" },
        has_logical_z_error(&lat)
    );

    // X₁ logical operator (non-contractible vertical X loop)
    let mut lat = ToricLattice::new(n);
    apply_logical_x1(&mut lat);
    let syn = Syndrome::measure(&lat);
    println!(
        "Logical X₁ (vertical X loop):   syndromes = {}, logical error = {}",
        if syn.is_clean() { "none ✓" } else { "PRESENT ✗" },
        has_logical_x_error(&lat)
    );

    // Anticommutation check
    let anticommutes = verify_logical_anticommutation(n);
    println!(
        "Z₁ and X₁ anticommute (share 1 edge): {} {}",
        anticommutes,
        if anticommutes { "✓" } else { "✗" }
    );
    println!("  → This is what protects the logical qubit!");
    println!();
}

fn demo_threshold_sweep() {
    println!("═══ 4. Error Correction Threshold ═══");
    println!();

    let error_rates = vec![0.01, 0.02, 0.04, 0.06, 0.08, 0.10, 0.12, 0.15, 0.20];
    let sizes = vec![4, 6, 8];
    let trials = 500;

    println!(
        "Greedy decoder threshold sweep ({} trials per point)",
        trials
    );
    println!();

    // Header
    print!("  p_err  ");
    for &n in &sizes {
        print!("  N={:<3} ", n);
    }
    println!();
    print!("  ─────  ");
    for _ in &sizes {
        print!("  ───── ");
    }
    println!();

    let all_results = compare_thresholds(&sizes, &error_rates, trials);

    for (i, &p) in error_rates.iter().enumerate() {
        print!("  {:.3}  ", p);
        for size_results in &all_results {
            let r = &size_results[i];
            print!("  {:.3} ", r.logical_error_rate);
        }
        println!();
    }

    println!();
    println!("Threshold estimates (greedy decoder):");
    for (j, &n) in sizes.iter().enumerate() {
        if let Some(t) = estimate_threshold(&all_results[j]) {
            println!("  N={}: p_threshold ≈ {:.3}", n, t);
        } else {
            println!("  N={}: threshold not found in range", n);
        }
    }

    println!();
    println!("Expected: ~7-8% (greedy), ~10.3% (MWPM optimal)");
    println!();
    println!("════════════════════════════════════════════════════════");
}
