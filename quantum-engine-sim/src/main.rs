//! Quantum Engine Simulator — full pipeline demonstration.
//!
//! Runs the unified simulation: torus spectral analysis → coherence →
//! toric code protection → vacuum physics → engine cycle.

use quantum_engine_sim::torus::TorusLattice;
use quantum_engine_sim::coherence;
use quantum_engine_sim::toric_code;
use quantum_engine_sim::vacuum;
use quantum_engine_sim::engine::{self, EngineConfig};

fn main() {
    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║          QUANTUM ENGINE SIMULATOR — QuantumTimeSandwich         ║");
    println!("║                                                                ║");
    println!("║  Toroidal spectral gaps → coherence → vacuum → engine cycle    ║");
    println!("║  Analog gravity: Unruh threshold, Casimir energy, DCE on T²   ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");
    println!();

    // ═══════════════════════════════════════════════════════════
    // Layer 1: Spectral Analysis on T²
    // ═══════════════════════════════════════════════════════════
    println!("━━━ Layer 1: Spectral Gap on T² ━━━");
    println!();
    println!("  {:>4}  {:>12}  {:>16}  {:>14}", "N", "λ₁", "λ₁ (approx)", "Mixing time");
    println!("  {:─>4}  {:─>12}  {:─>16}  {:─>14}", "", "", "", "");

    for &n in &[4, 8, 12, 16, 24, 32] {
        let t = TorusLattice::new(n, 1e-6);
        let gap = t.spectral_gap();
        let approx = 2.0 * std::f64::consts::PI.powi(2) / (n as f64).powi(2);
        let mix = t.mixing_time_lattice();
        println!("  {:>4}  {:>12.6}  {:>12.6} ≈  {:>12.2}", n, gap, approx, mix);
    }
    println!();

    // Spectrum detail for N=8
    let t8 = TorusLattice::new(8, 1e-6);
    let spec = t8.spectrum_with_multiplicities();
    println!("  Full spectrum for N=8 (distinct eigenvalues × multiplicity):");
    print!("  ");
    for (lam, mult) in &spec {
        print!("{:.3}×{} ", lam, mult);
    }
    println!();
    println!();

    // ═══════════════════════════════════════════════════════════
    // Layer 2: Coherence Analysis
    // ═══════════════════════════════════════════════════════════
    println!("━━━ Layer 2: Toroidal Coherence Protection ━━━");
    println!();

    let n_qubits = 64; // 8×8 torus
    let gamma = 1e6; // 1 MHz decoherence
    let comparisons = coherence::compare_topologies(n_qubits, gamma);

    println!("  {} qubits, γ = {:.0e} Hz:", n_qubits, gamma);
    println!();
    println!("  {:>20}  {:>10}  {:>14}  {:>12}", "Topology", "λ₁", "τ (units 1/γ)", "T₂ (ns)");
    println!("  {:─>20}  {:─>10}  {:─>14}  {:─>12}", "", "", "", "");

    for r in &comparisons {
        println!(
            "  {:>20}  {:>10.4}  {:>14.4}  {:>12.1}",
            r.topology,
            r.spectral_gap,
            r.coherence_time,
            r.t2_ns.unwrap_or(0.0)
        );
    }
    println!();

    // Tonnetz enhancement scaling
    println!("  Tonnetz-enhanced T₂ (bare T₂ = 1000 ns, Q = 1.0):");
    println!("  {:>6}  {:>12}  {:>12}", "Grid N", "T₂ enhanced", "Factor");
    println!("  {:─>6}  {:─>12}  {:─>12}", "", "", "");
    for &n in &[4, 8, 12, 16, 24] {
        let t2 = coherence::tonnetz_enhanced_t2(1000.0, n, 1.0);
        println!("  {:>6}  {:>10.1} ns  {:>10.2}×", n, t2, t2 / 1000.0);
    }
    println!();

    // ═══════════════════════════════════════════════════════════
    // Layer 3: Toric Code Error Suppression
    // ═══════════════════════════════════════════════════════════
    println!("━━━ Layer 3: Toric Code Topological Protection ━━━");
    println!();
    println!("  Threshold: p_c ≈ {:.1}% (MWPM decoder)", toric_code::TORIC_CODE_THRESHOLD * 100.0);
    println!();

    let p_test = 0.03;
    let trials = 5000;
    println!("  Physical error rate p = {:.0}%, {} trials per size:", p_test * 100.0, trials);
    println!();
    println!("  {:>6}  {:>14}  {:>10}", "N", "P_logical", "α = -ln(P)/N");
    println!("  {:─>6}  {:─>14}  {:─>10}", "", "", "");

    let results = toric_code::estimate_alpha(p_test, &[4, 6, 8, 10, 12], trials);
    for r in &results {
        let alpha_str = match r.alpha {
            Some(a) => format!("{:.4}", a),
            None => "—".to_string(),
        };
        println!("  {:>6}  {:>14.6}  {:>10}", r.lattice_size, r.logical_error_rate, alpha_str);
    }
    println!();
    println!("  Exponential suppression: P_L ~ exp(-α·N) below threshold.");
    println!();

    // ═══════════════════════════════════════════════════════════
    // Layer 4: Vacuum Physics on T²
    // ═══════════════════════════════════════════════════════════
    println!("━━━ Layer 4: Quantum Vacuum on T² (Analog Gravity) ━━━");
    println!();

    // Casimir energy
    println!("  Casimir energy scaling (N=8 lattice):");
    println!("  {:>10}  {:>16}  {:>14}", "L (μm)", "E_Casimir (J)", "Force (N)");
    println!("  {:─>10}  {:─>16}  {:─>14}", "", "", "");

    for &l_um in &[0.5, 1.0, 2.0, 5.0, 10.0] {
        let t = TorusLattice::new(8, l_um * 1e-6);
        let cas = vacuum::casimir_energy(&t);
        println!("  {:>10.1}  {:>16.4e}  {:>14.4e}", l_um, cas.energy, cas.force);
    }
    println!();

    // Unruh threshold
    println!("  Unruh effect — topological threshold on T² (N=8, L=1μm):");
    let t_unruh = TorusLattice::new(8, 1e-6);
    let unruh_base = vacuum::unruh_analysis(&t_unruh, 1.0);
    println!("  Minimum detectable acceleration: a_min = {:.4e} m/s²", unruh_base.a_min);
    println!("  Corresponding temperature:       T_min = {:.4e} K", unruh_base.t_min);
    println!();

    println!("  {:>12}  {:>12}  {:>10}  {:>12}", "Accel (m/s²)", "T_Unruh (K)", "Detected?", "Suppression");
    println!("  {:─>12}  {:─>12}  {:─>10}  {:─>12}", "", "", "", "");
    for &a in &[1e10, 1e15, 1e18, 1e20, 1e22] {
        let u = vacuum::unruh_analysis(&t_unruh, a);
        println!(
            "  {:>12.2e}  {:>12.4e}  {:>10}  {:>12.6}",
            a,
            u.temperature,
            if u.detectable { "YES" } else { "no" },
            u.suppression
        );
    }
    println!();

    // Dynamical Casimir — optical regime
    // ω_min = 2πc/L ≈ 1.88×10¹⁵ rad/s for L=1μm. Drive must be > 2×ω_min.
    let omega_drive = 6e15; // UV drive
    println!("  Dynamical Casimir effect (N=8, L=1μm, δL/L=1%, Ω={:.0e} rad/s):", omega_drive);
    let dce = vacuum::dynamical_casimir(&t_unruh, 0.01, omega_drive);
    println!("  Active modes:     {}/{}", dce.active_modes, dce.total_modes);
    println!("  Protected modes:  {:.1}% (below spectral gap)", dce.protected_fraction * 100.0);
    println!("  Pair production:  {:.4e} pairs/s", dce.pair_rate);
    println!("  Radiation power:  {:.4e} W", dce.power);
    println!();

    // Dynamical Casimir — microwave regime (cm-scale cavity)
    let t_mw = TorusLattice::new(8, 1e-2); // 1 cm cavity
    let omega_mw = 4e11; // ~400 GHz (sub-THz)
    println!("  Dynamical Casimir effect (N=8, L=1cm, δL/L=1%, Ω={:.0e} rad/s):", omega_mw);
    let dce_mw = vacuum::dynamical_casimir(&t_mw, 0.01, omega_mw);
    println!("  Active modes:     {}/{}", dce_mw.active_modes, dce_mw.total_modes);
    println!("  Protected modes:  {:.1}% (below spectral gap)", dce_mw.protected_fraction * 100.0);
    println!("  Pair production:  {:.4e} pairs/s", dce_mw.pair_rate);
    println!("  Radiation power:  {:.4e} W", dce_mw.power);
    println!();

    // ═══════════════════════════════════════════════════════════
    // Layer 5: Quantum Engine Cycle
    // ═══════════════════════════════════════════════════════════
    println!("━━━ Layer 5: Quantum Engine Cycle ━━━");
    println!();

    let config = EngineConfig::default();
    let result = engine::simulate(&config);

    let actual_drive = if config.drive_frequency > 0.0 {
        config.drive_frequency
    } else {
        config.auto_drive_frequency()
    };
    println!("  Configuration:");
    println!("    Lattice:         {}×{} torus", config.n, config.n);
    println!("    L_max:           {:.1} μm", config.l_max * 1e6);
    println!("    L_min:           {:.1} μm", config.l_min * 1e6);
    println!("    Drive freq:      {:.2e} rad/s (auto-derived from L_min)", actual_drive);
    println!("    Modulation:      {:.1}%", config.modulation_depth * 100.0);
    println!("    Decoherence:     {:.1e} Hz", config.decoherence_rate);
    println!();

    println!("  Cycle Energy Budget:");
    println!("    E(L_max):        {:>12.4e} J", result.cycle.e_max);
    println!("    E(L_min):        {:>12.4e} J", result.cycle.e_min);
    println!("    W_compression:   {:>12.4e} J", result.cycle.work_compression);
    println!("    E_extracted:     {:>12.4e} J  (dynamical Casimir)", result.cycle.energy_extracted);
    println!("    Decoherence:     {:>12.4e} J  (topo-suppressed)", result.cycle.decoherence_loss);
    println!("    Net work:        {:>12.4e} J", result.cycle.net_work);
    println!();

    println!("  Protection:");
    println!("    Spectral gap:           λ₁ = {:.6}", result.cycle.spectral_gap);
    println!("    Decoherence suppression: {:.2e}", result.cycle.protection_factor);
    println!("    Efficiency (protected):  {:.4e}", result.cycle.efficiency);
    println!("    Efficiency (bare):       {:.4e}", result.efficiency_unprotected);
    println!("    Coherence enhancement:   {:.2}×", result.coherence_enhancement);
    println!();

    println!("  Analog Gravity:");
    println!("    Unruh threshold:   {:.4e} m/s²", result.unruh_acceleration_threshold);
    println!("    Power output:      {:.4e} W", result.power_output);
    println!();

    // ═══════════════════════════════════════════════════════════
    // Scaling Study
    // ═══════════════════════════════════════════════════════════
    println!("━━━ Scaling: Engine Performance vs Lattice Size ━━━");
    println!();
    println!("  {:>4}  {:>10}  {:>14}  {:>12}  {:>10}", "N", "λ₁", "Protection", "η (topo)", "η (bare)");
    println!("  {:─>4}  {:─>10}  {:─>14}  {:─>12}  {:─>10}", "", "", "", "", "");

    let scaling = engine::scaling_study(1e-6, 0.5e-6, &[4, 6, 8, 10, 12, 16]);
    for r in &scaling {
        println!(
            "  {:>4}  {:>10.6}  {:>14.4e}  {:>12.4e}  {:>10.4e}",
            r.config.n,
            r.cycle.spectral_gap,
            r.cycle.protection_factor,
            r.cycle.efficiency,
            r.efficiency_unprotected
        );
    }
    println!();

    // ═══════════════════════════════════════════════════════════
    // Summary
    // ═══════════════════════════════════════════════════════════
    println!("━━━ Summary ━━━");
    println!();
    println!("  The toroidal geometry (T²) provides a unified framework:");
    println!("  1. Spectral gap λ₁ bounds mixing/drift (LLMs, consensus, quantum codes)");
    println!("  2. Toric code gives exp(-αN) error suppression below p_c ≈ 10.3%");
    println!("  3. Casimir energy on T² scales as E ~ -1/L² (attractive, size-dependent)");
    println!("  4. Unruh threshold: spectral gap creates minimum detectable acceleration");
    println!("  5. Engine cycle: compress → extract (DCE) → expand, protected by λ₁");
    println!();
    println!("  The spectral gap is geometric, not domain-specific.");
    println!("  Same torus, same math, five applications.");
    println!();
    println!("  QuantumTimeSandwich — Paraxiom Research");
    println!("  https://doi.org/10.5281/zenodo.18624950");
}
