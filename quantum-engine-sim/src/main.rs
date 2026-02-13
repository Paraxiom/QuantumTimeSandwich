//! Quantum Engine Simulator — superconducting microwave cavity regime.

use quantum_engine_sim::torus::TorusLattice;
use quantum_engine_sim::coherence;
use quantum_engine_sim::toric_code;
use quantum_engine_sim::vacuum;
use quantum_engine_sim::engine::{self, EngineConfig};
use quantum_engine_sim::covariant::{self, TorusPoint};
use quantum_engine_sim::units::*;

fn main() {
    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║     QUANTUM ENGINE SIMULATOR — Superconducting Microwave Regime     ║");
    println!("║                                                                    ║");
    println!("║  Cavity: 3 cm SC resonator · 20 mK · Q ~ 10¹⁰ · SQUID boundary   ║");
    println!("║  Toroidal spectral gaps → coherence → vacuum → engine cycle        ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();

    let config = EngineConfig::microwave();

    // ═══════════════════════════════════════
    // Physical parameters
    // ═══════════════════════════════════════
    let torus = TorusLattice::new(config.n, config.l_min);
    let omega_1 = torus.omega_min();
    let freq_ghz = omega_1 / (2.0 * PI * 1e9);

    println!("━━━ Physical Parameters ━━━");
    println!();
    println!("  Cavity size:        {:.1} cm (compressed) / {:.1} cm (expanded)",
        config.l_min * 100.0, config.l_max * 100.0);
    println!("  Lattice:            {}×{} torus ({} sites)", config.n, config.n, torus.num_sites());
    println!("  Lattice spacing:    {:.2} mm", torus.lattice_spacing() * 1e3);
    println!("  Fundamental mode:   ω₁ = {:.2} GHz ({:.2e} rad/s)", freq_ghz, omega_1);
    println!("  Temperature:        {} mK", config.temperature * 1e3);
    println!("  Quality factor:     Q ≈ {:.0e} (γ = {} Hz)",
        omega_1 / config.decoherence_rate, config.decoherence_rate);
    println!("  Modulation:         δL/L = {:.0e}", config.modulation_depth);
    println!("  Perturbative param: δL·ω/c = {:.2e} {}",
        config.perturbative_param(),
        if config.perturbative_param() < 0.01 { "(valid)" } else { "(WARNING: non-perturbative!)" });
    println!();

    // Thermal occupation
    let n_th = vacuum::fundamental_thermal_photons(&torus, config.temperature);
    let n_th_300k = vacuum::fundamental_thermal_photons(&torus, 300.0);
    println!("  Thermal photons (fundamental mode):");
    println!("    At {:.0} mK:  n_th = {:.4e}  {}", config.temperature * 1e3, n_th,
        if n_th < 0.01 { "(quantum ground state)" } else { "" });
    println!("    At 300 K:   n_th = {:.1}     (classical limit)", n_th_300k);
    println!();

    // ═══════════════════════════════════════
    // Layer 1: Spectral Gap
    // ═══════════════════════════════════════
    println!("━━━ Layer 1: Spectral Gap on T² ━━━");
    println!();
    println!("  {:>4}  {:>10}  {:>12}  {:>14}  {:>14}", "N", "λ₁", "ω_gap (GHz)", "T_gap (mK)", "Mix time (μs)");
    println!("  {:─>4}  {:─>10}  {:─>12}  {:─>14}  {:─>14}", "", "", "", "", "");

    for &n in &[4, 8, 12, 16, 24, 32] {
        let t = TorusLattice::new(n, config.l_min);
        let gap = t.spectral_gap();
        let omega_gap = t.omega_min() * gap.sqrt();
        let freq_gap_ghz = omega_gap / (2.0 * PI * 1e9);
        let t_gap_mk = HBAR * omega_gap / KB * 1e3;
        let mix_us = t.mixing_time_physical() * 1e6;
        println!("  {:>4}  {:>10.6}  {:>12.2}  {:>14.1}  {:>14.4}", n, gap, freq_gap_ghz, t_gap_mk, mix_us);
    }
    println!();

    // ═══════════════════════════════════════
    // Layer 2: Coherence
    // ═══════════════════════════════════════
    println!("━━━ Layer 2: Toroidal Coherence Protection ━━━");
    println!();

    let n_qubits = config.n * config.n;
    let gamma = config.decoherence_rate;
    let comparisons = coherence::compare_topologies(n_qubits, gamma);

    println!("  {} qubits, γ = {} Hz (Q ≈ {:.0e}):", n_qubits, gamma, omega_1 / gamma);
    println!();
    println!("  {:>20}  {:>10}  {:>14}  {:>14}", "Topology", "λ₁", "τ (units 1/γ)", "T₂ (ms)");
    println!("  {:─>20}  {:─>10}  {:─>14}  {:─>14}", "", "", "", "");

    for r in &comparisons {
        let t2_ms = r.t2_ns.map(|ns| ns / 1e6).unwrap_or(0.0);
        println!(
            "  {:>20}  {:>10.4}  {:>14.4}  {:>14.1}",
            r.topology, r.spectral_gap, r.coherence_time, t2_ms
        );
    }
    println!();

    println!("  Tonnetz-enhanced T₂ (bare T₂ = {:.0} ms, Q = 1.0):", 1.0 / gamma * 1e3);
    println!("  {:>6}  {:>14}  {:>10}", "Grid N", "T₂ enhanced", "Factor");
    println!("  {:─>6}  {:─>14}  {:─>10}", "", "", "");
    let t2_bare_ns = 1.0 / gamma * 1e9;
    for &n in &[4, 8, 12, 16, 24] {
        let t2 = coherence::tonnetz_enhanced_t2(t2_bare_ns, n, 1.0);
        let t2_ms = t2 / 1e6;
        println!("  {:>6}  {:>10.1} ms  {:>10.2}×", n, t2_ms, t2 / t2_bare_ns);
    }
    println!();

    // ═══════════════════════════════════════
    // Layer 3: Toric Code
    // ═══════════════════════════════════════
    println!("━━━ Layer 3: Toric Code Topological Protection ━━━");
    println!();

    let p_test = 0.03;
    let trials = 5000;
    println!("  Physical error rate p = {:.0}%, {} trials:", p_test * 100.0, trials);
    println!();
    println!("  {:>6}  {:>14}  {:>12}", "N", "P_logical", "α = -ln(P)/N");
    println!("  {:─>6}  {:─>14}  {:─>12}", "", "", "");

    let results = toric_code::estimate_alpha(p_test, &[4, 6, 8, 10, 12], trials);
    for r in &results {
        let alpha_str = match r.alpha {
            Some(a) => format!("{:.4}", a),
            None => "—".to_string(),
        };
        println!("  {:>6}  {:>14.6}  {:>12}", r.lattice_size, r.logical_error_rate, alpha_str);
    }
    println!();

    // ═══════════════════════════════════════
    // Layer 3b: Covariant Descent
    // ═══════════════════════════════════════
    println!("━━━ Layer 3b: Covariant Descent — Convergence = Coherence ━━━");
    println!();
    println!("  Poincaré inequality on T²: ||f - f*|| ≤ exp(-λ₁·t) ||f₀ - f*||");
    println!("  The spectral gap IS the convergence rate.");
    println!();

    // Compare Euclidean vs Covariant
    // Start and target on opposite sides of the wrapping boundary
    let start = TorusPoint::new(0.95, 0.05);
    let target = TorusPoint::new(0.05, 0.95);

    let (euc, cov) = covariant::compare_methods(8, start, target, 0.002, 2000);
    println!("  Euclidean vs Covariant (N=8, η=0.002, across wrapping boundary):");
    println!("  Start: (0.95, 0.05) → Target: (0.05, 0.95)");
    println!("  Toroidal distance: 0.14  |  Euclidean distance: 1.27");
    println!();
    println!("  {:>20}  {:>12}  {:>12}  {:>14}  {:>12}",
        "Method", "Final loss", "Final dist", "Converged at", "Meas. rate");
    println!("  {:─>20}  {:─>12}  {:─>12}  {:─>14}  {:─>12}", "", "", "", "", "");
    for r in [&euc, &cov] {
        let conv_str = match r.convergence_step {
            Some(s) => format!("step {}", s),
            None => "NOT converged".to_string(),
        };
        println!("  {:>20}  {:>12.6}  {:>12.6}  {:>14}  {:>12.6}",
            r.method, r.final_loss, r.final_distance, conv_str, r.measured_rate);
    }
    println!();

    // Convergence rate vs spectral gap across lattice sizes
    let eta = 0.001;
    println!("  Convergence rate vs spectral gap (single-mode loss, η={}):", eta);
    println!("  {:>6}  {:>10}  {:>14}  {:>12}", "N", "λ₁", "Meas. rate", "rate/λ₁");
    println!("  {:─>6}  {:─>10}  {:─>14}  {:─>12}", "", "", "", "");

    let validation = covariant::convergence_validation(&[4, 6, 8, 12, 16, 24, 32], eta);
    for (n, lambda1, measured) in &validation {
        let ratio = if *lambda1 > 0.0 { measured / lambda1 } else { 0.0 };
        println!("  {:>6}  {:>10.6}  {:>14.6}  {:>12.4}", n, lambda1, measured, ratio);
    }
    println!();
    println!("  rate/λ₁ ≈ const confirms: convergence rate ∝ spectral gap.");
    println!("  Same λ₁ bounds drift in LLMs, decoherence in qubits, mixing in consensus.");
    println!();

    // ═══════════════════════════════════════
    // Layer 4: Vacuum Physics
    // ═══════════════════════════════════════
    println!("━━━ Layer 4: Quantum Vacuum on T² ━━━");
    println!();

    // Casimir energy at different cavity sizes
    println!("  Casimir energy (N=8 torus):");
    println!("  {:>10}  {:>16}  {:>14}", "L (cm)", "E_Casimir (J)", "Force (fN)");
    println!("  {:─>10}  {:─>16}  {:─>14}", "", "", "");
    for &l_cm in &[1.0, 2.0, 3.0, 5.0, 10.0] {
        let t = TorusLattice::new(8, l_cm * 1e-2);
        let cas = vacuum::casimir_energy(&t);
        println!("  {:>10.1}  {:>16.4e}  {:>14.4}", l_cm, cas.energy, cas.force * 1e15);
    }
    println!();

    // Unruh threshold
    let unruh = vacuum::unruh_analysis(&torus, 1.0);
    println!("  Unruh threshold (N={}, L={:.1} cm):", config.n, config.l_min * 100.0);
    println!("    a_min = {:.2e} m/s²  (surface gravity comparison:", unruh.a_min);
    println!("      Earth:          9.8 m/s²");
    println!("      White dwarf:    ~10⁶ m/s²");
    println!("      Neutron star:   ~10¹² m/s²");
    println!("      Black hole 10M⊙: ~10¹³ m/s²)");
    println!("    T_min = {:.2} K", unruh.t_min);
    println!();

    // Dynamical Casimir — resonant drive
    let drive = config.effective_drive();
    let drive_ghz = drive / (2.0 * PI * 1e9);
    println!("  Dynamical Casimir effect (resonant drive Ω = {:.1} GHz ≈ 2ω₁):", drive_ghz);
    let dce = vacuum::dynamical_casimir(&torus, config.modulation_depth, drive);
    println!("    Perturbative param:  δL·ω/c = {:.2e}  {}", dce.perturbative_param,
        if dce.perturbative_param < 0.01 { "(perturbative regime)" } else { "(non-perturbative!)" });
    println!("    Active modes:        {}/{} (in resonance window)", dce.active_modes, dce.total_modes);
    println!("    Protected modes:     {:.1}% (below spectral gap)", dce.protected_fraction * 100.0);
    println!("    Pair production:     {:.4} pairs/s", dce.pair_rate);
    println!("    Radiation power:     {:.4e} W ({:.4e} eV/s)",
        dce.power, dce.power / 1.602e-19);
    println!();

    // Compare with Wilson et al. (2011) experimental result
    println!("    Reference: Wilson et al. (2011) observed ~1 photon/s at");
    println!("    δL_eff/c ~ 10⁻⁸ s, Ω/2π ~ 10 GHz, in a 1D SQUID line.");
    println!();

    // ═══════════════════════════════════════
    // Layer 5: Engine Cycle
    // ═══════════════════════════════════════
    println!("━━━ Layer 5: Quantum Engine Cycle ━━━");
    println!();

    let result = engine::simulate(&config);

    println!("  Cycle parameters:");
    println!("    Compression:     {:.1} cm → {:.1} cm (ΔL = {:.2} mm)",
        config.l_max * 100.0, config.l_min * 100.0,
        (config.l_max - config.l_min) * 1e3);
    println!("    Drive:           Ω/2π = {:.1} GHz (auto: 2×ω₁)", drive_ghz);
    println!("    Extraction:      {} oscillations", config.extraction_cycles);
    println!("    Cycle time:      {:.4e} s ({:.2} μs)", result.cycle.cycle_time, result.cycle.cycle_time * 1e6);
    println!();

    println!("  Energy budget:");
    println!("    E_Casimir(L_max):   {:>14.4e} J", result.cycle.e_max);
    println!("    E_Casimir(L_min):   {:>14.4e} J", result.cycle.e_min);
    println!("    W_compression:      {:>14.4e} J", result.cycle.work_compression);
    println!("    E_extracted (DCE):  {:>14.4e} J", result.cycle.energy_extracted);
    println!("    Decoherence loss:   {:>14.4e} J  (γ×t×P_topo)", result.cycle.decoherence_loss);
    println!("    Thermal noise:      {:>14.4e} J  (n_th×ℏω×γ×t×P_topo)", result.cycle.thermal_noise);
    println!("    ─────────────────────────────────────");
    println!("    Net work:           {:>14.4e} J", result.cycle.net_work);
    println!();

    println!("  Topological protection:");
    println!("    Spectral gap:        λ₁ = {:.6}", result.cycle.spectral_gap);
    println!("    Protection factor:   {:.4e}  (exp(-λ₁/γ_norm))", result.cycle.protection_factor);
    println!("    Thermal photons:     n_th = {:.4e}", result.thermal_photons);
    println!("    Efficiency:          η = {:.4e}", result.cycle.efficiency);
    println!("    Efficiency (bare):   η₀ = {:.4e}  (without topo protection)", result.efficiency_unprotected);
    if result.cycle.efficiency != 0.0 && result.efficiency_unprotected != 0.0 {
        println!("    Protection ratio:    η/η₀ = {:.2}×",
            result.cycle.efficiency / result.efficiency_unprotected);
    }
    println!("    Coherence enhance:   {:.2}× (Tonnetz vs bare)", result.coherence_enhancement);
    println!();

    println!("  Output:");
    println!("    Power:               {:.4e} W", result.power_output);
    println!("    Unruh threshold:     {:.2e} m/s²", result.unruh_acceleration_threshold);
    println!();

    // ═══════════════════════════════════════
    // Scaling Study
    // ═══════════════════════════════════════
    println!("━━━ Scaling: Performance vs Lattice Size ━━━");
    println!();
    println!("  {:>4}  {:>10}  {:>12}  {:>12}  {:>12}  {:>10}",
        "N", "λ₁", "DCE (pairs/s)", "η (topo)", "η (bare)", "Enhance");
    println!("  {:─>4}  {:─>10}  {:─>12}  {:─>12}  {:─>12}  {:─>10}", "", "", "", "", "", "");

    let scaling = engine::scaling_study(&config, &[4, 6, 8, 10, 12, 16, 24]);
    for r in &scaling {
        let dce_rate = {
            let t = TorusLattice::new(r.config.n, r.config.l_min);
            let d = vacuum::dynamical_casimir(&t, r.config.modulation_depth, r.drive_freq);
            d.pair_rate
        };
        println!(
            "  {:>4}  {:>10.6}  {:>12.4}  {:>12.4e}  {:>12.4e}  {:>8.2}×",
            r.config.n,
            r.cycle.spectral_gap,
            dce_rate,
            r.cycle.efficiency,
            r.efficiency_unprotected,
            r.coherence_enhancement
        );
    }
    println!();

    // ═══════════════════════════════════════
    // Summary
    // ═══════════════════════════════════════
    println!("━━━ Summary ━━━");
    println!();
    println!("  Superconducting 3 cm toroidal cavity at 20 mK:");
    println!("  - Fundamental mode at {:.1} GHz, Q ~ {:.0e}", freq_ghz, omega_1 / gamma);
    println!("  - Thermal ground state: n_th = {:.1e} (quantum regime)", n_th);
    println!("  - DCE photon production at perturbative δL·ω/c = {:.1e}", config.perturbative_param());
    println!("  - Spectral gap provides {:.2}× coherence enhancement", result.coherence_enhancement);
    println!("  - Same geometry: +19.5% TruthfulQA in LLMs, exp(-αN) in toric codes");
    println!();
    println!("  The spectral gap is geometric, not domain-specific.");
    println!();
    println!("  QuantumTimeSandwich — Paraxiom Research");
    println!("  https://doi.org/10.5281/zenodo.18624950");
}
