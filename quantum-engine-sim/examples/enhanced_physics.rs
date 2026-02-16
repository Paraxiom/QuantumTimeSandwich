//! Enhanced Physics Suite — Lindblad, noise models, Wilson cross-check, large-scale toric code.
//!
//! Run: cargo run --example enhanced_physics --release

use quantum_engine_sim::torus::TorusLattice;
use quantum_engine_sim::lindblad;
use quantum_engine_sim::noise::{self, NoiseParams};
use quantum_engine_sim::wilson_comparison;
use quantum_engine_sim::toric_code;
use quantum_engine_sim::units::PI;

fn main() {
    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║    ENHANCED PHYSICS SUITE — Lindblad · Noise · Wilson · Scaling    ║");
    println!("║                                                                    ║");
    println!("║  Paraxiom Research — Quantum Engine Simulator v0.2                 ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();

    // ═══════════════════════════════════════
    // 1. Wilson et al. (2011) cross-validation
    // ═══════════════════════════════════════
    let comp = wilson_comparison::compare_with_wilson();
    wilson_comparison::print_comparison(&comp);

    // Modulation sweep
    let torus = TorusLattice::new(8, 3e-2);
    let depths: Vec<f64> = (1..=8).map(|i| 10f64.powi(-(9 - i))).collect();
    let sweep = wilson_comparison::modulation_sweep(&torus, &depths);
    println!("  Modulation sweep (3 cm T², N=8):");
    println!("  {:>10}  {:>12}  {:>12}  {:>10}", "δL/L", "Γ (pairs/s)", "δL·ω/c", "Regime");
    println!("  {:─>10}  {:─>12}  {:─>12}  {:─>10}", "", "", "", "");
    for (depth, rate, pert, is_pert) in &sweep {
        let regime = if *is_pert { "perturb." } else { "NON-pert." };
        println!("  {:>10.0e}  {:>12.4e}  {:>12.4e}  {:>10}", depth, rate, pert, regime);
    }
    println!();

    // ═══════════════════════════════════════
    // 2. Realistic Noise Budget
    // ═══════════════════════════════════════
    println!("━━━ Realistic Noise Budget: Superconducting Cavity ━━━");
    println!();

    let nb_params = NoiseParams::niobium_3cm();
    let budget = noise::compute_noise_budget(&nb_params);

    println!("  Niobium 3 cm cavity at 20 mK (Q = {:.0e}):", nb_params.quality_factor);
    println!();
    println!("  Noise channel             Rate (Hz)       Fraction");
    println!("  ─────────────────────────────────────────────────────");
    let total_relax = budget.kappa + budget.gamma_tls + budget.gamma_qp;
    println!("  Cavity loss κ             {:>12.4e}    {:>6.1}%", budget.kappa, budget.kappa / total_relax * 100.0);
    println!("  1/f dephasing γ_φ         {:>12.4e}    (pure dephasing)", budget.gamma_phi);
    println!("  TLS defect loss           {:>12.4e}    {:>6.1}%", budget.gamma_tls, budget.gamma_tls / total_relax * 100.0);
    println!("  Quasiparticle loss        {:>12.4e}    {:>6.1}%", budget.gamma_qp, budget.gamma_qp / total_relax * 100.0);
    println!("  ─────────────────────────────────────────────────────");
    println!("  T₁ = {:.4e} s ({:.2} ms)", budget.t1, budget.t1 * 1e3);
    println!("  T₂ = {:.4e} s ({:.2} ms)", budget.t2, budget.t2 * 1e3);
    println!("  T₂ (topo protected) = {:.4e} s ({:.2} ms)", budget.t2_protected, budget.t2_protected * 1e3);
    println!("  Protection factor = {:.2}×", budget.protection_factor);
    println!();

    // Noise scaling with lattice size
    let scaling_results = noise::noise_scaling(&nb_params, &[4, 8, 12, 16, 24, 32]);
    println!("  Noise budget vs lattice size N:");
    println!("  {:>4}  {:>12}  {:>12}  {:>12}  {:>10}", "N", "T₂ (ms)", "T₂_prot (ms)", "Factor", "κ (Hz)");
    println!("  {:─>4}  {:─>12}  {:─>12}  {:─>12}  {:─>10}", "", "", "", "", "");
    for (n, nb) in &scaling_results {
        println!("  {:>4}  {:>12.4}  {:>12.4}  {:>12.2}×  {:>10.4}", n, nb.t2 * 1e3, nb.t2_protected * 1e3, nb.protection_factor, nb.kappa);
    }
    println!();

    // Temperature sweep
    let temp_results = noise::noise_vs_temperature(&nb_params, &[10.0, 15.0, 20.0, 30.0, 50.0, 100.0, 200.0]);
    println!("  Noise budget vs temperature:");
    println!("  {:>8}  {:>12}  {:>12}  {:>12}  {:>12}", "T (mK)", "T₁ (ms)", "T₂ (ms)", "T₂_prot", "n_thermal");
    println!("  {:─>8}  {:─>12}  {:─>12}  {:─>12}  {:─>12}", "", "", "", "", "");
    for (t_mk, nb) in &temp_results {
        let omega = nb_params.omega;
        let n_th = quantum_engine_sim::vacuum::thermal_occupation(omega, t_mk * 1e-3);
        println!("  {:>8.0}  {:>12.4}  {:>12.4}  {:>12.4}  {:>12.4e}", t_mk, nb.t1 * 1e3, nb.t2 * 1e3, nb.t2_protected * 1e3, n_th);
    }
    println!();

    // ═══════════════════════════════════════
    // 3. Lindblad Master Equation
    // ═══════════════════════════════════════
    println!("━━━ Lindblad Master Equation: Open Quantum System Dynamics ━━━");
    println!();

    let torus_8 = TorusLattice::new(8, 3e-2);
    let kappa_hz = 10.0; // Q ~ 10^10
    let temp = 0.020;

    println!("  Fundamental mode comparison (N=8, κ={} Hz, T=20 mK):", kappa_hz);
    let (bare, protected) = lindblad::compare_protection(&torus_8, kappa_hz, temp, 0.5, 10);
    let f_bare = *bare.vacuum_fidelities.last().unwrap_or(&0.0);
    let f_prot = *protected.vacuum_fidelities.last().unwrap_or(&0.0);
    println!("    Bare:      F(t=0.5s) = {:.6}, γ_eff = {:.2} Hz, <n> = {:.4e}", f_bare, bare.effective_gamma, bare.steady_state_n);
    println!("    Protected: F(t=0.5s) = {:.6}, γ_eff = {:.2} Hz, <n> = {:.4e}", f_prot, protected.effective_gamma, protected.steady_state_n);
    if f_bare > 0.0 {
        println!("    Fidelity advantage: {:.4}×", f_prot / f_bare.max(1e-15));
    }
    println!();

    // Multi-mode comparison
    println!("  Multi-mode Lindblad (first 6 modes, t=0.5s):");
    let multimode = lindblad::multimode_comparison(&torus_8, kappa_hz, temp, 0.5, 10, 6);
    println!("  {:>8}  {:>10}  {:>10}  {:>12}  {:>12}  {:>12}",
        "ω (GHz)", "Below gap", "Prot. fac.", "<n> steady", "n̄ theory", "γ_eff (Hz)");
    println!("  {:─>8}  {:─>10}  {:─>10}  {:─>12}  {:─>12}  {:─>12}", "", "", "", "", "", "");
    for e in &multimode {
        let gap_str = if e.below_gap { "YES" } else { "no" };
        println!("  {:>8.3}  {:>10}  {:>10.4e}  {:>12.4e}  {:>12.4e}  {:>12.4}",
            e.frequency_ghz, gap_str, e.protection_factor, e.steady_state_n, e.theoretical_n_th, e.effective_gamma);
    }
    println!();

    // ═══════════════════════════════════════
    // 4. Large-scale Toric Code (N=4 to 48)
    // ═══════════════════════════════════════
    println!("━━━ Large-Scale Toric Code Error Suppression ━━━");
    println!();

    let trials = 10_000;
    for &p in &[0.01, 0.03, 0.05, 0.07, 0.08, 0.09] {
        println!("  Physical error rate p = {:.0}%, {} trials:", p * 100.0, trials);
        println!("  {:>6}  {:>14}  {:>14}  {:>14}", "N", "P_logical", "α = -ln(P)/N", "Suppression");
        println!("  {:─>6}  {:─>14}  {:─>14}  {:─>14}", "", "", "", "");

        let sizes: Vec<usize> = vec![4, 8, 12, 16, 24, 32, 48];
        let results = toric_code::estimate_alpha(p, &sizes, trials);
        let p_ref = results.first().map(|r| r.logical_error_rate).unwrap_or(1.0);
        for r in &results {
            let alpha_str = match r.alpha {
                Some(a) => format!("{:.4}", a),
                None => "—".to_string(),
            };
            let suppression = if r.logical_error_rate > 0.0 {
                format!("{:.1}×", p_ref / r.logical_error_rate)
            } else {
                "∞".to_string()
            };
            println!("  {:>6}  {:>14.6}  {:>14}  {:>14}", r.lattice_size, r.logical_error_rate, alpha_str, suppression);
        }
        println!();
    }

    // ═══════════════════════════════════════
    // 5. Threshold estimation
    // ═══════════════════════════════════════
    println!("━━━ Error Correction Threshold ━━━");
    println!();
    println!("  Greedy decoder threshold (N=8 vs N=16 crossover):");
    println!("  {:>6}  {:>14}  {:>14}", "p", "P_L(N=8)", "P_L(N=16)");
    println!("  {:─>6}  {:─>14}  {:─>14}", "", "", "");

    for p_pct in (1..=12).map(|i| i as f64) {
        let p = p_pct / 100.0;
        let r8 = toric_code::estimate_alpha(p, &[8], 5000);
        let r16 = toric_code::estimate_alpha(p, &[16], 5000);
        let p8 = r8[0].logical_error_rate;
        let p16 = r16[0].logical_error_rate;
        let marker = if p8 > p16 { " ← below threshold" } else { "" };
        println!("  {:>5.0}%  {:>14.6}  {:>14.6}{}", p_pct, p8, p16, marker);
    }
    println!();

    // ═══════════════════════════════════════
    // Summary
    // ═══════════════════════════════════════
    println!("━━━ Summary of Enhanced Physics ━━━");
    println!();
    println!("  1. Wilson cross-check: Moore formula reproduces ~1 pair/s (ε_eff ≈ {:.2e})", comp.wilson.pert_param);
    println!("     Paraxiom 3cm cavity: {:.4} pairs/s at conservative δL/L = 10⁻⁵", comp.paraxiom_3cm.predicted_rate);
    println!();
    println!("  2. Noise budget (Nb, 20 mK, Q=10¹⁰):");
    println!("     T₁ = {:.2} ms, T₂ = {:.4} ms, T₂(protected) = {:.4} ms",
        budget.t1 * 1e3, budget.t2 * 1e3, budget.t2_protected * 1e3);
    println!("     Topological protection: {:.2}× T₂ enhancement", budget.protection_factor);
    println!();
    println!("  3. Lindblad dynamics: vacuum fidelity at t=0.5s:");
    println!("     Bare: {:.6}, Protected: {:.6} ({:.2}× advantage)", f_bare, f_prot, f_prot / f_bare.max(1e-15));
    println!();
    println!("  4. Toric code: exponential error suppression P_L ~ exp(-αN)");
    println!("     Greedy decoder threshold: p_c ~ 7-8%");
    println!();
    println!("  All physics: same spectral gap λ₁ = 2 - 2cos(2π/N).");
    println!("  Paraxiom Research — https://doi.org/10.5281/zenodo.18624950");
}
