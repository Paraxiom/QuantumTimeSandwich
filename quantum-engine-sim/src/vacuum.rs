//! Quantum vacuum physics on T²: Casimir energy, Unruh effect, dynamical Casimir.
//!
//! All formulas tuned to the **superconducting microwave cavity regime**:
//! - Cavity size: L ~ 1–10 cm
//! - Mode frequencies: ω ~ 1–100 GHz
//! - Temperature: T ~ 10–50 mK (dilution refrigerator)
//! - Quality factor: Q ~ 10⁸–10¹² (superconducting resonator)
//! - Modulation: δL/L ~ 10⁻⁶–10⁻⁴ (SQUID or piezo boundary)
//!
//! # Casimir energy on T²
//!
//! E_Casimir(L) = -(ℏc / L²) × C_T²
//! where C_T² is the Epstein zeta geometric factor.
//!
//! # Unruh effect
//!
//! T_U = ℏa / (2πck_B). On T², the spectral gap sets a_min below which
//! Unruh radiation is exponentially suppressed.
//!
//! # Dynamical Casimir effect (perturbative regime)
//!
//! Correct perturbative formula (Moore 1970, Wilson et al. 2011):
//!   Γ_mode = (δL × ω_n / c)² × Ω / (4π)
//!
//! Valid when δL × ω_n / c << 1. At L = 3 cm, δL/L = 10⁻⁵:
//!   δL × ω_min / c ≈ 6×10⁻⁵  (well within perturbative regime)
//!
//! References:
//! - Moore (1970), J. Math. Phys. 11, 2679
//! - Wilson et al. (2011), Nature 479, 376 (first experimental observation)
//! - Dodonov (2010), Phys. Scr. 82, 038105 (review)

use crate::torus::TorusLattice;
use crate::units::*;

/// Casimir energy computation result.
#[derive(Debug, Clone)]
pub struct CasimirResult {
    /// Total Casimir energy (J)
    pub energy: f64,
    /// Casimir force = -dE/dL (N)
    pub force: f64,
    /// Number of modes included
    pub num_modes: usize,
    /// Torus size (m)
    pub length: f64,
}

/// Unruh effect analysis on T².
#[derive(Debug, Clone)]
pub struct UnruhResult {
    /// Standard Unruh temperature at given acceleration (K)
    pub temperature: f64,
    /// Minimum detectable acceleration on this T² (m/s²)
    pub a_min: f64,
    /// Minimum Unruh temperature resolvable (K)
    pub t_min: f64,
    /// Whether the given acceleration is above threshold
    pub detectable: bool,
    /// Suppression factor below threshold (0 to 1)
    pub suppression: f64,
}

/// Dynamical Casimir effect result.
#[derive(Debug, Clone)]
pub struct DynamicalCasimirResult {
    /// Photon pair production rate (pairs/s)
    pub pair_rate: f64,
    /// Power output from vacuum radiation (W)
    pub power: f64,
    /// Number of active modes (in parametric resonance window)
    pub active_modes: usize,
    /// Total available modes
    pub total_modes: usize,
    /// Topological suppression: fraction of modes below spectral gap
    pub protected_fraction: f64,
    /// Perturbative parameter max(δL·ω/c) — must be << 1 for validity
    pub perturbative_param: f64,
}

/// Thermal photon occupation number at temperature T.
/// n_th(ω, T) = 1 / (exp(ℏω / k_B T) - 1)
pub fn thermal_occupation(omega: f64, temperature: f64) -> f64 {
    if temperature <= 0.0 || omega <= 0.0 {
        return 0.0;
    }
    let denom = KB * temperature;
    if denom <= 0.0 {
        return 0.0; // guard against subnormal underflow to zero
    }
    let x = HBAR * omega / denom;
    if !x.is_finite() || x > 500.0 {
        return 0.0; // avoid overflow/underflow
    }
    let exp_x_minus_1 = x.exp() - 1.0;
    if exp_x_minus_1 <= 0.0 {
        return 0.0; // guard against exp(x) ≈ 1 for very small x
    }
    1.0 / exp_x_minus_1
}

/// Average thermal photon number for the fundamental mode of the cavity.
pub fn fundamental_thermal_photons(torus: &TorusLattice, temperature: f64) -> f64 {
    thermal_occupation(torus.omega_min(), temperature)
}

/// Compute regularized Casimir energy on T² via mode summation.
pub fn casimir_energy(torus: &TorusLattice) -> CasimirResult {
    let n = torus.n as i64;
    let half = n / 2;
    let omega_unit = 2.0 * PI * C / torus.length;
    let omega_cutoff = torus.omega_max();

    let mut energy = 0.0;
    let mut num_modes = 0usize;

    for n1 in -half..=half {
        for n2 in -half..=half {
            if n1 == 0 && n2 == 0 {
                continue;
            }
            let r2 = (n1 * n1 + n2 * n2) as f64;
            let omega = omega_unit * r2.sqrt();
            let reg_factor = (-omega / omega_cutoff).exp();
            energy += 0.5 * HBAR * omega * reg_factor;
            num_modes += 1;
        }
    }

    // Subtract bulk (size-independent) contribution.
    // E_cas = E(L) - 2·E(2L) isolates the L-dependent geometric part.
    let mut energy_2l = 0.0;
    let omega_unit_2l = 2.0 * PI * C / (2.0 * torus.length);
    for n1 in -half..=half {
        for n2 in -half..=half {
            if n1 == 0 && n2 == 0 {
                continue;
            }
            let r2 = (n1 * n1 + n2 * n2) as f64;
            let omega = omega_unit_2l * r2.sqrt();
            let reg_factor = (-omega / omega_cutoff).exp();
            energy_2l += 0.5 * HBAR * omega * reg_factor;
        }
    }

    let e_casimir = energy - 2.0 * energy_2l;

    // Force via numerical derivative
    let dl = torus.length * 1e-6;
    let torus_plus = TorusLattice::new(torus.n, torus.length + dl);
    let e_plus = casimir_energy_raw(&torus_plus, omega_cutoff);
    let torus_minus = TorusLattice::new(torus.n, torus.length - dl);
    let e_minus = casimir_energy_raw(&torus_minus, omega_cutoff);
    let force = -(e_plus - e_minus) / (2.0 * dl);

    CasimirResult {
        energy: e_casimir,
        force,
        num_modes,
        length: torus.length,
    }
}

fn casimir_energy_raw(torus: &TorusLattice, omega_cutoff: f64) -> f64 {
    let n = torus.n as i64;
    let half = n / 2;
    let omega_unit = 2.0 * PI * C / torus.length;
    let mut energy = 0.0;
    for n1 in -half..=half {
        for n2 in -half..=half {
            if n1 == 0 && n2 == 0 {
                continue;
            }
            let r2 = (n1 * n1 + n2 * n2) as f64;
            let omega = omega_unit * r2.sqrt();
            energy += 0.5 * HBAR * omega * (-omega / omega_cutoff).exp();
        }
    }
    energy
}

/// Analyze Unruh effect on T².
pub fn unruh_analysis(torus: &TorusLattice, acceleration: f64) -> UnruhResult {
    let t_unruh = HBAR * acceleration / (2.0 * PI * C * KB);

    let gap = torus.spectral_gap();
    let omega_gap = (2.0 * PI * C / torus.length) * gap.sqrt();
    let t_min = HBAR * omega_gap / KB;
    let a_min = 2.0 * PI * C * KB * t_min / HBAR;

    let detectable = t_unruh >= t_min;
    let suppression = if t_unruh > 0.0 {
        (-t_min / t_unruh).exp()
    } else {
        0.0
    };

    UnruhResult {
        temperature: t_unruh,
        a_min,
        t_min,
        detectable,
        suppression,
    }
}

/// Compute dynamical Casimir photon production (perturbative regime).
///
/// Correct formula for oscillating boundary L(t) = L₀ + δL sin(Ωt):
///
/// Per-mode pair rate (parametric resonance at Ω ≈ 2ω_n):
///   Γ_n = (δL × ω_n / c)² × Ω / (4π)
///
/// Total rate sums over modes in the resonance window |Ω - 2ω_n| < Δω,
/// where Δω = Ω/Q_mode is the resonance bandwidth.
///
/// Only modes above the spectral gap contribute (topological protection).
///
/// Reference: Dodonov (2010), Eq. 2.15; Wilson et al. (2011)
pub fn dynamical_casimir(
    torus: &TorusLattice,
    modulation_depth: f64, // δL/L₀
    drive_frequency: f64,  // Ω (rad/s)
) -> DynamicalCasimirResult {
    let delta_l = modulation_depth * torus.length;
    let omega_gap = (2.0 * PI * C / torus.length) * torus.spectral_gap().sqrt();
    let freqs = torus.mode_frequencies();
    let total_modes = freqs.len();

    // Resonance bandwidth: Ω/Q where Q is the cavity quality factor.
    // For superconducting cavity, Q ~ 10⁹. Use a fractional bandwidth of 10⁻³
    // to capture modes near parametric resonance Ω ≈ 2ω_n.
    let resonance_bandwidth = drive_frequency * 1e-3;

    let mut pair_rate = 0.0;
    let mut active_modes = 0usize;
    let mut max_pert_param = 0.0_f64;

    for &omega_n in &freqs {
        // Skip modes below spectral gap (topologically protected)
        if omega_n <= omega_gap {
            continue;
        }

        // Parametric resonance condition: Ω ≈ 2ω_n
        let detuning = (drive_frequency - 2.0 * omega_n).abs();
        if detuning > resonance_bandwidth {
            continue;
        }

        active_modes += 1;

        // Perturbative parameter for this mode
        let pert_param = delta_l * omega_n / C;
        max_pert_param = max_pert_param.max(pert_param);

        // Per-mode pair rate: (δL·ω_n/c)² × Ω/(4π)
        let gamma_n = pert_param.powi(2) * drive_frequency / (4.0 * PI);
        pair_rate += gamma_n;
    }

    // If no exact resonance found, check broader window for nearest mode
    // and use off-resonance suppressed rate.
    if active_modes == 0 && !freqs.is_empty() {
        // Find mode closest to Ω/2
        let target = drive_frequency / 2.0;
        let mut best_omega = freqs[0];
        let mut best_detuning = (target - freqs[0]).abs();
        for &omega_n in &freqs {
            if omega_n <= omega_gap {
                continue;
            }
            let det = (target - omega_n).abs();
            if det < best_detuning {
                best_detuning = det;
                best_omega = omega_n;
            }
        }

        if best_omega > omega_gap {
            active_modes = 1;
            let pert_param = delta_l * best_omega / C;
            max_pert_param = pert_param;
            // Off-resonance suppression: Lorentzian profile
            let lorentz = resonance_bandwidth.powi(2)
                / (best_detuning.powi(2) + resonance_bandwidth.powi(2));
            pair_rate = pert_param.powi(2) * drive_frequency / (4.0 * PI) * lorentz;
        }
    }

    // Power: each pair carries energy ℏΩ
    let power = pair_rate * HBAR * drive_frequency;

    let sub_gap_modes = freqs.iter().filter(|&&omega| omega <= omega_gap).count();
    let protected_fraction = if total_modes > 0 {
        sub_gap_modes as f64 / total_modes as f64
    } else {
        0.0
    };

    DynamicalCasimirResult {
        pair_rate,
        power,
        active_modes,
        total_modes,
        protected_fraction,
        perturbative_param: max_pert_param,
    }
}

/// Casimir energy scaling: returns (L, E_casimir) pairs.
pub fn casimir_scaling(n: usize, l_min: f64, l_max: f64, steps: usize) -> Vec<(f64, f64)> {
    (0..steps)
        .map(|i| {
            let frac = i as f64 / (steps - 1) as f64;
            let l = l_min + frac * (l_max - l_min);
            let torus = TorusLattice::new(n, l);
            let cas = casimir_energy(&torus);
            (l, cas.energy)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn casimir_energy_is_negative() {
        let torus = TorusLattice::new(8, 1e-6);
        let cas = casimir_energy(&torus);
        assert!(cas.energy < 0.0, "Casimir energy should be negative, got {}", cas.energy);
    }

    #[test]
    fn casimir_scales_with_size() {
        let e1 = casimir_energy(&TorusLattice::new(8, 1e-6));
        let e2 = casimir_energy(&TorusLattice::new(8, 2e-6));
        assert!(e1.energy.abs() > e2.energy.abs());
    }

    #[test]
    fn unruh_threshold_exists() {
        let torus = TorusLattice::new(8, 3e-2); // 3 cm microwave cavity
        let low = unruh_analysis(&torus, 1.0);
        assert!(!low.detectable);
        assert!(low.suppression < 0.01);
    }

    #[test]
    fn dynamical_casimir_zero_modulation() {
        let torus = TorusLattice::new(8, 3e-2);
        let dce = dynamical_casimir(&torus, 0.0, 1e11);
        assert_eq!(dce.pair_rate, 0.0);
    }

    #[test]
    fn perturbative_param_small_microwave() {
        // At 3 cm with δL/L = 1e-5, perturbative param should be << 1
        let torus = TorusLattice::new(8, 3e-2);
        let omega_drive = 2.0 * torus.omega_min(); // resonant with fundamental
        let dce = dynamical_casimir(&torus, 1e-5, omega_drive);
        assert!(
            dce.perturbative_param < 0.01,
            "Perturbative param {} should be << 1",
            dce.perturbative_param
        );
    }

    #[test]
    fn thermal_occupation_at_millikelvin() {
        // At 20 mK, ω = 10 GHz: n_th should be very small
        let omega = 2.0 * PI * 10e9; // 10 GHz
        let n_th = thermal_occupation(omega, 0.020);
        assert!(n_th < 0.01, "n_th = {} should be < 0.01 at 20 mK / 10 GHz", n_th);
    }

    #[test]
    fn thermal_occupation_at_room_temp() {
        // At 300K, ω = 10 GHz: n_th should be large (classical limit)
        let omega = 2.0 * PI * 10e9;
        let n_th = thermal_occupation(omega, 300.0);
        assert!(n_th > 100.0, "n_th = {} should be >> 1 at room temp", n_th);
    }
}

// ─── Kani formal verification harnesses ─────────────────────────────────────
#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Prove thermal_occupation never panics and never returns NaN.
    /// The function now has guards for all intermediate overflow/underflow paths.
    #[kani::proof]
    #[kani::unwind(2)]
    fn thermal_occupation_no_panic() {
        let omega: f64 = kani::any();
        let temp: f64 = kani::any();
        kani::assume(omega.is_finite() && omega >= 0.0 && omega < 1e16);
        kani::assume(temp.is_finite() && temp >= 0.0 && temp < 1e6);
        let n_th = thermal_occupation(omega, temp);
        assert!(n_th >= 0.0);
        // With the new guards, NaN should be impossible
        assert!(!n_th.is_nan());
    }

    /// Prove thermal_occupation returns 0 for zero temperature.
    #[kani::proof]
    #[kani::unwind(2)]
    fn thermal_occupation_zero_at_zero_temp() {
        let omega: f64 = kani::any();
        kani::assume(omega.is_finite() && omega > 0.0 && omega < 1e16);
        let n_th = thermal_occupation(omega, 0.0);
        assert_eq!(n_th, 0.0);
    }

    /// Prove thermal_occupation returns 0 for zero frequency.
    #[kani::proof]
    #[kani::unwind(2)]
    fn thermal_occupation_zero_at_zero_omega() {
        let temp: f64 = kani::any();
        kani::assume(temp.is_finite() && temp > 0.0 && temp < 1e6);
        let n_th = thermal_occupation(0.0, temp);
        assert_eq!(n_th, 0.0);
    }

    /// Prove thermal_occupation returns 0 for negative inputs.
    #[kani::proof]
    #[kani::unwind(2)]
    fn thermal_occupation_zero_for_negative() {
        let omega: f64 = kani::any();
        let temp: f64 = kani::any();
        kani::assume(omega.is_finite() && temp.is_finite());
        kani::assume(omega.abs() < 1e16 && temp.abs() < 1e6);
        kani::assume(omega < 0.0 || temp < 0.0);
        let n_th = thermal_occupation(omega, temp);
        assert_eq!(n_th, 0.0);
    }

    // NOTE: Value properties of thermal_occupation at specific temperature/frequency
    // (e.g., microwave regime assertions) depend on exp() which CBMC models
    // non-deterministically. Verified by unit tests: thermal_occupation_at_millikelvin,
    // thermal_occupation_at_room_temp.
}
