//! Quantum vacuum physics on T²: Casimir energy, Unruh effect, dynamical Casimir.
//!
//! # Casimir energy on T²
//!
//! A massless scalar field on T² (periods L₁ = L₂ = L) has vacuum energy
//! modified by the periodic boundary conditions. The regularized Casimir
//! energy density:
//!
//!   E_Casimir(L) = -(ℏc / L²) × C_T²
//!
//! where C_T² is computed from the Epstein zeta function on Z².
//!
//! # Unruh effect
//!
//! An observer with proper acceleration a experiences thermal radiation:
//!   T_U = ℏa / (2πck_B)
//!
//! On discrete T², the spectral gap sets a minimum detectable acceleration:
//!   a_min = 2πck_B × T_gap / ℏ
//! where T_gap = ℏω_min / k_B and ω_min = 2πc√λ₁ / L.
//!
//! Below a_min, the toroidal geometry renders the vacuum "rigid" — the
//! topological protection suppresses Unruh radiation at low accelerations.
//!
//! # Dynamical Casimir effect
//!
//! When the torus boundary oscillates at frequency Ω, photon pairs are
//! produced from the vacuum. The production rate scales as:
//!   Γ ~ (δL/L)² × (Ω/ω₁)² × ω₁
//!
//! Only modes above the spectral gap are excited — topological protection
//! prevents vacuum noise at long wavelengths.

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
    /// Number of active modes (above spectral gap)
    pub active_modes: usize,
    /// Total available modes
    pub total_modes: usize,
    /// Topological suppression: fraction of modes protected
    pub protected_fraction: f64,
}

/// Compute regularized Casimir energy on T² via mode summation.
///
/// Uses exponential regularization with lattice UV cutoff:
///   E_reg = (ℏ/2) Σ_{n≠0} ω_n × exp(-ω_n/ω_max)
///   minus the divergent vacuum energy of flat space.
///
/// The finite Casimir energy is the difference between T² and R² at the
/// same UV cutoff, which converges as the cutoff is removed.
pub fn casimir_energy(torus: &TorusLattice) -> CasimirResult {
    let n = torus.n as i64;
    let half = n / 2;
    let omega_unit = 2.0 * PI * C / torus.length;
    let omega_cutoff = torus.omega_max();

    let mut energy = 0.0;
    let mut num_modes = 0usize;

    // Mode sum with exponential regularization
    for n1 in -half..=half {
        for n2 in -half..=half {
            if n1 == 0 && n2 == 0 {
                continue;
            }
            let r2 = (n1 * n1 + n2 * n2) as f64;
            let omega = omega_unit * r2.sqrt();
            // Regularized zero-point energy per mode
            let reg_factor = (-omega / omega_cutoff).exp();
            energy += 0.5 * HBAR * omega * reg_factor;
            num_modes += 1;
        }
    }

    // Subtract the flat-space (continuum) contribution at the same cutoff.
    // For a 2D box of area L², the mode density is L²/(4π).
    // Continuum integral: (L²/4π) ∫₀^∞ ω² (ℏω/2) e^{-ω/ω_c} dω / (2πc/L)²
    // = (ℏ/2)(L/(2π))² × 2π ∫₀^∞ κ² × κ × e^{-κL/(2π)/ω_c} dκ ... complicated.
    //
    // Instead, we compute the Casimir contribution as the energy at size L
    // minus the energy at size 2L (which approaches the bulk limit faster).
    // The Casimir energy is the L-dependent part.
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

    // The Casimir energy is the L-dependent (geometric) part of the vacuum energy.
    // On T², E_Casimir ~ -ℏc C_T² / L². Since E(L) > E(2L) in absolute terms
    // (higher frequencies at smaller L), the physical Casimir energy is negative:
    // E_cas = E(L) - 2·E(2L) approximates the finite-size correction.
    // The factor of 2 accounts for the mode density scaling: doubling L
    // halves each ω_n but the sum scales as L (bulk energy ∝ L in 2D).
    let e_casimir = energy - 2.0 * energy_2l;

    // Casimir force via numerical derivative: F = -dE/dL ≈ -ΔE/ΔL
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

/// Raw mode sum energy (internal, for force computation).
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
///
/// On flat space, any acceleration produces Unruh radiation.
/// On T², the spectral gap creates a threshold: below a_min,
/// the toroidal vacuum is topologically protected from thermal excitation.
pub fn unruh_analysis(torus: &TorusLattice, acceleration: f64) -> UnruhResult {
    // Standard Unruh temperature
    let t_unruh = HBAR * acceleration / (2.0 * PI * C * KB);

    // Minimum resolvable frequency from spectral gap
    let gap = torus.spectral_gap();
    let omega_gap = (2.0 * PI * C / torus.length) * gap.sqrt();

    // Minimum temperature corresponding to spectral gap
    let t_min = HBAR * omega_gap / KB;

    // Minimum acceleration to excite the gap
    let a_min = 2.0 * PI * C * KB * t_min / HBAR;

    let detectable = t_unruh >= t_min;

    // Suppression factor: exponential suppression below threshold
    // Models the Boltzmann factor for exciting across the gap
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

/// Compute dynamical Casimir photon production rate.
///
/// When the torus boundary oscillates: L(t) = L₀ + δL sin(Ωt),
/// the vacuum radiates photon pairs at rate:
///
///   Γ ≈ (δL/L₀)² × (Ω/c)² × (Ω/2π) × N_active
///
/// where N_active is the number of modes with ω < Ω/2 (parametric resonance
/// condition: photon pairs each carry energy ℏΩ/2).
///
/// The spectral gap protects low-frequency modes from excitation,
/// reducing vacuum noise.
pub fn dynamical_casimir(
    torus: &TorusLattice,
    modulation_depth: f64, // δL/L₀ (dimensionless)
    drive_frequency: f64,  // Ω (rad/s)
) -> DynamicalCasimirResult {
    let omega_gap = (2.0 * PI * C / torus.length) * torus.spectral_gap().sqrt();
    let freqs = torus.mode_frequencies();
    let total_modes = freqs.len();

    // Active modes: those with ω_n < Ω/2 (parametric resonance condition)
    // AND above the spectral gap (topological protection removes sub-gap modes)
    let active_modes = freqs
        .iter()
        .filter(|&&omega| omega < drive_frequency / 2.0 && omega > omega_gap)
        .count();

    // Photon pair production rate (simplified Schwinger formula for oscillating boundary)
    // Γ_pair ≈ (δL/L)² × (Ω²/c²) × (Ω/2π) × N_active
    let pair_rate = modulation_depth.powi(2)
        * (drive_frequency / C).powi(2)
        * (drive_frequency / (2.0 * PI))
        * active_modes as f64;

    // Power: each pair carries energy ℏΩ
    let power = pair_rate * HBAR * drive_frequency;

    // Protected fraction: modes below spectral gap that are NOT excited
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
    }
}

/// Casimir energy scaling: E(L) ~ -C/L².
/// Returns (L, E_casimir) pairs for plotting.
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
        // Casimir energy on T² should be negative (attractive)
        let torus = TorusLattice::new(8, 1e-6);
        let cas = casimir_energy(&torus);
        assert!(cas.energy < 0.0, "Casimir energy should be negative, got {}", cas.energy);
    }

    #[test]
    fn casimir_scales_with_size() {
        let e1 = casimir_energy(&TorusLattice::new(8, 1e-6));
        let e2 = casimir_energy(&TorusLattice::new(8, 2e-6));
        // E ~ -1/L², so |E(L)| > |E(2L)|
        assert!(e1.energy.abs() > e2.energy.abs());
    }

    #[test]
    fn unruh_threshold_exists() {
        let torus = TorusLattice::new(8, 1e-6);
        let low = unruh_analysis(&torus, 1.0); // 1 m/s² — very low
        assert!(!low.detectable);
        assert!(low.suppression < 0.01);
    }

    #[test]
    fn dynamical_casimir_zero_modulation() {
        let torus = TorusLattice::new(8, 1e-6);
        let dce = dynamical_casimir(&torus, 0.0, 1e12);
        assert_eq!(dce.pair_rate, 0.0);
    }
}
