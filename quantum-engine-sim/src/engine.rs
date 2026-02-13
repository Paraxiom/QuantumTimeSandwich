//! Quantum engine cycle simulation on T².
//!
//! # The Toroidal Vacuum Engine
//!
//! Analogous to a thermodynamic Otto cycle, operating on the quantum vacuum
//! of a superconducting toroidal microwave cavity.
//!
//! ## Physical regime
//!
//! - Cavity: 3 cm superconducting resonator at 20 mK (dilution fridge)
//! - Modes: ω₁ ≈ 10 GHz (fundamental), N² total modes on lattice
//! - Quality: Q ~ 10⁸–10¹² → γ = ω/Q ~ 0.1–1000 Hz
//! - Modulation: δL/L ~ 10⁻⁵ via SQUID-terminated boundary
//! - Perturbative: δL·ω/c ~ 10⁻⁵ << 1 (formula valid)
//!
//! ## Cycle
//!
//! 1. **Compression** (L_max → L_min): Adiabatic size reduction.
//!    Casimir energy becomes more negative. Mode frequencies blue-shift.
//!
//! 2. **Extraction**: Drive boundary at Ω ≈ 2ω₁. Dynamical Casimir
//!    effect produces photon pairs. Spectral gap protects sub-gap modes.
//!
//! 3. **Expansion** (L_min → L_max): Release vacuum elastic energy.
//!
//! 4. **Idle**: Re-thermalize. Spectral gap exponentially suppresses
//!    thermal decoherence below the gap frequency.
//!
//! ## Analog gravity
//!
//! - Compression ↔ Unruh acceleration (particle creation from vacuum)
//! - Spectral gap ↔ mass gap (minimum excitation energy)
//! - Toroidal periodicity ↔ Matsubara frequencies (thermal field theory)
//! - DCE ↔ Hawking radiation (moving mirror ≡ accelerating horizon)

use crate::torus::TorusLattice;
use crate::vacuum::{casimir_energy, dynamical_casimir, unruh_analysis, CasimirResult};
use crate::coherence;
use crate::units::*;

/// Configuration for a quantum engine simulation.
#[derive(Debug, Clone)]
pub struct EngineConfig {
    /// Lattice dimension N (N×N torus)
    pub n: usize,
    /// Maximum torus size (meters)
    pub l_max: f64,
    /// Minimum torus size (meters) — compression target
    pub l_min: f64,
    /// Boundary oscillation frequency for DCE extraction (rad/s).
    /// Set to 0 to auto-derive from cavity geometry.
    pub drive_frequency: f64,
    /// Modulation depth δL/L for DCE (dimensionless)
    pub modulation_depth: f64,
    /// Number of extraction oscillation cycles per engine cycle
    pub extraction_cycles: usize,
    /// Physical decoherence rate γ (Hz) = ω/Q for cavity
    pub decoherence_rate: f64,
    /// Operating temperature (K) — dilution fridge
    pub temperature: f64,
}

impl EngineConfig {
    /// Auto-derive drive frequency: Ω = 2 × ω_min(L_min) for parametric resonance.
    pub fn auto_drive_frequency(&self) -> f64 {
        let omega_min = 2.0 * PI * C / self.l_min;
        2.0 * omega_min
    }

    /// Effective drive frequency (auto-derived if set to 0).
    pub fn effective_drive(&self) -> f64 {
        if self.drive_frequency > 0.0 {
            self.drive_frequency
        } else {
            self.auto_drive_frequency()
        }
    }

    /// Perturbative parameter: δL × ω_min / c. Must be << 1 for DCE validity.
    pub fn perturbative_param(&self) -> f64 {
        let omega_min = 2.0 * PI * C / self.l_min;
        self.modulation_depth * self.l_min * omega_min / C
    }

    /// Superconducting microwave cavity defaults.
    pub fn microwave() -> Self {
        Self {
            n: 8,
            l_max: 3.0e-2,                // 3.0 cm
            l_min: 2.9e-2,                // 2.9 cm (small compression)
            drive_frequency: 0.0,          // auto = 2 × ω_min ≈ 130 GHz
            modulation_depth: 1e-5,        // δL/L = 10⁻⁵ (SQUID boundary)
            extraction_cycles: 1_000_000,  // 1M oscillations per engine cycle
            decoherence_rate: 10.0,        // 10 Hz (Q ≈ 10¹⁰)
            temperature: 0.020,            // 20 mK
        }
    }
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self::microwave()
    }
}

/// Result of one engine cycle.
#[derive(Debug, Clone)]
pub struct CycleResult {
    pub e_max: f64,
    pub e_min: f64,
    pub work_compression: f64,
    pub energy_extracted: f64,
    pub decoherence_loss: f64,
    pub thermal_noise: f64,
    pub net_work: f64,
    /// Topological protection factor: exp(-λ₁ / γ_norm)
    pub protection_factor: f64,
    /// Thermodynamic efficiency η = W_net / W_compression
    pub efficiency: f64,
    pub spectral_gap: f64,
    /// Cycle time (seconds)
    pub cycle_time: f64,
}

/// Result of full engine simulation.
#[derive(Debug, Clone)]
pub struct EngineResult {
    pub config: EngineConfig,
    pub cycle: CycleResult,
    pub casimir_max: CasimirResult,
    pub casimir_min: CasimirResult,
    pub unruh_acceleration_threshold: f64,
    /// Power output (W)
    pub power_output: f64,
    /// Efficiency without topological protection
    pub efficiency_unprotected: f64,
    /// Coherence enhancement from torus topology
    pub coherence_enhancement: f64,
    /// Drive frequency used (Hz)
    pub drive_freq: f64,
    /// Perturbative parameter (must be << 1)
    pub perturbative_param: f64,
    /// Thermal photons in fundamental mode
    pub thermal_photons: f64,
}

/// Run one engine cycle.
pub fn run_cycle(config: &EngineConfig) -> CycleResult {
    let torus_max = TorusLattice::new(config.n, config.l_max);
    let torus_min = TorusLattice::new(config.n, config.l_min);

    let cas_max = casimir_energy(&torus_max);
    let cas_min = casimir_energy(&torus_min);

    let work_compression = (cas_min.energy - cas_max.energy).abs();

    let drive_freq = config.effective_drive();

    // Dynamical Casimir extraction at compressed size
    let dce = dynamical_casimir(&torus_min, config.modulation_depth, drive_freq);
    let extraction_time = config.extraction_cycles as f64 * 2.0 * PI / drive_freq;
    let energy_extracted = dce.power * extraction_time;

    let gap = torus_min.spectral_gap();

    // Cycle time = extraction + adiabatic transit (speed of sound ~ c)
    let cycle_time = extraction_time + (config.l_max - config.l_min).abs() / C * 100.0;
    // Factor 100: adiabatic means slow compared to cavity round-trip

    // Decoherence loss: energy leaks at rate γ, suppressed by spectral gap.
    // γ_normalized = γ × L/c = dimensionless decoherence per cavity crossing.
    // Topological protection: exp(-λ₁ / γ_norm) suppresses loss.
    let gamma_normalized = config.decoherence_rate * config.l_min / C;
    let protection_factor = if gamma_normalized > 1e-30 {
        (-gap / gamma_normalized).exp().min(1.0)
    } else {
        0.0 // perfect protection when γ → 0
    };

    // Raw decoherence loss (without protection)
    let raw_loss = energy_extracted * config.decoherence_rate * cycle_time;
    let decoherence_loss = raw_loss * protection_factor;

    // Thermal noise: n_th photons per mode × ℏω per photon × N_modes × γ × t
    let n_th = crate::vacuum::fundamental_thermal_photons(&torus_min, config.temperature);
    let thermal_noise = n_th * HBAR * torus_min.omega_min()
        * torus_min.num_sites() as f64
        * config.decoherence_rate * cycle_time
        * protection_factor; // also suppressed by spectral gap

    let net_work = energy_extracted - decoherence_loss - thermal_noise;
    let efficiency = if work_compression > 0.0 {
        net_work / work_compression
    } else {
        0.0
    };

    CycleResult {
        e_max: cas_max.energy,
        e_min: cas_min.energy,
        work_compression,
        energy_extracted,
        decoherence_loss,
        thermal_noise,
        net_work,
        protection_factor,
        efficiency,
        spectral_gap: gap,
        cycle_time,
    }
}

/// Run full engine simulation with diagnostics.
pub fn simulate(config: &EngineConfig) -> EngineResult {
    let torus_max = TorusLattice::new(config.n, config.l_max);
    let torus_min = TorusLattice::new(config.n, config.l_min);

    let cas_max = casimir_energy(&torus_max);
    let cas_min = casimir_energy(&torus_min);

    let cycle = run_cycle(config);
    let drive_freq = config.effective_drive();

    // Unruh threshold
    let unruh = unruh_analysis(&torus_min, 1.0);

    // Power output
    let power = if cycle.cycle_time > 0.0 {
        cycle.net_work / cycle.cycle_time
    } else {
        0.0
    };

    // Unprotected efficiency
    let raw_loss = cycle.energy_extracted * config.decoherence_rate * cycle.cycle_time;
    let n_th = crate::vacuum::fundamental_thermal_photons(&torus_min, config.temperature);
    let raw_thermal = n_th * HBAR * torus_min.omega_min()
        * torus_min.num_sites() as f64
        * config.decoherence_rate * cycle.cycle_time;
    let net_unprotected = cycle.energy_extracted - raw_loss - raw_thermal;
    let eff_unprotected = if cycle.work_compression > 0.0 {
        net_unprotected / cycle.work_compression
    } else {
        0.0
    };

    // Coherence enhancement
    let t2_bare = if config.decoherence_rate > 0.0 {
        1.0 / config.decoherence_rate * 1e9
    } else {
        1e12
    };
    let t2_enhanced = coherence::tonnetz_enhanced_t2(t2_bare, config.n, 1.0);

    let thermal_n = crate::vacuum::fundamental_thermal_photons(&torus_min, config.temperature);

    EngineResult {
        config: config.clone(),
        cycle,
        casimir_max: cas_max,
        casimir_min: cas_min,
        unruh_acceleration_threshold: unruh.a_min,
        power_output: power,
        efficiency_unprotected: eff_unprotected,
        coherence_enhancement: t2_enhanced / t2_bare,
        drive_freq,
        perturbative_param: config.perturbative_param(),
        thermal_photons: thermal_n,
    }
}

/// Compare engine performance across lattice sizes.
pub fn scaling_study(base_config: &EngineConfig, sizes: &[usize]) -> Vec<EngineResult> {
    sizes
        .iter()
        .map(|&n| {
            let config = EngineConfig {
                n,
                ..base_config.clone()
            };
            simulate(&config)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn microwave_config_runs() {
        let config = EngineConfig::microwave();
        let result = simulate(&config);
        assert!(result.cycle.spectral_gap > 0.0);
        assert!(result.coherence_enhancement >= 1.0);
    }

    #[test]
    fn perturbative_param_is_small() {
        let config = EngineConfig::microwave();
        assert!(
            config.perturbative_param() < 0.01,
            "δL·ω/c = {} must be << 1",
            config.perturbative_param()
        );
    }

    #[test]
    fn compression_requires_work() {
        let cycle = run_cycle(&EngineConfig::microwave());
        assert!(cycle.work_compression > 0.0);
    }

    #[test]
    fn larger_lattice_better_coherence() {
        let r4 = simulate(&EngineConfig { n: 4, ..EngineConfig::microwave() });
        let r16 = simulate(&EngineConfig { n: 16, ..EngineConfig::microwave() });
        assert!(r16.coherence_enhancement >= r4.coherence_enhancement);
    }
}
