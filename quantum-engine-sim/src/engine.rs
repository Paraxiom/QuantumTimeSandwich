//! Quantum engine cycle simulation on T².
//!
//! # The Toroidal Vacuum Engine
//!
//! Analogous to a thermodynamic Otto cycle, but operating on the quantum
//! vacuum of a toroidal cavity. The "working fluid" is the vacuum state
//! of a quantum field on T², and the "pistons" are boundary modulations.
//!
//! ## Cycle
//!
//! 1. **Compression** (L_max → L_min): Adiabatic reduction of torus size.
//!    Casimir energy becomes more negative. Mode frequencies blue-shift.
//!    Work is stored in the vacuum field.
//!
//! 2. **Extraction**: Oscillate boundary at frequency Ω. Dynamical Casimir
//!    effect produces photon pairs from the vacuum. Topological protection
//!    from spectral gap ensures coherent extraction (no sub-gap noise).
//!
//! 3. **Expansion** (L_min → L_max): Release stored elastic energy.
//!    Mode frequencies red-shift back.
//!
//! 4. **Idle**: Vacuum re-thermalizes (protected by spectral gap from
//!    decoherence — exponential suppression of thermal noise below gap).
//!
//! ## Key insight
//!
//! The spectral gap λ₁ of T² serves dual roles:
//! - **Thermodynamic**: Sets minimum temperature for vacuum fluctuations
//! - **Topological**: Exponentially suppresses decoherence losses per cycle
//!
//! Net work per cycle = ΔE_Casimir × η_topo, where η_topo approaches 1
//! as the spectral gap increases (larger N or smaller L).
//!
//! ## Analog gravity connection
//!
//! The compression/expansion cycle on T² is mathematically equivalent to
//! a time-dependent metric perturbation. In the comoving frame of the
//! oscillating boundary:
//! - Compression → Unruh-like acceleration → particle creation
//! - The spectral gap → mass gap in the field theory → minimum energy to
//!   excite the vacuum (analogous to confinement in QCD)
//! - The toroidal topology → periodic identification → Matsubara frequencies
//!   → thermal field theory at inverse temperature β = L/c

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
    /// Boundary oscillation frequency for DCE extraction (rad/s)
    pub drive_frequency: f64,
    /// Modulation depth δL/L for DCE
    pub modulation_depth: f64,
    /// Number of extraction cycles per engine cycle
    pub extraction_cycles: usize,
    /// Physical decoherence rate (Hz) — ambient noise
    pub decoherence_rate: f64,
}

impl EngineConfig {
    /// Auto-derive drive frequency from compressed cavity geometry.
    /// Sets Ω = 4 × ω_min(L_min) to ensure several active modes.
    pub fn auto_drive_frequency(&self) -> f64 {
        let omega_min = 2.0 * PI * C / self.l_min;
        4.0 * omega_min // parametric resonance: need Ω > 2ω for active modes
    }
}

impl Default for EngineConfig {
    fn default() -> Self {
        // Optical-scale toroidal cavity.
        // Drive frequency auto-derived in simulate() if set to 0.
        Self {
            n: 8,
            l_max: 1e-6,                  // 1 μm
            l_min: 0.5e-6,                // 0.5 μm
            drive_frequency: 0.0,          // 0 = auto-derive from cavity geometry
            modulation_depth: 0.01,        // 1% boundary modulation
            extraction_cycles: 1000,
            decoherence_rate: 1e6,         // 1 MHz ambient decoherence
        }
    }
}

/// Result of one engine cycle.
#[derive(Debug, Clone)]
pub struct CycleResult {
    /// Casimir energy at L_max (J)
    pub e_max: f64,
    /// Casimir energy at L_min (J)
    pub e_min: f64,
    /// Work input for compression (J)
    pub work_compression: f64,
    /// Energy extracted via dynamical Casimir (J)
    pub energy_extracted: f64,
    /// Decoherence loss per cycle (J)
    pub decoherence_loss: f64,
    /// Net work output per cycle (J)
    pub net_work: f64,
    /// Topological protection factor (0 to 1)
    pub protection_factor: f64,
    /// Thermodynamic efficiency η = W_net / W_in
    pub efficiency: f64,
    /// Spectral gap λ₁
    pub spectral_gap: f64,
}

/// Result of full engine simulation.
#[derive(Debug, Clone)]
pub struct EngineResult {
    pub config: EngineConfig,
    pub cycle: CycleResult,
    /// Casimir analysis at L_max
    pub casimir_max: CasimirResult,
    /// Casimir analysis at L_min
    pub casimir_min: CasimirResult,
    /// Unruh threshold analysis
    pub unruh_acceleration_threshold: f64,
    /// Effective power output (W)
    pub power_output: f64,
    /// Comparison: efficiency with vs without topological protection
    pub efficiency_unprotected: f64,
    /// Coherence time enhancement from toroidal topology
    pub coherence_enhancement: f64,
}

/// Run one engine cycle.
pub fn run_cycle(config: &EngineConfig) -> CycleResult {
    let torus_max = TorusLattice::new(config.n, config.l_max);
    let torus_min = TorusLattice::new(config.n, config.l_min);

    let cas_max = casimir_energy(&torus_max);
    let cas_min = casimir_energy(&torus_min);

    // Work to compress: |E_Casimir(L_min) - E_Casimir(L_max)|
    // (Casimir energy is more negative at smaller L, so compression requires work)
    let work_compression = (cas_min.energy - cas_max.energy).abs();

    // Auto-derive drive frequency if not set
    let drive_freq = if config.drive_frequency > 0.0 {
        config.drive_frequency
    } else {
        config.auto_drive_frequency()
    };

    // Dynamical Casimir extraction at compressed size
    let dce = dynamical_casimir(&torus_min, config.modulation_depth, drive_freq);
    let extraction_time = config.extraction_cycles as f64 * 2.0 * PI / drive_freq;
    let energy_extracted = dce.power * extraction_time;

    // Spectral gap protection against decoherence
    let gap = torus_min.spectral_gap();

    // Decoherence loss: proportional to cycle time × decoherence rate,
    // but exponentially suppressed by spectral gap.
    // Loss ~ E_stored × γ × t_cycle × exp(-λ₁/γ_normalized)
    let cycle_time = extraction_time + config.l_max / C; // extraction + transit
    let gamma_normalized = config.decoherence_rate * config.l_min / C;
    let protection_factor = (-gap / gamma_normalized.max(1e-30)).exp().min(1.0);
    let raw_loss = work_compression * config.decoherence_rate * cycle_time;
    let decoherence_loss = raw_loss * protection_factor;

    let net_work = energy_extracted - decoherence_loss;
    let efficiency = if work_compression > 0.0 {
        (net_work / work_compression).max(0.0)
    } else {
        0.0
    };

    CycleResult {
        e_max: cas_max.energy,
        e_min: cas_min.energy,
        work_compression,
        energy_extracted,
        decoherence_loss,
        net_work,
        protection_factor,
        efficiency,
        spectral_gap: gap,
    }
}

/// Run full engine simulation with diagnostics.
pub fn simulate(config: &EngineConfig) -> EngineResult {
    let torus_max = TorusLattice::new(config.n, config.l_max);
    let torus_min = TorusLattice::new(config.n, config.l_min);

    let cas_max = casimir_energy(&torus_max);
    let cas_min = casimir_energy(&torus_min);

    let cycle = run_cycle(config);

    // Unruh threshold
    let unruh = unruh_analysis(&torus_min, 1.0);
    let a_threshold = unruh.a_min;

    // Power output
    let drive_freq = if config.drive_frequency > 0.0 {
        config.drive_frequency
    } else {
        config.auto_drive_frequency()
    };
    let cycle_time = config.extraction_cycles as f64 * 2.0 * PI / drive_freq
        + config.l_max / C;
    let power = if cycle_time > 0.0 {
        cycle.net_work / cycle_time
    } else {
        0.0
    };

    // Unprotected efficiency (no spectral gap benefit)
    let raw_loss = cycle.work_compression * config.decoherence_rate * cycle_time;
    let net_unprotected = cycle.energy_extracted - raw_loss;
    let eff_unprotected = if cycle.work_compression > 0.0 {
        (net_unprotected / cycle.work_compression).max(0.0)
    } else {
        0.0
    };

    // Coherence enhancement from torus vs single qubit
    let t2_bare = 1.0 / config.decoherence_rate * 1e9; // ns
    let t2_enhanced = coherence::tonnetz_enhanced_t2(t2_bare, config.n, 1.0);
    let coherence_enhancement = t2_enhanced / t2_bare;

    EngineResult {
        config: config.clone(),
        cycle,
        casimir_max: cas_max,
        casimir_min: cas_min,
        unruh_acceleration_threshold: a_threshold,
        power_output: power,
        efficiency_unprotected: eff_unprotected,
        coherence_enhancement,
    }
}

/// Compare engine performance across lattice sizes.
/// Shows how topological protection scales with N.
pub fn scaling_study(
    l_max: f64,
    l_min: f64,
    sizes: &[usize],
) -> Vec<EngineResult> {
    sizes
        .iter()
        .map(|&n| {
            let config = EngineConfig {
                n,
                l_max,
                l_min,
                ..Default::default()
            };
            simulate(&config)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_config_runs() {
        let config = EngineConfig::default();
        let result = simulate(&config);
        assert!(result.cycle.spectral_gap > 0.0);
        assert!(result.coherence_enhancement >= 1.0);
    }

    #[test]
    fn compression_requires_work() {
        let config = EngineConfig::default();
        let cycle = run_cycle(&config);
        assert!(cycle.work_compression > 0.0);
    }

    #[test]
    fn larger_lattice_better_protection() {
        let r4 = simulate(&EngineConfig { n: 4, ..Default::default() });
        let r12 = simulate(&EngineConfig { n: 12, ..Default::default() });
        // Larger lattice should have better coherence enhancement
        assert!(r12.coherence_enhancement >= r4.coherence_enhancement);
    }
}
