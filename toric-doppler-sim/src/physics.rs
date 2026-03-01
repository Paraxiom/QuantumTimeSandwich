//! Doppler cooling physics + Tonnetz coherence filter.
//!
//! Ports the CNT optomechanical model from the JS demo with a proper
//! Tonnetz spectral-gap enhancement replacing the weak scalar fudge.

use tonnetz_coherence_sim::coherence::theoretical_decay_rate;
use tonnetz_coherence_sim::topology::{build_coupling_map, CouplingTopology};

/// Physical constants.
const HBAR: f64 = 1.054571817e-34; // J·s
const K_B: f64 = 1.380649e-23; // J/K

/// All tunable physical parameters for the Doppler cooling model.
#[derive(Debug, Clone)]
pub struct PhysicsParams {
    /// Bath temperature (K).
    pub temperature: f64,
    /// Mechanical frequency of CNT resonator (rad/s).
    pub omega_m: f64,
    /// Laser power (mW).
    pub laser_power: f64,
    /// Laser detuning from resonance (units of omega_m).
    pub detuning: f64,
    /// Cavity linewidth / 2 (units of omega_m).
    pub kappa: f64,
    /// Optomechanical coupling rate (Hz).
    pub g0: f64,
    /// Piezo drive frequency (rad/s).
    pub piezo_freq: f64,
    /// Piezo voltage (V).
    pub piezo_voltage: f64,
    /// Tonnetz grid size for spectral gap.
    pub tonnetz_grid_size: usize,
    /// Quality factor of the Tonnetz harmonic filter.
    pub tonnetz_q: f64,
}

impl Default for PhysicsParams {
    fn default() -> Self {
        Self {
            temperature: 300.0,
            omega_m: 2.0 * std::f64::consts::PI * 1.0e9, // 1 GHz
            laser_power: 5.0,
            detuning: -1.0, // red-detuned by omega_m
            kappa: 0.5,     // kappa/2 = 0.5 * omega_m
            g0: 1.0e6,      // 1 MHz coupling
            piezo_freq: 2.0 * std::f64::consts::PI * 1.0e9,
            piezo_voltage: 0.0,
            tonnetz_grid_size: 6,
            tonnetz_q: 10.0,
        }
    }
}

/// Results from one physics evaluation.
#[derive(Debug, Clone)]
pub struct PhysicsResult {
    /// Thermal phonon number.
    pub n_thermal: f64,
    /// Cooperativity parameter.
    pub cooperativity: f64,
    /// Final phonon occupation after cooling.
    pub n_final: f64,
    /// Tonnetz spectral gap λ₁.
    pub spectral_gap: f64,
    /// Total Tonnetz coupling weight.
    pub coupling_weight: f64,
    /// Tonnetz coherence enhancement factor.
    pub tonnetz_enhancement: f64,
    /// T₁ relaxation time (ns).
    pub t1_ns: f64,
    /// T₂ dephasing time (ns).
    pub t2_ns: f64,
    /// T₂ without Tonnetz filter (ns), for comparison.
    pub t2_bare_ns: f64,
}

/// Evaluate the full Doppler cooling + Tonnetz filter model.
pub fn evaluate(params: &PhysicsParams) -> PhysicsResult {
    // -- Thermal phonon occupation (Bose-Einstein) --
    let hw_over_kt = HBAR * params.omega_m / (K_B * params.temperature);
    let n_thermal = if hw_over_kt > 500.0 {
        0.0
    } else {
        1.0 / (hw_over_kt.exp() - 1.0)
    };

    // -- Optomechanical cooperativity --
    // C = 4 * n_photon * g0² / (kappa * gamma_m)
    // Simplified: laser_power acts as a proxy for intracavity photon number
    let gamma_m = params.omega_m / 1e6; // mechanical damping rate (Q~10^6)
    let kappa_hz = params.kappa * params.omega_m;
    let n_photon = params.laser_power * 1e-3 / (HBAR * params.omega_m * kappa_hz);
    let cooperativity = 4.0 * n_photon * params.g0 * params.g0 / (kappa_hz * gamma_m);

    // -- Sideband cooling --
    // Quantum backaction limit
    let n_ba = (kappa_hz / (4.0 * params.omega_m)).powi(2);
    let n_cooled = n_thermal / (1.0 + cooperativity) + n_ba;
    let n_final = n_cooled.max(n_ba);

    // -- Piezo enhancement --
    // Lorentzian response near mechanical resonance
    let delta_piezo = (params.piezo_freq - params.omega_m) / gamma_m;
    let piezo_lorentzian = 1.0 / (1.0 + delta_piezo * delta_piezo);
    let piezo_factor = 1.0 + params.piezo_voltage * 0.1 * piezo_lorentzian;

    // -- Tonnetz spectral gap filter --
    let spectral_gap = theoretical_decay_rate(params.tonnetz_grid_size);
    let n_qubits = params.tonnetz_grid_size * params.tonnetz_grid_size;
    let coupling_map = build_coupling_map(
        &CouplingTopology::Toroidal {
            grid_size: params.tonnetz_grid_size,
        },
        n_qubits,
    );
    let coupling_weight: f64 = coupling_map.iter().map(|&(_, _, w)| w).sum();

    // Enhancement: the Tonnetz filter suppresses dephasing noise by a factor
    // proportional to the inverse spectral gap (larger grid → smaller gap → more protection)
    // weighted by the total coupling strength and quality factor.
    // This replaces the JS fudge factor √(1 + harmonics * 0.1).
    let tonnetz_enhancement =
        1.0 + params.tonnetz_q * (coupling_weight / n_qubits as f64) * (1.0 / spectral_gap);

    // -- Decoherence rates (Bloch-Redfield) --
    // T₁ from optomechanical damping
    let gamma_opt = cooperativity * gamma_m; // optomechanical damping
    let t1 = piezo_factor / (gamma_m + gamma_opt); // seconds

    // Dephasing contributions
    let gamma_thermal = gamma_m * (2.0 * n_final + 1.0);
    let gamma_charge = 1e3; // charge noise ~1 kHz for CNT
    let gamma_magnetic = 1e2; // magnetic noise ~100 Hz

    let gamma_2_bare = 1.0 / (2.0 * t1) + gamma_thermal + gamma_charge + gamma_magnetic;
    let t2_bare = 1.0 / gamma_2_bare;

    // Tonnetz filter reduces dephasing (not T₁ relaxation)
    let gamma_2_filtered =
        1.0 / (2.0 * t1) + (gamma_thermal + gamma_charge + gamma_magnetic) / tonnetz_enhancement;
    let t2 = 1.0 / gamma_2_filtered;

    PhysicsResult {
        n_thermal,
        cooperativity,
        n_final,
        spectral_gap,
        coupling_weight,
        tonnetz_enhancement,
        t1_ns: t1 * 1e9,
        t2_ns: t2 * 1e9,
        t2_bare_ns: t2_bare * 1e9,
    }
}
