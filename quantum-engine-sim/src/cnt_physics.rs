//! Doppler cooling physics + Tonnetz coherence filter.
//!
//! Ports the CNT optomechanical model from the toric-doppler-sim crate.
//! Uses Tonnetz spectral-gap enhancement for dephasing suppression.

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
    /// Laser power (mW).
    pub laser_power: f64,
    /// Laser detuning from resonance (units of omega_m).
    pub detuning: f64,
    /// Cavity linewidth / 2 (units of omega_m).
    pub kappa: f64,
    /// Piezo voltage (V).
    pub piezo_voltage: f64,
    /// Tonnetz grid size for spectral gap.
    pub tonnetz_grid_size: usize,
    /// Quality factor of the Tonnetz harmonic filter.
    pub tonnetz_q: f64,

    // ── CNT geometry parameters ──
    /// Nanotube length (nm). Typical: 300–5000 nm.
    pub cnt_length_nm: f64,
    /// Outer diameter (nm). SWCNT ~1–2 nm, MWCNT ~5–50 nm.
    pub cnt_diameter_nm: f64,
    /// Number of walls (1 = SWCNT, 2+ = MWCNT).
    pub num_walls: usize,
    /// Cavity finesse (determines cavity linewidth). Typical: 1e3–1e5.
    pub cavity_finesse: f64,
}

/// Young's modulus of CNT (Pa).
const CNT_YOUNGS_MODULUS: f64 = 1.0e12;
/// Graphite density (kg/m³).
const CNT_DENSITY: f64 = 2200.0;
/// Wall thickness of single graphene layer (m).
const WALL_THICKNESS: f64 = 0.34e-9;

impl PhysicsParams {
    /// Derive mechanical frequency omega_m (rad/s) from CNT geometry.
    ///
    /// Uses Euler-Bernoulli beam theory for clamped-clamped nanotube:
    /// f_m = (β₁²/2π) × √(EI / ρAL⁴) where β₁ = 4.730.
    pub fn omega_m(&self) -> f64 {
        let l = self.cnt_length_nm * 1e-9; // meters
        let d_outer = self.cnt_diameter_nm * 1e-9;
        let wall_total = WALL_THICKNESS * self.num_walls as f64;
        let d_inner = (d_outer - 2.0 * wall_total).max(0.0);

        // Second moment of area (hollow cylinder)
        let i_moment = std::f64::consts::PI / 64.0
            * (d_outer.powi(4) - d_inner.powi(4));
        // Cross-sectional area
        let area = std::f64::consts::PI / 4.0
            * (d_outer.powi(2) - d_inner.powi(2));

        if area < 1e-30 || l < 1e-12 {
            return 2.0 * std::f64::consts::PI * 1e9; // fallback 1 GHz
        }

        let beta1 = 4.730; // first mode, clamped-clamped
        beta1 * beta1 * (CNT_YOUNGS_MODULUS * i_moment / (CNT_DENSITY * area * l.powi(4))).sqrt()
    }

    /// Derive optomechanical coupling g₀ (Hz) from geometry.
    ///
    /// g₀ = G × x_zpf where G = ω_c/L_cav (cavity pull parameter)
    /// and x_zpf = √(ℏ / 2mω_m) is the zero-point motion.
    pub fn g0(&self) -> f64 {
        let l = self.cnt_length_nm * 1e-9;
        let d_outer = self.cnt_diameter_nm * 1e-9;
        let wall_total = WALL_THICKNESS * self.num_walls as f64;
        let d_inner = (d_outer - 2.0 * wall_total).max(0.0);
        let area = std::f64::consts::PI / 4.0
            * (d_outer.powi(2) - d_inner.powi(2));
        let mass = CNT_DENSITY * area * l;

        if mass < 1e-30 {
            return 1e6; // fallback 1 MHz
        }

        let omega = self.omega_m();
        let x_zpf = (HBAR / (2.0 * mass * omega)).sqrt();

        // Cavity pull: G ~ omega_cavity / L_cavity
        // Use optical cavity wavelength ~ 1064nm, L_cav ~ 100µm
        let omega_c = 2.0 * std::f64::consts::PI * 2.82e14; // 1064nm laser
        let l_cav = 100e-6; // 100 µm cavity
        let g_pull = omega_c / l_cav;

        g_pull * x_zpf
    }

    /// Mechanical quality factor derived from geometry.
    ///
    /// SWCNT: Q ~ 1e5–1e6, MWCNT: degrades with inter-wall friction.
    pub fn q_mech(&self) -> f64 {
        let base_q = 5e5;
        // Multi-wall friction reduces Q
        let wall_factor = 1.0 / (self.num_walls as f64).sqrt();
        // Longer tubes have lower clamping losses
        let length_factor = (self.cnt_length_nm / 1000.0).sqrt().clamp(0.3, 3.0);
        base_q * wall_factor * length_factor
    }

    /// Mechanical damping rate gamma_m (rad/s).
    pub fn gamma_m(&self) -> f64 {
        self.omega_m() / self.q_mech()
    }

    /// Cavity linewidth kappa (rad/s) from finesse.
    pub fn kappa_hz(&self) -> f64 {
        // κ = ω_m / (2F) scaled by the kappa slider
        self.kappa * self.omega_m()
    }

    /// Piezo frequency (matches mechanical resonance).
    pub fn piezo_freq(&self) -> f64 {
        self.omega_m()
    }
}

impl Default for PhysicsParams {
    fn default() -> Self {
        Self {
            temperature: 300.0,
            laser_power: 5.0,
            detuning: -1.0,
            kappa: 0.5,
            piezo_voltage: 0.0,
            tonnetz_grid_size: 6,
            tonnetz_q: 10.0,
            // Default: 1µm SWCNT, d=1.4nm
            cnt_length_nm: 1000.0,
            cnt_diameter_nm: 1.4,
            num_walls: 1,
            cavity_finesse: 10000.0,
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
    /// Piezo enhancement factor.
    #[allow(dead_code)]
    pub piezo_factor: f64,
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
    /// Derived mechanical frequency (GHz).
    pub freq_ghz: f64,
    /// Derived optomechanical coupling (kHz).
    pub g0_khz: f64,
    /// Derived mechanical Q factor.
    pub q_mech: f64,
}

/// Evaluate the full Doppler cooling + Tonnetz filter model.
pub fn evaluate(params: &PhysicsParams) -> PhysicsResult {
    // -- Derive physical quantities from CNT geometry --
    let omega_m = params.omega_m();
    let g0 = params.g0();
    let gamma_m = params.gamma_m();
    let kappa_hz = params.kappa_hz();
    let q_mech = params.q_mech();
    let freq_ghz = omega_m / (2.0 * std::f64::consts::PI * 1e9);
    let g0_khz = g0 / 1e3;

    // -- Thermal phonon occupation (Bose-Einstein) --
    let hw_over_kt = HBAR * omega_m / (K_B * params.temperature);
    let n_thermal = if hw_over_kt > 500.0 {
        0.0
    } else {
        1.0 / (hw_over_kt.exp() - 1.0)
    };

    // -- Optomechanical cooperativity --
    // C = 4 * n_photon * g0² / (kappa * gamma_m)
    let n_photon = params.laser_power * 1e-3 / (HBAR * omega_m * kappa_hz);
    let cooperativity = 4.0 * n_photon * g0 * g0 / (kappa_hz * gamma_m);

    // -- Sideband cooling --
    // Quantum backaction limit
    let n_ba = (kappa_hz / (4.0 * omega_m)).powi(2);
    let n_cooled = n_thermal / (1.0 + cooperativity) + n_ba;
    let n_final = n_cooled.max(n_ba);

    // -- Piezo enhancement --
    // Lorentzian response near mechanical resonance
    let piezo_freq = params.piezo_freq();
    let delta_piezo = (piezo_freq - omega_m) / gamma_m;
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
    let tonnetz_enhancement = 1.0
        + params.tonnetz_q
            * (coupling_weight / n_qubits as f64)
            * (1.0 / spectral_gap);

    // -- Decoherence rates (Bloch-Redfield) --
    // T₁ from optomechanical damping
    let gamma_opt = cooperativity * gamma_m;
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
        piezo_factor,
        spectral_gap,
        coupling_weight,
        tonnetz_enhancement,
        t1_ns: t1 * 1e9,
        t2_ns: t2 * 1e9,
        t2_bare_ns: t2_bare * 1e9,
        freq_ghz,
        g0_khz,
        q_mech,
    }
}
