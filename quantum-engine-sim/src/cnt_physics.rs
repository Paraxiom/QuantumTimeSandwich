//! Doppler cooling physics + Tonnetz coherence filter.
//!
//! Ports the CNT optomechanical model from the toric-doppler-sim crate.
//! Supports two resonator geometries:
//!
//! - **Nanotube**: clamped-clamped beam (Euler-Bernoulli theory).
//! - **Nanotorus**: toroidal ring with T² topology (Timoshenko ring theory).
//!   First observed by Martel et al. (1997). No clamping losses → Q ~ 10⁷–10⁸.
//!   Modes indexed by winding numbers (m,n) on T².
//!
//! Uses Tonnetz spectral-gap enhancement for dephasing suppression.

use tonnetz_coherence_sim::coherence::theoretical_decay_rate;
use tonnetz_coherence_sim::topology::{build_coupling_map, CouplingTopology};

/// Physical constants.
const HBAR: f64 = 1.054571817e-34; // J·s
const K_B: f64 = 1.380649e-23; // J/K

/// Resonator geometry type.
///
/// - `Nanotube`: A clamped-clamped carbon nanotube modeled as an Euler-Bernoulli
///   beam. Clamping at both ends introduces anchor losses that limit Q ~ 10⁵–10⁶.
/// - `Nanotorus`: A carbon nanotube bent into a ring (T² topology). Eliminates
///   clamping losses entirely, achieving Q ~ 10⁷–10⁸. Vibration modes are indexed
///   by winding numbers (m,n) on the torus, and the ring naturally couples to
///   whispering-gallery-mode (WGM) optical cavities with ~50× better geometric
///   overlap than tube-in-Fabry-Perot configurations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResonatorType {
    /// Clamped-clamped nanotube (Euler-Bernoulli beam).
    Nanotube,
    /// Toroidal nanotorus ring (Timoshenko ring theory, T² topology).
    Nanotorus,
}

/// Charge state for BN nanotubes. Affects Jahn-Teller distortion.
///
/// The second-order Jahn-Teller (SOJT) effect in charged BN nanotubes
/// breaks vibrational degeneracies, shifting phonon mode frequencies.
/// Neutral BN (BN⁰) is preferred for Tonnetz-tuned arrays as SOJT
/// distortion is minimized. See Monajjemi & Mollaamin (2024), Quantum Reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChargeState {
    /// Neutral — minimal Jahn-Teller distortion.
    Neutral,
    /// Cation (+1) — moderate SOJT distortion.
    Cation,
    /// Anion (-1) — moderate SOJT distortion.
    Anion,
}

impl ChargeState {
    /// Jahn-Teller Q-factor degradation multiplier.
    /// Neutral: no degradation. Charged: Q reduced by ~30%.
    pub fn jt_q_factor(self) -> f64 {
        match self {
            ChargeState::Neutral => 1.0,
            ChargeState::Cation => 0.7,
            ChargeState::Anion => 0.7,
        }
    }

    /// Phonon frequency shift factor from SOJT distortion.
    /// Charged states shift modes by ~5%, detuning Tonnetz harmonic ratios.
    pub fn jt_freq_shift(self) -> f64 {
        match self {
            ChargeState::Neutral => 1.0,
            ChargeState::Cation => 1.05,
            ChargeState::Anion => 0.95,
        }
    }

    /// Human-readable label.
    pub fn label(self) -> &'static str {
        match self {
            ChargeState::Neutral => "BN⁰",
            ChargeState::Cation => "BN⁺",
            ChargeState::Anion => "BN⁻",
        }
    }
}

/// Material type for the nanotube/nanotorus wall.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Material {
    /// Standard carbon nanotube — E=1.0 TPa, ρ=2200 kg/m³.
    Carbon,
    /// Boron nitride nanotube — E=0.8 TPa, ρ=2100, lower charge noise.
    BoronNitride,
    /// MoS₂ nanotube — E=0.27 TPa, ρ=5060, semiconducting.
    MoS2,
    /// Silicon carbide nanotube — E=0.45 TPa, ρ=3210, excellent thermal.
    SiliconCarbide,
}

impl Material {
    /// Young's modulus (Pa).
    pub fn youngs_modulus(self) -> f64 {
        match self {
            Material::Carbon => 1.0e12,
            Material::BoronNitride => 0.8e12,
            Material::MoS2 => 0.27e12,
            Material::SiliconCarbide => 0.45e12,
        }
    }

    /// Bulk density (kg/m³).
    pub fn density(self) -> f64 {
        match self {
            Material::Carbon => 2200.0,
            Material::BoronNitride => 2100.0,
            Material::MoS2 => 5060.0,
            Material::SiliconCarbide => 3210.0,
        }
    }

    /// Single-wall thickness (m).
    pub fn wall_thickness(self) -> f64 {
        match self {
            Material::Carbon => 0.34e-9,
            Material::BoronNitride => 0.33e-9,
            Material::MoS2 => 0.62e-9,
            Material::SiliconCarbide => 0.25e-9,
        }
    }

    /// Base mechanical Q for nanotube (clamping-limited).
    pub fn base_q_tube(self) -> f64 {
        match self {
            Material::Carbon => 5e5,
            Material::BoronNitride => 3e5,
            Material::MoS2 => 1e5,
            Material::SiliconCarbide => 8e5,
        }
    }

    /// Base mechanical Q for nanotorus (intrinsic only).
    pub fn base_q_torus(self) -> f64 {
        match self {
            Material::Carbon => 1e7,
            Material::BoronNitride => 6e6,
            Material::MoS2 => 2e6,
            Material::SiliconCarbide => 1.5e7,
        }
    }

    /// Geometric overlap factor for nanotube in Fabry-Perot cavity.
    pub fn eta_geo_tube(self) -> f64 {
        match self {
            Material::Carbon => 1e-5,
            Material::BoronNitride => 8e-6,
            Material::MoS2 => 5e-6,
            Material::SiliconCarbide => 1.2e-5,
        }
    }

    /// Geometric overlap factor for nanotorus in WGM cavity.
    pub fn eta_geo_torus(self) -> f64 {
        match self {
            Material::Carbon => 5e-4,
            Material::BoronNitride => 4e-4,
            Material::MoS2 => 2e-4,
            Material::SiliconCarbide => 6e-4,
        }
    }

    /// Charge noise dephasing rate (Hz).
    pub fn charge_noise_hz(self) -> f64 {
        match self {
            Material::Carbon => 1e3,
            Material::BoronNitride => 5e2,
            Material::MoS2 => 2e3,
            Material::SiliconCarbide => 3e2,
        }
    }

    /// Magnetic noise dephasing rate (Hz).
    pub fn magnetic_noise_hz(self) -> f64 {
        match self {
            Material::Carbon => 1e2,
            Material::BoronNitride => 1e2,
            Material::MoS2 => 3e2,
            Material::SiliconCarbide => 50.0,
        }
    }

    /// Human-readable label.
    pub fn label(self) -> &'static str {
        match self {
            Material::Carbon => "Carbon",
            Material::BoronNitride => "Boron Nitride",
            Material::MoS2 => "MoS\u{2082}",
            Material::SiliconCarbide => "Silicon Carbide",
        }
    }
}

/// Bundle geometry for multiple nanotori.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BundleGeometry {
    /// Single nanotorus (current behavior).
    Single,
    /// N nanotori in a linear chain, mechanically coupled end-to-end.
    Chain { count: usize },
    /// N nanotori arranged in a ring-of-rings (T² of T²).
    RingOfRings { count: usize },
    /// N concentric nanotori of increasing radius.
    Concentric { layers: usize },
    /// Two interlocked nanotori (Hopf link topology).
    HopfLink,
}

impl BundleGeometry {
    /// Number of individual nanotori in the bundle.
    pub fn n_resonators(&self) -> usize {
        match *self {
            BundleGeometry::Single => 1,
            BundleGeometry::Chain { count } => count,
            BundleGeometry::RingOfRings { count } => count,
            BundleGeometry::Concentric { layers } => layers,
            BundleGeometry::HopfLink => 2,
        }
    }

    /// Mass multiplier relative to a single torus.
    pub fn mass_factor(&self) -> f64 {
        match *self {
            BundleGeometry::Single => 1.0,
            BundleGeometry::Chain { count } => count as f64,
            BundleGeometry::RingOfRings { count } => count as f64,
            BundleGeometry::Concentric { layers } => {
                // Sum of radii ratios: 1 + 2 + 3 + ... + layers
                (1..=layers).map(|i| i as f64).sum()
            }
            BundleGeometry::HopfLink => 2.0,
        }
    }

    /// Cooperative Q enhancement from collective modes.
    pub fn cooperative_q_factor(&self) -> f64 {
        match *self {
            BundleGeometry::Single => 1.0,
            BundleGeometry::Chain { count } => (count as f64).sqrt(), // phased modes
            BundleGeometry::RingOfRings { count } => count as f64,   // full phase matching
            BundleGeometry::Concentric { layers } => layers as f64 * 0.8,
            BundleGeometry::HopfLink => 1.5, // strong coupling
        }
    }

    /// Human-readable label.
    pub fn label(&self) -> &'static str {
        match *self {
            BundleGeometry::Single => "Single",
            BundleGeometry::Chain { .. } => "Chain",
            BundleGeometry::RingOfRings { .. } => "Ring of Rings",
            BundleGeometry::Concentric { .. } => "Concentric",
            BundleGeometry::HopfLink => "Hopf Link",
        }
    }
}

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

    // ── Resonator geometry ──
    /// Resonator geometry: clamped nanotube or toroidal ring.
    pub resonator_type: ResonatorType,
    /// Nanotube length (nm). Typical: 300–5000 nm. Only used for Nanotube.
    pub cnt_length_nm: f64,
    /// Outer diameter (nm). SWCNT ~1–2 nm, MWCNT ~5–50 nm.
    pub cnt_diameter_nm: f64,
    /// Number of walls (1 = SWCNT, 2+ = MWCNT).
    pub num_walls: usize,
    /// Cavity finesse (determines cavity linewidth). Typical: 1e3–1e5.
    pub cavity_finesse: f64,
    /// Ring major diameter (nm). Only used for Nanotorus. Typical: 50–500 nm.
    pub ring_diameter_nm: f64,
    /// Wall material (Carbon, BN, MoS₂, SiC).
    pub material: Material,
    /// Charge state for BN nanotubes (Jahn-Teller effect). Ignored for non-BN materials.
    pub bn_charge_state: ChargeState,
    /// Bundle geometry for nanotorus arrays.
    pub bundle_geometry: BundleGeometry,
}

// Material-specific constants are now in `Material` methods.
// Former constants CNT_YOUNGS_MODULUS, CNT_DENSITY, WALL_THICKNESS are replaced
// by self.material.youngs_modulus(), self.material.density(), self.material.wall_thickness().

impl PhysicsParams {
    /// Cross-section geometry: outer/inner diameters, second moment of area, area.
    fn cross_section(&self) -> (f64, f64, f64, f64) {
        let d_outer = self.cnt_diameter_nm * 1e-9;
        let wall_total = self.material.wall_thickness() * self.num_walls as f64;
        let d_inner = (d_outer - 2.0 * wall_total).max(0.0);
        let i_moment = std::f64::consts::PI / 64.0
            * (d_outer.powi(4) - d_inner.powi(4));
        let area = std::f64::consts::PI / 4.0
            * (d_outer.powi(2) - d_inner.powi(2));
        (d_outer, d_inner, i_moment, area)
    }

    /// Derive mechanical frequency omega_m (rad/s) from resonator geometry.
    ///
    /// **Nanotube** (Euler-Bernoulli clamped-clamped beam):
    /// ω = β₁² × √(EI / ρAL⁴), where β₁ = 4.730 (first mode).
    ///
    /// **Nanotorus** (Timoshenko in-plane bending of a thin ring):
    /// ω_m = m(m²−1)/√(m²+1) × √(EI / ρAR⁴), where m=2 is the lowest
    /// non-rigid bending mode. Coefficient = 6/√5 ≈ 2.683.
    /// Reference: Love, "A Treatise on the Mathematical Theory of Elasticity" (1927).
    pub fn omega_m(&self) -> f64 {
        let (_d_outer, _d_inner, i_moment, area) = self.cross_section();

        if area < 1e-30 {
            return 2.0 * std::f64::consts::PI * 1e9; // fallback 1 GHz
        }

        // Jahn-Teller frequency shift (only affects BN)
        let jt_shift = if self.material == Material::BoronNitride {
            self.bn_charge_state.jt_freq_shift()
        } else {
            1.0
        };

        match self.resonator_type {
            ResonatorType::Nanotube => {
                let l = self.cnt_length_nm * 1e-9;
                if l < 1e-12 {
                    return 2.0 * std::f64::consts::PI * 1e9;
                }
                let beta1 = 4.730; // first mode, clamped-clamped
                jt_shift * beta1 * beta1
                    * (self.material.youngs_modulus() * i_moment
                        / (self.material.density() * area * l.powi(4)))
                    .sqrt()
            }
            ResonatorType::Nanotorus => {
                let r = (self.ring_diameter_nm / 2.0) * 1e-9; // major radius in meters
                if r < 1e-12 {
                    return 2.0 * std::f64::consts::PI * 1e9;
                }
                // m=2 lowest non-rigid bending mode: coeff = 2(4-1)/√(4+1) = 6/√5
                let coeff = 6.0 / 5.0_f64.sqrt(); // ≈ 2.683
                jt_shift * coeff
                    * (self.material.youngs_modulus() * i_moment
                        / (self.material.density() * area * r.powi(4)))
                    .sqrt()
            }
        }
    }

    /// Derive optomechanical coupling g₀ (Hz) from geometry.
    ///
    /// g₀ = G_eff × x_zpf where G_eff = (ω_c/L_cav) × η_geo.
    ///
    /// **Nanotube**: η_geo ~ 10⁻⁵ (tube in Fabry-Perot cavity).
    /// **Nanotorus**: η_geo ~ 5×10⁻⁴ (ring mode naturally matches WGM cavity
    /// mode profile, ~50× better geometric overlap). Scales with √(finesse/10⁴).
    pub fn g0(&self) -> f64 {
        let (_d_outer, _d_inner, _i_moment, area) = self.cross_section();

        let single_mass = match self.resonator_type {
            ResonatorType::Nanotube => {
                let l = self.cnt_length_nm * 1e-9;
                self.material.density() * area * l
            }
            ResonatorType::Nanotorus => {
                let r = (self.ring_diameter_nm / 2.0) * 1e-9;
                self.material.density() * area * 2.0 * std::f64::consts::PI * r
            }
        };

        // Bundle mass: for collective modes the effective mass scales with n_resonators
        let mass = single_mass * self.bundle_geometry.mass_factor();

        if mass < 1e-30 {
            return 1e3; // fallback 1 kHz
        }

        let omega = self.omega_m();
        let x_zpf = (HBAR / (2.0 * mass * omega)).sqrt();

        // Collective enhancement: g0_collective = g0_single × √N for phase-matched modes
        let n_res = self.bundle_geometry.n_resonators() as f64;
        let collective_factor = n_res.sqrt();

        // Cavity pull with geometric overlap factor
        let omega_c = 2.0 * std::f64::consts::PI * 2.82e14; // 1064nm laser
        let l_cav = 100e-6; // 100 µm microcavity

        let eta_geo_base = match self.resonator_type {
            ResonatorType::Nanotube => self.material.eta_geo_tube(),
            ResonatorType::Nanotorus => self.material.eta_geo_torus(),
        };
        let eta_geo = eta_geo_base * (self.cavity_finesse / 1e4).sqrt();
        let g_eff = omega_c / l_cav * eta_geo;

        g_eff * x_zpf * collective_factor
    }

    /// Mechanical quality factor derived from geometry.
    ///
    /// **Nanotube**: Q ~ 5×10⁵ × wall_factor × length_factor (clamping-limited).
    /// **Nanotorus**: Q ~ 1×10⁷ × wall_factor (no clamping points — intrinsic
    /// dissipation only). Multi-wall friction still degrades Q for both types.
    pub fn q_mech(&self) -> f64 {
        let wall_factor = 1.0 / (self.num_walls as f64).sqrt();

        // Jahn-Teller Q degradation (only affects BN)
        let jt_q = if self.material == Material::BoronNitride {
            self.bn_charge_state.jt_q_factor()
        } else {
            1.0
        };

        match self.resonator_type {
            ResonatorType::Nanotube => {
                let base_q = self.material.base_q_tube();
                let length_factor =
                    (self.cnt_length_nm / 1000.0).sqrt().clamp(0.3, 3.0);
                base_q * wall_factor * length_factor * jt_q
            }
            ResonatorType::Nanotorus => {
                // No clamping losses → intrinsic Q is ~20× higher
                let base_q = self.material.base_q_torus();
                base_q * wall_factor * self.bundle_geometry.cooperative_q_factor() * jt_q
            }
        }
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

    /// Mechanical spectral gap: ratio of 2nd to 1st mode frequency.
    ///
    /// This quantifies the frequency separation between the fundamental and
    /// next bending mode — analogous to the Tonnetz mathematical spectral gap.
    ///
    /// **Nanotube**: ω₂/ω₁ = (β₂/β₁)² = (7.853/4.730)² ≈ 2.757
    /// **Nanotorus**: ω₃/ω₂ = [3(9−1)/√10] / [2(4−1)/√5]
    ///              = [24/√10] / [6/√5] ≈ 2.83
    ///   where m=2,3 are the lowest non-rigid ring modes.
    pub fn mech_spectral_gap(&self) -> f64 {
        match self.resonator_type {
            ResonatorType::Nanotube => {
                // (β₂/β₁)² for clamped-clamped beam
                let beta1: f64 = 4.730;
                let beta2: f64 = 7.853;
                (beta2 / beta1).powi(2)
            }
            ResonatorType::Nanotorus => {
                // ω_m = m(m²−1)/√(m²+1) × const
                // ratio ω₃/ω₂:
                let omega_2_coeff = 2.0 * 3.0 / 5.0_f64.sqrt(); // 6/√5
                let omega_3_coeff = 3.0 * 8.0 / 10.0_f64.sqrt(); // 24/√10
                omega_3_coeff / omega_2_coeff
            }
        }
    }

    /// Human-readable label for the active resonator type.
    pub fn resonator_label(&self) -> &'static str {
        match self.resonator_type {
            ResonatorType::Nanotube => "CNT RESONATOR",
            ResonatorType::Nanotorus => "NANOTORUS",
        }
    }
}

impl PhysicsParams {
    /// Optimal nanotorus preset: cryo SWCNT ring, high finesse, strong Tonnetz.
    pub fn nanotorus_default() -> Self {
        Self {
            resonator_type: ResonatorType::Nanotorus,
            ring_diameter_nm: 200.0,
            cnt_diameter_nm: 1.4,
            num_walls: 1,
            cavity_finesse: 50000.0,
            temperature: 0.020,
            laser_power: 20.0,
            detuning: -1.0,
            kappa: 0.5,
            piezo_voltage: 5.0,
            tonnetz_grid_size: 12,
            tonnetz_q: 100.0,
            cnt_length_nm: 1000.0, // unused for nanotorus but must be set
            material: Material::Carbon,
            bn_charge_state: ChargeState::Neutral,
            bundle_geometry: BundleGeometry::Single,
        }
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
            resonator_type: ResonatorType::Nanotube,
            // Default: 1µm SWCNT, d=1.4nm
            cnt_length_nm: 1000.0,
            cnt_diameter_nm: 1.4,
            num_walls: 1,
            cavity_finesse: 10000.0,
            ring_diameter_nm: 200.0,
            material: Material::Carbon,
            bn_charge_state: ChargeState::Neutral,
            bundle_geometry: BundleGeometry::Single,
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
    /// Resonator type label for display.
    pub resonator_label: &'static str,
    /// Mechanical spectral gap (ratio of 2nd to 1st mode frequency).
    /// Analogous to the Tonnetz mathematical spectral gap.
    pub mech_spectral_gap: f64,
}

/// Build coupling map for a bundle of nanotori on a Tonnetz grid.
///
/// Each nanotorus gets its own toroidal sub-lattice of size `grid_size²`.
/// Inter-torus edges are added according to the bundle topology.
fn build_bundle_coupling_map(
    bundle: &BundleGeometry,
    grid_size: usize,
) -> (Vec<(usize, usize, f64)>, usize) {
    let sub_n = grid_size * grid_size;
    match *bundle {
        BundleGeometry::Single => {
            let map = build_coupling_map(
                &CouplingTopology::Toroidal { grid_size },
                sub_n,
            );
            (map, sub_n)
        }
        BundleGeometry::Chain { count } | BundleGeometry::RingOfRings { count } => {
            let total = count * sub_n;
            let mut edges = Vec::new();
            // Build each sub-lattice with offset indices
            for t in 0..count {
                let offset = t * sub_n;
                let sub_map = build_coupling_map(
                    &CouplingTopology::Toroidal { grid_size },
                    sub_n,
                );
                for (a, b, w) in sub_map {
                    edges.push((a + offset, b + offset, w));
                }
            }
            // Compute base nearest-neighbor weight from the sub-lattice
            let base_w = edges.first().map(|&(_, _, w)| w).unwrap_or(1.0);
            let inter_w = 0.5 * base_w;
            // Inter-torus coupling: adjacent tori share boundary edges
            let wrap = matches!(*bundle, BundleGeometry::RingOfRings { .. });
            for t in 0..(count - 1) {
                let off_a = t * sub_n;
                let off_b = (t + 1) * sub_n;
                // Couple corresponding boundary qubits (last row ↔ first row)
                for col in 0..grid_size {
                    let a = off_a + (grid_size - 1) * grid_size + col;
                    let b = off_b + col;
                    edges.push((a, b, inter_w));
                }
            }
            if wrap && count > 2 {
                let off_a = (count - 1) * sub_n;
                let off_b = 0;
                for col in 0..grid_size {
                    let a = off_a + (grid_size - 1) * grid_size + col;
                    let b = off_b + col;
                    edges.push((a, b, inter_w));
                }
            }
            (edges, total)
        }
        BundleGeometry::Concentric { layers } => {
            let total = layers * sub_n;
            let mut edges = Vec::new();
            for t in 0..layers {
                let offset = t * sub_n;
                let sub_map = build_coupling_map(
                    &CouplingTopology::Toroidal { grid_size },
                    sub_n,
                );
                for (a, b, w) in sub_map {
                    edges.push((a + offset, b + offset, w));
                }
            }
            let base_w = edges.first().map(|&(_, _, w)| w).unwrap_or(1.0);
            // All-to-all inter-torus coupling with exponential decay
            for i in 0..layers {
                for j in (i + 1)..layers {
                    let w = base_w * (-(( j - i) as f64)).exp();
                    for q in 0..grid_size {
                        let a = i * sub_n + q;
                        let b = j * sub_n + q;
                        edges.push((a, b, w));
                    }
                }
            }
            (edges, total)
        }
        BundleGeometry::HopfLink => {
            let total = 2 * sub_n;
            let mut edges = Vec::new();
            for t in 0..2 {
                let offset = t * sub_n;
                let sub_map = build_coupling_map(
                    &CouplingTopology::Toroidal { grid_size },
                    sub_n,
                );
                for (a, b, w) in sub_map {
                    edges.push((a + offset, b + offset, w));
                }
            }
            let base_w = edges.first().map(|&(_, _, w)| w).unwrap_or(1.0);
            // Strong cross-coupling between corresponding qubit pairs
            let cross_w = 0.8 * base_w;
            for q in 0..sub_n {
                edges.push((q, q + sub_n, cross_w));
            }
            (edges, total)
        }
    }
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
    let resonator_label = params.resonator_label();
    let mech_spectral_gap = params.mech_spectral_gap();

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
    let n_base = params.tonnetz_grid_size * params.tonnetz_grid_size;
    let (coupling_map, n_qubits) = if params.resonator_type == ResonatorType::Nanotorus {
        build_bundle_coupling_map(&params.bundle_geometry, params.tonnetz_grid_size)
    } else {
        (build_coupling_map(
            &CouplingTopology::Toroidal {
                grid_size: params.tonnetz_grid_size,
            },
            n_base,
        ), n_base)
    };
    let coupling_weight: f64 = coupling_map.iter().map(|&(_, _, w)| w).sum();

    // Enhancement: the Tonnetz filter suppresses dephasing noise by a factor
    // proportional to the inverse spectral gap (larger grid → smaller gap → more protection)
    // weighted by the total coupling strength and quality factor.
    let tonnetz_enhancement = 1.0
        + params.tonnetz_q
            * (coupling_weight / n_qubits as f64)
            * (1.0 / spectral_gap);

    // -- Decoherence rates (geometric thermodynamics picture) --
    //
    // Cooperativity C acts as a curvature parameter on the optomechanical state
    // manifold (cf. McGinty, "Geometric Thermodynamics", 2026). When C → ∞ the
    // bare-state metric becomes singular — a geometric phase transition to the
    // dressed-state (strong coupling) regime.
    //
    // The qubit is encoded in the Fock states |0⟩,|1⟩ of the *cooled* mechanical
    // mode.  Optomechanical cooling reduces n_final (beneficial) but the qubit T₁
    // depends on phonon transition rates in the cooled state, not on the optical
    // damping rate γ_m(1+C).
    //
    // T₁ = 1 / [γ_m × (n_final + 1)]   (downward transition |1⟩→|0⟩ dominates
    //                                     near ground state)
    // T_φ = charge + magnetic + thermal dephasing (pure phase noise)
    // T₂ = 1 / [1/(2T₁) + γ_φ]         (Bloch-Redfield)
    //
    // The Tonnetz spectral gap λ₁ (curvature of T²) bounds the dephasing
    // suppression — the geometric invariant that protects coherence.

    // Qubit T₁: energy relaxation of the cooled mechanical mode
    let gamma_1 = gamma_m * (n_final + 1.0);
    let t1 = piezo_factor / gamma_1; // seconds

    // Pure dephasing contributions (phase-randomizing noise channels)
    let gamma_charge = params.material.charge_noise_hz();
    let gamma_magnetic = params.material.magnetic_noise_hz();
    // Residual thermal dephasing from phonon number fluctuations
    let gamma_thermal_phi = gamma_m * n_final;

    let gamma_phi = gamma_thermal_phi + gamma_charge + gamma_magnetic;
    let gamma_2_bare = 1.0 / (2.0 * t1) + gamma_phi;
    let t2_bare = 1.0 / gamma_2_bare;

    // Tonnetz filter reduces pure dephasing (not T₁ relaxation)
    let gamma_2_filtered = 1.0 / (2.0 * t1) + gamma_phi / tonnetz_enhancement;
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
        resonator_label,
        mech_spectral_gap,
    }
}

#[cfg(test)]
mod numerical_results {
    use super::*;

    #[test]
    fn print_nanotorus_vs_tube_results() {
        // ── Nanotorus (optimal cryo preset) ──
        let nt_params = PhysicsParams::nanotorus_default();
        let nt = evaluate(&nt_params);

        // ── Nanotube (default: 1µm SWCNT at 300 K) ──
        let tb_params = PhysicsParams::default();
        let tb = evaluate(&tb_params);

        println!("\n{}", "=".repeat(80));
        println!("  CNT NANOTORUS vs NANOTUBE — FULL PHYSICS RESULTS");
        println!("{}", "=".repeat(80));

        println!("{:<35} {:>20} {:>20}", "PARAMETER", "NANOTORUS", "NANOTUBE");
        println!("{:-<35} {:->20} {:->20}", "", "", "");
        println!("{:<35} {:>20} {:>20}", "Resonator type", nt.resonator_label, tb.resonator_label);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Frequency (GHz)", nt.freq_ghz, tb.freq_ghz);
        println!("{:<35} {:>20.6e} {:>20.6e}", "g0 coupling (kHz)", nt.g0_khz, tb.g0_khz);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Q mechanical", nt.q_mech, tb.q_mech);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Mech spectral gap (omega2/omega1)", nt.mech_spectral_gap, tb.mech_spectral_gap);
        println!("{:<35} {:>20.6e} {:>20.6e}", "n_thermal (phonons)", nt.n_thermal, tb.n_thermal);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Cooperativity C", nt.cooperativity, tb.cooperativity);
        println!("{:<35} {:>20.6e} {:>20.6e}", "n_final (cooled phonons)", nt.n_final, tb.n_final);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Piezo factor", nt.piezo_factor, tb.piezo_factor);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Tonnetz spectral gap lambda_1", nt.spectral_gap, tb.spectral_gap);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Coupling weight", nt.coupling_weight, tb.coupling_weight);
        println!("{:<35} {:>20.6e} {:>20.6e}", "Tonnetz enhancement", nt.tonnetz_enhancement, tb.tonnetz_enhancement);
        println!("{:<35} {:>20.6e} {:>20.6e}", "T1 (ns)", nt.t1_ns, tb.t1_ns);
        println!("{:<35} {:>20.6e} {:>20.6e}", "T2 bare (ns)", nt.t2_bare_ns, tb.t2_bare_ns);
        println!("{:<35} {:>20.6e} {:>20.6e}", "T2 with Tonnetz (ns)", nt.t2_ns, tb.t2_ns);
        println!("{:<35} {:>20.6e} {:>20.6e}", "T2 enhancement (T2/T2_bare)", nt.t2_ns / nt.t2_bare_ns, tb.t2_ns / tb.t2_bare_ns);
        println!("\n{}", "=".repeat(80));

        // Also print intermediate params for full traceability
        println!("\n  INTERMEDIATE DERIVED QUANTITIES");
        println!("{:-<75}", "");
        println!("{:<35} {:>20.6e} {:>20.6e}", "omega_m (rad/s)", nt_params.omega_m(), tb_params.omega_m());
        println!("{:<35} {:>20.6e} {:>20.6e}", "g0 raw (Hz)", nt_params.g0(), tb_params.g0());
        println!("{:<35} {:>20.6e} {:>20.6e}", "gamma_m (rad/s)", nt_params.gamma_m(), tb_params.gamma_m());
        println!("{:<35} {:>20.6e} {:>20.6e}", "kappa_hz (rad/s)", nt_params.kappa_hz(), tb_params.kappa_hz());
        println!("{:<35} {:>20.6e} {:>20.6e}", "Q mech", nt_params.q_mech(), tb_params.q_mech());
    }

    #[test]
    fn print_bn_charge_state_comparison() {
        println!("\n{}", "=".repeat(90));
        println!("  BORON NITRIDE CHARGE STATE COMPARISON — JAHN-TELLER EFFECT");
        println!("{}", "=".repeat(90));

        let states = [ChargeState::Neutral, ChargeState::Cation, ChargeState::Anion];

        println!("{:<30} {:>18} {:>18} {:>18}", "PARAMETER", "BN⁰ (Neutral)", "BN⁺ (Cation)", "BN⁻ (Anion)");
        println!("{:-<30} {:->18} {:->18} {:->18}", "", "", "", "");

        let mut results = Vec::new();
        for &cs in &states {
            let params = PhysicsParams {
                material: Material::BoronNitride,
                bn_charge_state: cs,
                ..PhysicsParams::nanotorus_default()
            };
            let r = evaluate(&params);
            results.push((params, r));
        }

        let labels = ["BN⁰", "BN⁺", "BN⁻"];
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "Frequency (GHz)",
            results[0].1.freq_ghz, results[1].1.freq_ghz, results[2].1.freq_ghz);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "Q mechanical",
            results[0].1.q_mech, results[1].1.q_mech, results[2].1.q_mech);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "g0 coupling (kHz)",
            results[0].1.g0_khz, results[1].1.g0_khz, results[2].1.g0_khz);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "Cooperativity C",
            results[0].1.cooperativity, results[1].1.cooperativity, results[2].1.cooperativity);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "T1 (ns)",
            results[0].1.t1_ns, results[1].1.t1_ns, results[2].1.t1_ns);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "T2 bare (ns)",
            results[0].1.t2_bare_ns, results[1].1.t2_bare_ns, results[2].1.t2_bare_ns);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "T2 Tonnetz (ns)",
            results[0].1.t2_ns, results[1].1.t2_ns, results[2].1.t2_ns);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "T2 enhancement",
            results[0].1.t2_ns / results[0].1.t2_bare_ns,
            results[1].1.t2_ns / results[1].1.t2_bare_ns,
            results[2].1.t2_ns / results[2].1.t2_bare_ns);
        println!("{:<30} {:>18.4e} {:>18.4e} {:>18.4e}", "Tonnetz enhancement",
            results[0].1.tonnetz_enhancement, results[1].1.tonnetz_enhancement, results[2].1.tonnetz_enhancement);

        println!("\n  VERDICT: BN⁰ T2 = {:.2} ns vs BN⁺ T2 = {:.2} ns ({:.1}% longer)",
            results[0].1.t2_ns, results[1].1.t2_ns,
            (results[0].1.t2_ns / results[1].1.t2_ns - 1.0) * 100.0);

        println!("{}", "=".repeat(90));

        // Assert neutral BN has strictly better coherence
        assert!(results[0].1.t2_ns > results[1].1.t2_ns, "Neutral BN should have longer T2 than Cation");
        assert!(results[0].1.t2_ns > results[2].1.t2_ns, "Neutral BN should have longer T2 than Anion");
        assert!(results[0].1.q_mech > results[1].1.q_mech, "Neutral BN should have higher Q than Cation");
    }
}
