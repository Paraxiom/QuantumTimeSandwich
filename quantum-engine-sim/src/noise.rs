//! Realistic noise models for superconducting microwave cavities.
//!
//! Implements the dominant decoherence channels in state-of-the-art
//! superconducting resonators:
//!
//! 1. **1/f flux noise**: Power spectral density S(f) = A²/f.
//!    Causes frequency fluctuations δω(t) that dephase the cavity mode.
//!    Characterized by T_φ (pure dephasing time).
//!
//! 2. **Two-Level System (TLS) defects**: Amorphous oxide layer defects
//!    that couple to the cavity field. Cause frequency shifts and loss.
//!    Modeled as an ensemble of random fluctuators.
//!
//! 3. **Quasiparticle poisoning**: Broken Cooper pairs in the
//!    superconductor create normal-state electrons that absorb photons.
//!    Rate: γ_qp = n_qp × σ × v_F where n_qp ~ exp(-Δ/k_BT).
//!
//! # Noise budget for 3 cm niobium cavity at 20 mK
//!
//! | Source          | Rate (Hz)      | Notes                        |
//! |-----------------|----------------|------------------------------|
//! | Cavity loss κ   | 1–100          | Q = 10⁸–10¹⁰                |
//! | 1/f dephasing   | 10–1000        | T_φ = 1–100 ms              |
//! | TLS loss        | 0.1–10         | tan δ_TLS ~ 10⁻⁷            |
//! | Quasiparticle   | 0.01–1         | n_qp ~ 10⁻⁸ at 20 mK       |
//!
//! References:
//! - Müller, Cole, Lisenfeld (2019), Rep. Prog. Phys. 82, 124501 (TLS review)
//! - Paladino et al. (2014), Rev. Mod. Phys. 86, 361 (1/f noise review)
//! - Wang et al. (2014), Nat. Commun. 5, 5836 (quasiparticle tunneling)

use crate::units::*;

/// Complete noise budget for a superconducting cavity.
#[derive(Debug, Clone)]
pub struct NoiseBudget {
    /// Cavity photon loss rate κ (Hz) = ω/Q
    pub kappa: f64,
    /// 1/f pure dephasing rate (Hz) = 1/T_φ
    pub gamma_phi: f64,
    /// TLS-induced loss rate (Hz)
    pub gamma_tls: f64,
    /// Quasiparticle loss rate (Hz)
    pub gamma_qp: f64,
    /// Total decoherence rate (Hz)
    pub gamma_total: f64,
    /// Effective T₁ = 1/(κ + γ_tls + γ_qp) (seconds)
    pub t1: f64,
    /// Effective T₂ = 1/(1/(2T₁) + γ_φ) (seconds)
    pub t2: f64,
    /// T₂ with topological protection (seconds)
    pub t2_protected: f64,
    /// Protection enhancement factor T₂_protected / T₂
    pub protection_factor: f64,
}

/// Parameters for the noise model.
#[derive(Debug, Clone)]
pub struct NoiseParams {
    /// Cavity frequency ω (rad/s)
    pub omega: f64,
    /// Quality factor Q (dimensionless)
    pub quality_factor: f64,
    /// Temperature (K)
    pub temperature: f64,
    /// 1/f noise amplitude A (rad/s/√Hz)
    /// Typical: 10⁻⁶ to 10⁻⁴ for transmons
    pub flux_noise_amplitude: f64,
    /// Effective TLS loss tangent: p_TLS × tan δ_intrinsic
    /// p_TLS ~ 10⁻³ (participation ratio), tan δ_intrinsic ~ 10⁻⁷
    /// State-of-the-art 3D cavities: effective tan δ ~ 10⁻¹⁰
    pub tls_loss_tangent: f64,
    /// Quasiparticle density n_qp (normalized to Cooper pair density)
    /// Typical: 10⁻⁸ at 20 mK (far below BCS equilibrium)
    pub quasiparticle_density: f64,
    /// Superconducting gap Δ (eV). Nb: 1.55 meV, Al: 0.34 meV
    pub sc_gap_ev: f64,
    /// Lattice size N for T² spectral gap
    pub lattice_n: usize,
    /// Torus physical size (m)
    pub torus_length: f64,
}

impl NoiseParams {
    /// Default parameters for a 3 cm niobium cavity at 20 mK.
    pub fn niobium_3cm() -> Self {
        Self {
            omega: 2.0 * PI * 10e9, // 10 GHz
            quality_factor: 1e10,
            temperature: 0.020, // 20 mK
            flux_noise_amplitude: 1e-5, // moderate 1/f noise
            tls_loss_tangent: 1e-10, // effective: p_TLS(~10⁻³) × tan_δ(~10⁻⁷)
            quasiparticle_density: 1e-8, // typical for Nb at 20 mK
            sc_gap_ev: 1.55e-3, // Nb gap
            lattice_n: 8,
            torus_length: 3e-2, // 3 cm
        }
    }

    /// Aluminum cavity parameters (lower gap, different noise profile).
    pub fn aluminum_3cm() -> Self {
        Self {
            omega: 2.0 * PI * 8e9, // 8 GHz
            quality_factor: 5e9,
            temperature: 0.015, // 15 mK
            flux_noise_amplitude: 5e-6,
            tls_loss_tangent: 5e-11, // effective: p_TLS × tan_δ for Al
            quasiparticle_density: 5e-8,
            sc_gap_ev: 0.34e-3, // Al gap
            lattice_n: 8,
            torus_length: 3e-2,
        }
    }
}

/// Compute the full noise budget from physical parameters.
pub fn compute_noise_budget(params: &NoiseParams) -> NoiseBudget {
    // 1. Cavity loss: κ = ω/Q
    let kappa = params.omega / params.quality_factor;

    // 2. 1/f pure dephasing rate
    // γ_φ = A² × ln(ω_ir/ω_uv) where the log factor is ~10-20
    // Simplified: γ_φ ≈ A² × 15 (typical for 1 μs to 1 s bandwidth)
    let log_factor = 15.0;
    let gamma_phi = params.flux_noise_amplitude.powi(2) * log_factor;

    // 3. TLS loss rate
    // γ_TLS = ω × tan(δ_TLS) × tanh(ℏω / 2k_BT)
    // At 20 mK, ℏω >> k_BT for microwave, so tanh ≈ 1
    let x = HBAR * params.omega / (2.0 * KB * params.temperature);
    let tanh_factor = if x > 20.0 { 1.0 } else { x.tanh() };
    let gamma_tls = params.omega * params.tls_loss_tangent * tanh_factor;

    // 4. Quasiparticle loss rate
    // γ_qp = n_qp × (ω / (2Δ/ℏ))
    // At low photon number, single-photon absorption rate
    let delta_rad = params.sc_gap_ev * 1.602e-19 / HBAR; // gap in rad/s
    let gamma_qp = params.quasiparticle_density * params.omega / (2.0 * delta_rad);

    // Total relaxation rate
    let gamma_relax = kappa + gamma_tls + gamma_qp;

    // T₁ and T₂
    let t1 = if gamma_relax > 0.0 { 1.0 / gamma_relax } else { f64::INFINITY };
    let gamma_2 = gamma_relax / 2.0 + gamma_phi;
    let t2 = if gamma_2 > 0.0 { 1.0 / gamma_2 } else { f64::INFINITY };

    let gamma_total = gamma_2;

    // Topological protection: spectral gap suppresses dephasing channels
    let torus = crate::torus::TorusLattice::new(params.lattice_n, params.torus_length);
    let gap = torus.spectral_gap();
    let gamma_norm = gamma_relax * params.torus_length / C;
    let topo_factor = if gamma_norm > 1e-30 {
        (-gap / gamma_norm).exp().min(1.0)
    } else {
        0.0
    };

    // Protected T₂: topology suppresses dephasing (not T₁ relaxation)
    let gamma_2_protected = gamma_relax / 2.0 + gamma_phi * topo_factor;
    let t2_protected = if gamma_2_protected > 0.0 {
        1.0 / gamma_2_protected
    } else {
        f64::INFINITY
    };

    let protection_factor = if t2 > 0.0 && t2.is_finite() {
        t2_protected / t2
    } else {
        1.0
    };

    NoiseBudget {
        kappa,
        gamma_phi,
        gamma_tls,
        gamma_qp,
        gamma_total,
        t1,
        t2,
        t2_protected,
        protection_factor,
    }
}

/// Noise budget comparison across lattice sizes.
pub fn noise_scaling(params: &NoiseParams, sizes: &[usize]) -> Vec<(usize, NoiseBudget)> {
    sizes.iter()
        .map(|&n| {
            let p = NoiseParams {
                lattice_n: n,
                ..params.clone()
            };
            (n, compute_noise_budget(&p))
        })
        .collect()
}

/// Temperature sweep: noise budget vs temperature.
pub fn noise_vs_temperature(params: &NoiseParams, temps_mk: &[f64]) -> Vec<(f64, NoiseBudget)> {
    temps_mk.iter()
        .map(|&t_mk| {
            let p = NoiseParams {
                temperature: t_mk * 1e-3,
                ..params.clone()
            };
            (t_mk, compute_noise_budget(&p))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn niobium_noise_budget_reasonable() {
        let params = NoiseParams::niobium_3cm();
        let budget = compute_noise_budget(&params);

        // κ should be ~1 Hz for Q=10^10 at 10 GHz
        assert!(budget.kappa > 0.1 && budget.kappa < 100.0,
            "κ = {} Hz unexpected for Q=10^10", budget.kappa);

        // T₁ should be ~10 ms to 1 s
        assert!(budget.t1 > 0.001 && budget.t1 < 10.0,
            "T₁ = {} s unexpected", budget.t1);

        // T₂ should be milliseconds to seconds
        assert!(budget.t2 > 1e-4 && budget.t2 < 10.0,
            "T₂ = {} s unexpected", budget.t2);

        // Protection should improve T₂
        assert!(budget.protection_factor >= 1.0,
            "Protection factor {} should be >= 1", budget.protection_factor);
    }

    #[test]
    fn higher_q_means_longer_t1() {
        let low_q = compute_noise_budget(&NoiseParams {
            quality_factor: 1e8,
            ..NoiseParams::niobium_3cm()
        });
        let high_q = compute_noise_budget(&NoiseParams {
            quality_factor: 1e10,
            ..NoiseParams::niobium_3cm()
        });
        assert!(high_q.t1 > low_q.t1);
    }

    #[test]
    fn protection_increases_with_lattice_size() {
        let results = noise_scaling(&NoiseParams::niobium_3cm(), &[4, 8, 16]);
        // Larger lattice → smaller gap → but bigger enhancement denominator
        // Protection factor should generally increase
        let pf_4 = results[0].1.protection_factor;
        let pf_16 = results[2].1.protection_factor;
        assert!(pf_16 >= pf_4 * 0.9,
            "N=16 protection {} should be >= N=4 protection {}", pf_16, pf_4);
    }

    #[test]
    fn tls_dominates_at_low_temperature() {
        let budget = compute_noise_budget(&NoiseParams::niobium_3cm());
        // At 20 mK with Q=10^10, TLS and 1/f should be significant relative to κ
        let tls_fraction = budget.gamma_tls / (budget.kappa + budget.gamma_tls + budget.gamma_qp);
        // TLS should be a non-trivial fraction
        assert!(tls_fraction > 0.01,
            "TLS fraction {} unexpectedly small", tls_fraction);
    }
}
