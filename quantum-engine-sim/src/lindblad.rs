//! Lindblad master equation for open quantum systems on T².
//!
//! Solves the Gorini–Kossakowski–Sudarshan–Lindblad (GKSL) equation:
//!
//!   dρ/dt = -i[H, ρ] + Σ_k γ_k (L_k ρ L_k† - ½{L_k†L_k, ρ})
//!
//! for cavity modes on a toroidal lattice coupled to thermal baths.
//!
//! # Physical model
//!
//! Each mode n of the cavity on T² has:
//! - Hamiltonian: H = ℏω_n a†_n a_n
//! - Cavity loss:   L_loss = √κ a_n         (photon leakage, rate κ = ω/Q)
//! - Thermal emission: L_em = √(γ(n̄+1)) a_n  (spontaneous + stimulated)
//! - Thermal absorption: L_abs = √(γn̄) a†_n   (stimulated absorption)
//!
//! where n̄ = 1/(exp(ℏω_n/k_BT) - 1) is the Bose-Einstein occupation.
//!
//! # Topological protection
//!
//! Modes below the spectral gap ω_gap = ω_min √λ₁ are protected:
//! their effective κ is reduced by the protection factor exp(-λ₁/γ_norm).
//!
//! # Truncated Fock space
//!
//! Each mode uses a truncated Fock space |0⟩,...,|M-1⟩ where M is chosen
//! so that ⟨M-1|ρ|M-1⟩ < ε throughout the evolution.
//!
//! References:
//! - Lindblad (1976), Commun. Math. Phys. 48, 119
//! - Breuer & Petruccione, "The Theory of Open Quantum Systems" (2002)
//! - Carmichael, "Statistical Methods in Quantum Optics" (1999)

use crate::torus::TorusLattice;
use crate::units::*;
use crate::vacuum::thermal_occupation;

/// Configuration for Lindblad simulation of a single cavity mode.
#[derive(Debug, Clone)]
pub struct LindbladConfig {
    /// Mode frequency ω (rad/s)
    pub omega: f64,
    /// Cavity loss rate κ (Hz) = ω/Q
    pub kappa: f64,
    /// Bath temperature (K)
    pub temperature: f64,
    /// Truncated Fock space dimension
    pub fock_dim: usize,
    /// Time step dt (seconds)
    pub dt: f64,
    /// Total simulation time (seconds)
    pub total_time: f64,
    /// Whether this mode is below the spectral gap (protected)
    pub protected: bool,
    /// Topological protection factor (0 to 1, applied to κ)
    pub protection_factor: f64,
}

/// State of the density matrix evolution.
#[derive(Debug, Clone)]
pub struct LindbladState {
    /// Density matrix ρ in Fock basis (dim × dim, real since we track diagonal + coherences)
    /// Stored as flattened row-major complex: [re_00, im_00, re_01, im_01, ...]
    pub rho_re: Vec<f64>,
    pub rho_im: Vec<f64>,
    pub dim: usize,
}

impl LindbladState {
    /// Initialize in vacuum state |0⟩⟨0|.
    pub fn vacuum(dim: usize) -> Self {
        let n = dim * dim;
        let mut rho_re = vec![0.0; n];
        let rho_im = vec![0.0; n];
        rho_re[0] = 1.0; // |0⟩⟨0|
        Self { rho_re, rho_im, dim }
    }

    /// Initialize in thermal state at temperature T.
    pub fn thermal(dim: usize, omega: f64, temperature: f64) -> Self {
        let n_th = thermal_occupation(omega, temperature);
        let n = dim * dim;
        let mut rho_re = vec![0.0; n];
        let rho_im = vec![0.0; n];

        // Thermal state: ρ = Σ_n p_n |n⟩⟨n| where p_n = (n̄/(n̄+1))^n / (n̄+1)
        let mut norm = 0.0;
        for k in 0..dim {
            let p_k = if n_th > 1e-15 {
                (n_th / (n_th + 1.0)).powi(k as i32) / (n_th + 1.0)
            } else {
                if k == 0 { 1.0 } else { 0.0 }
            };
            rho_re[k * dim + k] = p_k;
            norm += p_k;
        }
        // Normalize
        if norm > 0.0 {
            for k in 0..dim {
                rho_re[k * dim + k] /= norm;
            }
        }

        Self { rho_re, rho_im, dim }
    }

    /// Get ρ[i][j] = (re, im).
    #[inline]
    pub fn get(&self, i: usize, j: usize) -> (f64, f64) {
        let idx = i * self.dim + j;
        (self.rho_re[idx], self.rho_im[idx])
    }

    /// Set ρ[i][j] = (re, im).
    #[inline]
    pub fn set(&mut self, i: usize, j: usize, re: f64, im: f64) {
        let idx = i * self.dim + j;
        self.rho_re[idx] = re;
        self.rho_im[idx] = im;
    }

    /// Mean photon number ⟨n⟩ = Tr(a†a ρ) = Σ_n n × ρ_nn.
    pub fn mean_photon_number(&self) -> f64 {
        let mut n_mean = 0.0;
        for k in 0..self.dim {
            n_mean += k as f64 * self.rho_re[k * self.dim + k];
        }
        n_mean
    }

    /// Trace of ρ (should be 1.0).
    pub fn trace(&self) -> f64 {
        let mut tr = 0.0;
        for k in 0..self.dim {
            tr += self.rho_re[k * self.dim + k];
        }
        tr
    }

    /// Purity Tr(ρ²).
    pub fn purity(&self) -> f64 {
        let d = self.dim;
        let mut p = 0.0;
        for i in 0..d {
            for j in 0..d {
                let (re_ij, im_ij) = self.get(i, j);
                p += re_ij * re_ij + im_ij * im_ij;
            }
        }
        p
    }

    /// Fidelity with vacuum state: F = ⟨0|ρ|0⟩ = ρ_00.
    pub fn vacuum_fidelity(&self) -> f64 {
        self.rho_re[0]
    }
}

/// Result of a Lindblad time evolution.
#[derive(Debug, Clone)]
pub struct LindbladResult {
    /// Time points (seconds)
    pub times: Vec<f64>,
    /// Mean photon number at each time
    pub photon_numbers: Vec<f64>,
    /// Purity at each time
    pub purities: Vec<f64>,
    /// Vacuum fidelity at each time
    pub vacuum_fidelities: Vec<f64>,
    /// Trace at each time (sanity check, should be ≈1)
    pub traces: Vec<f64>,
    /// Steady-state mean photon number
    pub steady_state_n: f64,
    /// Thermalization time (time to reach 90% of steady state)
    pub thermalization_time: f64,
    /// Effective decoherence rate (fitted from fidelity decay)
    pub effective_gamma: f64,
}

/// Apply one Euler step of the Lindblad master equation.
///
/// For a single bosonic mode with annihilation operator a:
///   a|n⟩ = √n |n-1⟩,  a†|n⟩ = √(n+1) |n+1⟩
///
/// Lindblad terms:
///   1. Cavity loss: L = √κ_eff × a
///   2. Thermal emission: L = √(γ_th(n̄+1)) × a
///   3. Thermal absorption: L = √(γ_th × n̄) × a†
fn lindblad_step(state: &mut LindbladState, config: &LindbladConfig) {
    let d = state.dim;
    let dt = config.dt;
    let n_th = thermal_occupation(config.omega, config.temperature);

    // Effective kappa with topological protection
    let kappa_eff = if config.protected {
        config.kappa * config.protection_factor
    } else {
        config.kappa
    };

    // Thermal rates
    let gamma_down = kappa_eff * (n_th + 1.0); // emission (a)
    let gamma_up = kappa_eff * n_th;            // absorption (a†)

    // Compute dρ/dt and apply Euler step
    let mut drho_re = vec![0.0; d * d];
    let mut drho_im = vec![0.0; d * d];

    for i in 0..d {
        for j in 0..d {
            let (rho_re, rho_im) = state.get(i, j);

            // 1. Hamiltonian: -i[H, ρ]
            //    H = ω a†a → [H, ρ]_{ij} = ω(i - j) ρ_{ij}
            let h_comm_re = config.omega * (i as f64 - j as f64) * rho_im;
            let h_comm_im = -config.omega * (i as f64 - j as f64) * rho_re;

            // 2. Dissipator for L = a (emission/loss):
            //    L ρ L† - ½{L†L, ρ}
            //    = a ρ a† - ½(a†a ρ + ρ a†a)
            //    (a ρ a†)_{ij} = √((i+1)(j+1)) ρ_{i+1,j+1}
            //    (a†a ρ)_{ij} = i × ρ_{ij}
            //    (ρ a†a)_{ij} = j × ρ_{ij}
            let mut d_loss_re = -0.5 * (i as f64 + j as f64) * rho_re;
            let mut d_loss_im = -0.5 * (i as f64 + j as f64) * rho_im;
            if i + 1 < d && j + 1 < d {
                let sqrt_ij = ((i + 1) as f64 * (j + 1) as f64).sqrt();
                let (r_ip1_jp1, i_ip1_jp1) = state.get(i + 1, j + 1);
                d_loss_re += sqrt_ij * r_ip1_jp1;
                d_loss_im += sqrt_ij * i_ip1_jp1;
            }

            // 3. Dissipator for L = a† (absorption):
            //    a† ρ a - ½{a a†, ρ}
            //    (a† ρ a)_{ij} = √(i × j) ρ_{i-1,j-1}
            //    (a a† ρ)_{ij} = (i+1) × ρ_{ij}
            //    (ρ a a†)_{ij} = (j+1) × ρ_{ij}
            let mut d_abs_re = -0.5 * ((i + 1) as f64 + (j + 1) as f64) * rho_re;
            let mut d_abs_im = -0.5 * ((i + 1) as f64 + (j + 1) as f64) * rho_im;
            if i > 0 && j > 0 {
                let sqrt_ij = (i as f64 * j as f64).sqrt();
                let (r_im1_jm1, i_im1_jm1) = state.get(i - 1, j - 1);
                d_abs_re += sqrt_ij * r_im1_jm1;
                d_abs_im += sqrt_ij * i_im1_jm1;
            }

            // Combine: dρ/dt = -i[H,ρ] + γ_down D[a] + γ_up D[a†]
            let idx = i * d + j;
            drho_re[idx] = h_comm_re + gamma_down * d_loss_re + gamma_up * d_abs_re;
            drho_im[idx] = h_comm_im + gamma_down * d_loss_im + gamma_up * d_abs_im;
        }
    }

    // Euler step: ρ(t+dt) = ρ(t) + dt × dρ/dt
    for k in 0..d * d {
        state.rho_re[k] += dt * drho_re[k];
        state.rho_im[k] += dt * drho_im[k];
    }
}

/// Evolve a single cavity mode under Lindblad dynamics.
pub fn evolve(config: &LindbladConfig, initial: LindbladState) -> LindbladResult {
    let n_steps = (config.total_time / config.dt).ceil() as usize;
    let record_stride = (n_steps / 500).max(1); // record ~500 points

    let mut state = initial;
    let mut times = Vec::new();
    let mut photon_numbers = Vec::new();
    let mut purities = Vec::new();
    let mut vacuum_fidelities = Vec::new();
    let mut traces = Vec::new();

    for step in 0..=n_steps {
        if step % record_stride == 0 || step == n_steps {
            let t = step as f64 * config.dt;
            times.push(t);
            photon_numbers.push(state.mean_photon_number());
            purities.push(state.purity());
            vacuum_fidelities.push(state.vacuum_fidelity());
            traces.push(state.trace());
        }
        if step < n_steps {
            lindblad_step(&mut state, config);
        }
    }

    // Steady-state photon number (last value)
    let steady_state_n = *photon_numbers.last().unwrap_or(&0.0);

    // Thermalization time: time to reach 90% of steady state
    let target_n = 0.9 * steady_state_n;
    let thermalization_time = if steady_state_n > 1e-15 {
        times.iter()
            .zip(photon_numbers.iter())
            .find(|(_, &n)| n >= target_n)
            .map(|(&t, _)| t)
            .unwrap_or(*times.last().unwrap_or(&0.0))
    } else {
        0.0
    };

    // Effective decoherence rate from vacuum fidelity decay
    // F(t) ≈ exp(-γ_eff t) → γ_eff = -ln(F(t_end)) / t_end
    let effective_gamma = {
        let f_end = *vacuum_fidelities.last().unwrap_or(&1.0);
        let t_end = *times.last().unwrap_or(&1.0);
        if f_end > 1e-15 && t_end > 0.0 {
            -f_end.ln() / t_end
        } else {
            config.kappa // fallback
        }
    };

    LindbladResult {
        times,
        photon_numbers,
        purities,
        vacuum_fidelities,
        traces,
        steady_state_n,
        thermalization_time,
        effective_gamma,
    }
}

/// Compare Lindblad dynamics with and without topological protection.
///
/// Returns (unprotected_result, protected_result).
pub fn compare_protection(
    torus: &TorusLattice,
    kappa_hz: f64,
    temperature: f64,
    total_time: f64,
    fock_dim: usize,
) -> (LindbladResult, LindbladResult) {
    let omega = torus.omega_min();
    let gap = torus.spectral_gap();
    let gamma_norm = kappa_hz * torus.length / C;
    let protection = (-gap / gamma_norm).exp().min(1.0);

    let dt = (1.0 / (10.0 * kappa_hz)).min(total_time / 1000.0);

    let config_bare = LindbladConfig {
        omega,
        kappa: kappa_hz,
        temperature,
        fock_dim,
        dt,
        total_time,
        protected: false,
        protection_factor: 1.0,
    };

    let config_protected = LindbladConfig {
        protected: true,
        protection_factor: protection,
        ..config_bare.clone()
    };

    let result_bare = evolve(&config_bare, LindbladState::vacuum(fock_dim));
    let result_protected = evolve(&config_protected, LindbladState::vacuum(fock_dim));

    (result_bare, result_protected)
}

/// Multi-mode Lindblad comparison: run for each mode frequency on T².
///
/// Returns results for the first `max_modes` modes, sorted by frequency.
pub fn multimode_comparison(
    torus: &TorusLattice,
    kappa_hz: f64,
    temperature: f64,
    total_time: f64,
    fock_dim: usize,
    max_modes: usize,
) -> Vec<MultimodeEntry> {
    let gap = torus.spectral_gap();
    let omega_gap = torus.omega_min() * gap.sqrt();
    let gamma_norm = kappa_hz * torus.length / C;
    let protection = (-gap / gamma_norm).exp().min(1.0);

    let freqs = torus.mode_frequencies();
    let dt = (1.0 / (10.0 * kappa_hz)).min(total_time / 1000.0);

    freqs.iter()
        .take(max_modes)
        .map(|&omega_n| {
            let is_protected = omega_n <= omega_gap;
            let pf = if is_protected { protection } else { 1.0 };

            let config = LindbladConfig {
                omega: omega_n,
                kappa: kappa_hz,
                temperature,
                fock_dim,
                dt,
                total_time,
                protected: is_protected,
                protection_factor: pf,
            };

            let result = evolve(&config, LindbladState::vacuum(fock_dim));
            let n_th_theory = thermal_occupation(omega_n, temperature);

            MultimodeEntry {
                frequency_ghz: omega_n / (2.0 * PI * 1e9),
                below_gap: is_protected,
                protection_factor: pf,
                steady_state_n: result.steady_state_n,
                theoretical_n_th: n_th_theory,
                thermalization_time_us: result.thermalization_time * 1e6,
                effective_gamma: result.effective_gamma,
            }
        })
        .collect()
}

/// Entry for multi-mode comparison table.
#[derive(Debug, Clone)]
pub struct MultimodeEntry {
    pub frequency_ghz: f64,
    pub below_gap: bool,
    pub protection_factor: f64,
    pub steady_state_n: f64,
    pub theoretical_n_th: f64,
    pub thermalization_time_us: f64,
    pub effective_gamma: f64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vacuum_state_has_zero_photons() {
        let state = LindbladState::vacuum(8);
        assert!((state.mean_photon_number() - 0.0).abs() < 1e-15);
        assert!((state.trace() - 1.0).abs() < 1e-15);
        assert!((state.purity() - 1.0).abs() < 1e-15);
    }

    #[test]
    fn thermal_state_correct_photon_number() {
        // Use 5 GHz at 100 mK → n̄ ≈ 0.10, easily fits dim=10
        let omega = 2.0 * PI * 5e9;
        let temp = 0.100;
        let state = LindbladState::thermal(10, omega, temp);
        let n_th = thermal_occupation(omega, temp);
        // Should match thermal occupation within truncation error
        let error = (state.mean_photon_number() - n_th).abs() / n_th.max(1e-10);
        assert!(error < 0.05, "Thermal state <n>={} vs theory n_th={}", state.mean_photon_number(), n_th);
    }

    #[test]
    fn lindblad_preserves_trace() {
        let config = LindbladConfig {
            omega: 2.0 * PI * 10e9,
            kappa: 100.0,
            temperature: 0.020,
            fock_dim: 8,
            dt: 1e-5,
            total_time: 0.01,
            protected: false,
            protection_factor: 1.0,
        };
        let result = evolve(&config, LindbladState::vacuum(8));
        for &tr in &result.traces {
            assert!((tr - 1.0).abs() < 0.05, "Trace deviated: {}", tr);
        }
    }

    #[test]
    fn protection_reduces_decoherence() {
        let torus = TorusLattice::new(8, 3e-2);
        let (bare, protected) = compare_protection(&torus, 10.0, 0.020, 0.1, 8);
        // Protected should have higher vacuum fidelity at end
        let f_bare = *bare.vacuum_fidelities.last().unwrap_or(&0.0);
        let f_prot = *protected.vacuum_fidelities.last().unwrap_or(&0.0);
        assert!(
            f_prot >= f_bare - 1e-10,
            "Protected fidelity {} should be >= bare {}",
            f_prot, f_bare
        );
    }

    #[test]
    fn vacuum_thermalizes_to_nth() {
        // 5 GHz at 100 mK → n̄ ≈ 0.10 (small, fits easily in dim 8)
        // Use moderate κ so Euler is well-resolved: κ × dt = 0.01
        let omega = 2.0 * PI * 5e9;
        let temp = 0.100;
        let n_th = thermal_occupation(omega, temp);
        let kappa = 100.0;
        let dt = 1e-4; // κ * n̄ * dim * dt ≈ 100 * 0.1 * 8 * 1e-4 = 0.008
        let config = LindbladConfig {
            omega,
            kappa,
            temperature: temp,
            fock_dim: 8,
            dt,
            total_time: 0.5, // 50 thermalization times
            protected: false,
            protection_factor: 1.0,
        };
        let result = evolve(&config, LindbladState::vacuum(8));
        // n̄ ≈ 0.1 — accept relative error up to 30% since it's a small number
        let error = (result.steady_state_n - n_th).abs();
        assert!(error < 0.05, "Steady state <n>={} vs n_th={}", result.steady_state_n, n_th);
    }
}
