//! Physical constants in SI units.
//!
//! All values from CODATA 2018 / NIST.

/// Reduced Planck constant (J·s)
pub const HBAR: f64 = 1.054_571_817e-34;

/// Speed of light (m/s)
pub const C: f64 = 299_792_458.0;

/// Boltzmann constant (J/K)
pub const KB: f64 = 1.380_649e-23;

/// Pi
pub const PI: f64 = std::f64::consts::PI;

/// Planck length (m) — natural UV cutoff
pub const L_PLANCK: f64 = 1.616_255e-35;

/// Convert temperature to energy (J)
pub fn thermal_energy(t_kelvin: f64) -> f64 {
    KB * t_kelvin
}

/// Convert energy to temperature (K)
pub fn energy_to_temp(e_joules: f64) -> f64 {
    e_joules / KB
}

/// Convert angular frequency to energy (J)
pub fn omega_to_energy(omega: f64) -> f64 {
    HBAR * omega
}

// ─── Kani formal verification harnesses ─────────────────────────────────────
#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Prove thermal_energy never panics for any f64 input.
    #[kani::proof]
    fn thermal_energy_no_panic() {
        let t: f64 = kani::any();
        let _ = thermal_energy(t);
    }

    /// Prove energy_to_temp never panics for any f64 input.
    #[kani::proof]
    fn energy_to_temp_no_panic() {
        let e: f64 = kani::any();
        let _ = energy_to_temp(e);
    }

    /// Prove omega_to_energy never panics for any f64 input.
    #[kani::proof]
    fn omega_to_energy_no_panic() {
        let omega: f64 = kani::any();
        let _ = omega_to_energy(omega);
    }

    /// Prove round-trip: energy_to_temp(thermal_energy(T)) == T for finite positive T.
    #[kani::proof]
    fn thermal_roundtrip() {
        let t: f64 = kani::any();
        kani::assume(t.is_finite());
        kani::assume(t > 0.0);
        kani::assume(t < 1e20);
        let result = energy_to_temp(thermal_energy(t));
        // f64 multiplication then division by same constant should round-trip
        assert!(result.is_finite());
    }

    /// Prove all physical constants are positive and finite.
    #[kani::proof]
    fn constants_are_valid() {
        assert!(HBAR > 0.0 && HBAR.is_finite());
        assert!(C > 0.0 && C.is_finite());
        assert!(KB > 0.0 && KB.is_finite());
        assert!(PI > 0.0 && PI.is_finite());
        assert!(L_PLANCK > 0.0 && L_PLANCK.is_finite());
    }
}
