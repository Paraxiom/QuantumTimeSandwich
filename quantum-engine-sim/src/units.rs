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
