//! # Quantum Engine Simulator
//!
//! Unified simulation framework for the Quantum Time Sandwich platform.
//! Chains five layers of physics through a single toroidal geometry:
//!
//! ```text
//! Atlas Spectral Gap (λ₁=1)
//!   ↓ geometric principle
//! Tonnetz Coherence (λ₁ = 2-2cos(2π/N))
//!   ↓ decay rate
//! Toric Code Protection (P_L ~ exp(-αN))
//!   ↓ error suppression
//! Vacuum Physics (Casimir, Unruh, DCE on T²)
//!   ↓ energy extraction
//! Quantum Engine Cycle (vacuum → work)
//! ```
//!
//! ## The thesis
//!
//! The spectral gap of T² is a **geometric invariant** — not domain-specific.
//! It bounds drift in LLMs (toroidal logit bias), suppresses errors in
//! quantum codes (toric code), and protects vacuum states from decoherence
//! (Casimir cavity). The same mathematics, three domains.
//!
//! ## Analog gravity connection
//!
//! The engine cycle on T² maps to analog gravity phenomena:
//! - **Unruh effect**: Spectral gap creates minimum detectable acceleration
//! - **Dynamical Casimir**: Boundary oscillation extracts photon pairs from vacuum
//! - **Hawking analog**: Topological defects on T² create acoustic horizons
//! - **Alcubierre analog**: Metric deformation bounded by spectral gap stability
//!
//! ## References
//!
//! - Cormier (2026), "Topological Constraints for Coherent Language Models"
//!   <https://doi.org/10.5281/zenodo.18624950>
//! - Kitaev (2003), "Fault-tolerant quantum computation by anyons"
//! - Casimir (1948), "On the attraction between two perfectly conducting plates"
//! - Unruh (1976), "Notes on black-hole evaporation"
//! - Moore (1970), "Quantum theory of the electromagnetic field in a variable-length
//!   one-dimensional cavity" (dynamical Casimir effect)
//! - Aharonov, Bergmann, Lebowitz (1964), "Time symmetry in the quantum process
//!   of measurement" (two-state vector formalism — the original time sandwich)

pub mod units;
pub mod torus;
pub mod spectral;
pub mod coherence;
pub mod toric_code;
pub mod vacuum;
pub mod engine;
pub mod covariant;
pub mod cnt_physics;
pub mod cnt_bridge;
pub mod logit_drift;
pub mod lindblad;
pub mod noise;
pub mod wilson_comparison;
pub mod sim_worker;
pub mod gui;
