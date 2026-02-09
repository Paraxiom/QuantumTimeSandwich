//! # toric-code-sim
//!
//! Kitaev toric code simulator using Pauli frame tracking.
//!
//! Simulates anyonic excitations (e-particles and m-particles) on an N×N torus,
//! with braiding statistics computed via linking numbers. Uses classical bit-vector
//! representation (4N² bits) rather than exponential state vectors, enabling
//! lattice sizes of N=50+.
//!
//! ## Physics
//!
//! - **e-particles** (electric): vertex stabilizer violations from Z errors
//! - **m-particles** (magnetic): plaquette stabilizer violations from X errors
//! - **Braiding**: e around m yields phase (-1), computed from Pauli anticommutation
//! - **Threshold**: ~10.3% (MWPM), ~7-8% (greedy decoder)

pub mod lattice;
pub mod syndrome;
pub mod anyon;
pub mod braiding;
pub mod simulation;

pub mod prelude {
    pub use crate::lattice::*;
    pub use crate::syndrome::*;
    pub use crate::anyon::*;
    pub use crate::braiding::*;
    pub use crate::simulation::*;
}
