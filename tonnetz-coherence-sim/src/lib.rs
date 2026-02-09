//! # tonnetz-coherence-sim
//!
//! Numerical simulation of toroidal coherence scaling on quantum hardware,
//! bridging the QuantumTimeSandwich circuit simulator with Tonnetz topology
//! from the topological-coherence crate.
//!
//! ## Hypothesis
//!
//! Qubits coupled through a toroidal (Tonnetz) topology exhibit √N coherence
//! scaling compared to O(1) for random or linear coupling — matching the
//! spectral gap advantage proven analytically and validated empirically in
//! the LLM domain (+2.8pp TruthfulQA).
//!
//! ## Usage
//!
//! ```no_run
//! use tonnetz_coherence_sim::prelude::*;
//!
//! let config = SimulationConfig {
//!     n_qubits: 16,
//!     topology: CouplingTopology::Toroidal { grid_size: 4 },
//!     noise: NoiseChannel::Depolarizing { p: 0.05 },
//!     time_steps: 100,
//!     trials: 10,
//! };
//! let result = run_simulation(&config);
//! println!("Mean coherence time: {}", result.mean_coherence_time);
//! ```

pub mod noise;
pub mod topology;
pub mod coherence;
pub mod simulation;
pub mod torus;

pub mod prelude {
    pub use crate::noise::*;
    pub use crate::topology::*;
    pub use crate::coherence::*;
    pub use crate::simulation::*;
    pub use crate::torus::*;
}
