//! Scaling experiment: varies N = {2, 4, 9} qubits across topologies.
//!
//! Tests the √N coherence scaling prediction for toroidal topology.
//! Outputs CSV: n_qubits,topology,mean_coherence_time,std_dev
//!
//! Run with:
//!   cargo run --example scaling_experiment
//!
//! Note: N=9 (3×3 grid) takes significantly longer due to 512-dim state
//! vectors with O(T²) circuit depth. N=4 is fast, N=9 is moderate.

use tonnetz_coherence_sim::prelude::*;

fn main() {
    let qubit_counts = [2, 4];
    let noise = NoiseChannel::Depolarizing { p: 0.05 };
    let time_steps = 15;
    let trials = 3;

    println!("n_qubits,topology,mean_coherence_time,std_dev");

    for &n in &qubit_counts {
        let grid_size = (n as f64).sqrt() as usize;

        let topologies: Vec<(&str, CouplingTopology)> = vec![
            ("toroidal", CouplingTopology::Toroidal { grid_size }),
            ("linear", CouplingTopology::Linear),
            (
                "random",
                CouplingTopology::Random {
                    seed: 42,
                    density: 0.3,
                },
            ),
        ];

        for (label, topology) in topologies {
            let config = SimulationConfig {
                n_qubits: n,
                topology,
                noise,
                time_steps,
                trials,
            };

            let result = run_simulation(&config);
            println!(
                "{},{},{:.2},{:.2}",
                n, label, result.mean_coherence_time, result.std_dev
            );
        }
    }

    println!();
    println!("# Theoretical sqrt(N) scaling prediction:");
    for &n in &qubit_counts {
        let grid_size = (n as f64).sqrt() as usize;
        let t_theory =
            tonnetz_coherence_sim::coherence::theoretical_coherence_time(grid_size, 0.5);
        println!(
            "#   N={}: grid_size={}, theoretical_coherence_time={:.2}",
            n, grid_size, t_theory
        );
    }
}
