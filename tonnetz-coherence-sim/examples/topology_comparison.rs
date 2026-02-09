//! Topology comparison: fixed N=4 qubits (2×2 grid), varies noise strength.
//!
//! Compares toroidal, linear, random, and all-to-all topologies
//! across different noise levels to show the toroidal advantage.
//!
//! Run with:
//!   cargo run --example topology_comparison

use tonnetz_coherence_sim::prelude::*;

fn main() {
    let n_qubits = 4;
    let grid_size = 2;
    let noise_levels = [0.01, 0.05, 0.1];
    let time_steps = 20;
    let trials = 3;

    println!(
        "Topology Comparison (N={} qubits, {}x{} grid)",
        n_qubits, grid_size, grid_size
    );
    println!("{:-<72}", "");
    println!(
        "{:<12} {:<8} {:>20} {:>12} {:>12}",
        "Topology", "Noise p", "Mean Coherence Time", "Std Dev", "Fidelity@5"
    );
    println!("{:-<72}", "");

    for &p in &noise_levels {
        let noise = NoiseChannel::Depolarizing { p };

        let topologies: Vec<CouplingTopology> = vec![
            CouplingTopology::Toroidal { grid_size },
            CouplingTopology::Linear,
            CouplingTopology::Random {
                seed: 42,
                density: 0.3,
            },
            CouplingTopology::AllToAll,
        ];

        for topology in topologies {
            let label = tonnetz_coherence_sim::topology::topology_label(&topology);
            let config = SimulationConfig {
                n_qubits,
                topology,
                noise,
                time_steps,
                trials,
            };

            let result = run_simulation(&config);
            let fid_at_5 = result.fidelity_curve.get(4).copied().unwrap_or(f64::NAN);

            println!(
                "{:<12} {:<8.3} {:>20.2} {:>12.2} {:>12.4}",
                label, p, result.mean_coherence_time, result.std_dev, fid_at_5
            );
        }
        println!("{:-<72}", "");
    }

    println!();
    println!("Theoretical spectral gaps:");
    for n in [2, 3, 4, 5, 6] {
        let gap = tonnetz_coherence_sim::coherence::theoretical_decay_rate(n);
        println!("  grid_size={}: lambda_1 = {:.4}", n, gap);
    }
}
