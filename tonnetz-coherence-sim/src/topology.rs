//! Coupling topologies defining qubit connectivity and interaction strengths.
//!
//! Maps the Tonnetz toroidal geometry (from topological-coherence) and
//! comparison topologies onto qubit coupling graphs with weighted edges.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

/// Coupling topology variant for a qubit array.
#[derive(Debug, Clone)]
pub enum CouplingTopology {
    /// Toroidal (Tonnetz) coupling: qubits on a grid_size × grid_size torus.
    /// Edge weight = exp(-d_T(i,j)) where d_T is the toroidal L1 distance.
    Toroidal { grid_size: usize },

    /// Linear (nearest-neighbor) coupling: weight = 1.0 for |i-j| = 1.
    Linear,

    /// Random (Erdős–Rényi) coupling: each pair connected with given density.
    Random { seed: u64, density: f64 },

    /// All-to-all coupling: every pair connected with weight 1.0.
    AllToAll,
}

/// An edge in the coupling graph: (qubit_i, qubit_j, weight).
pub type CouplingEdge = (usize, usize, f64);

/// Compute the coupling strength between two qubits under a topology.
///
/// Returns 0.0 if the qubits are not coupled.
pub fn coupling_strength(topology: &CouplingTopology, n_qubits: usize, i: usize, j: usize) -> f64 {
    if i == j {
        return 0.0;
    }
    match topology {
        CouplingTopology::Toroidal { grid_size } => {
            let gs = *grid_size;
            let ii = i % (gs * gs);
            let jj = j % (gs * gs);
            let ci = (ii / gs, ii % gs);
            let cj = (jj / gs, jj % gs);
            let dr = toroidal_dist_1d(ci.0, cj.0, gs);
            let dc = toroidal_dist_1d(ci.1, cj.1, gs);
            let d = (dr + dc) as f64;
            (-d).exp()
        }
        CouplingTopology::Linear => {
            if (i as isize - j as isize).unsigned_abs() == 1 {
                1.0
            } else {
                0.0
            }
        }
        CouplingTopology::Random { seed, density } => {
            // Deterministic: use a hash of (seed, min(i,j), max(i,j))
            let (lo, hi) = if i < j { (i, j) } else { (j, i) };
            let pair_seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add((lo as u64).wrapping_mul(1442695040888963407))
                .wrapping_add((hi as u64).wrapping_mul(2862933555777941757));
            let mut rng = StdRng::seed_from_u64(pair_seed);
            let r: f64 = rng.gen();
            if r < *density {
                1.0
            } else {
                0.0
            }
        }
        CouplingTopology::AllToAll => {
            if i < n_qubits && j < n_qubits {
                1.0
            } else {
                0.0
            }
        }
    }
}

/// Build the complete coupling map for a given topology and qubit count.
///
/// Returns a list of (i, j, weight) edges where weight > 0, with i < j
/// to avoid duplicates.
pub fn build_coupling_map(topology: &CouplingTopology, n_qubits: usize) -> Vec<CouplingEdge> {
    let mut edges = Vec::new();
    for i in 0..n_qubits {
        for j in (i + 1)..n_qubits {
            let w = coupling_strength(topology, n_qubits, i, j);
            if w > 1e-12 {
                edges.push((i, j, w));
            }
        }
    }
    edges
}

/// 1D toroidal distance on a ring of size n.
fn toroidal_dist_1d(a: usize, b: usize, n: usize) -> usize {
    let diff = if a > b { a - b } else { b - a };
    diff.min(n - diff)
}

/// Label string for a topology (for output formatting).
pub fn topology_label(topology: &CouplingTopology) -> &'static str {
    match topology {
        CouplingTopology::Toroidal { .. } => "toroidal",
        CouplingTopology::Linear => "linear",
        CouplingTopology::Random { .. } => "random",
        CouplingTopology::AllToAll => "all-to-all",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn toroidal_self_distance_is_zero_weight_one() {
        // coupling_strength(i, i) should be 0 (no self-loops)
        let topo = CouplingTopology::Toroidal { grid_size: 4 };
        assert_eq!(coupling_strength(&topo, 16, 3, 3), 0.0);
    }

    #[test]
    fn toroidal_neighbors_have_high_weight() {
        let topo = CouplingTopology::Toroidal { grid_size: 4 };
        // Qubit 0 = (0,0), Qubit 1 = (0,1) — distance 1
        let w = coupling_strength(&topo, 16, 0, 1);
        assert!((w - (-1.0_f64).exp()).abs() < 1e-10);
    }

    #[test]
    fn linear_only_neighbors() {
        let topo = CouplingTopology::Linear;
        assert!(coupling_strength(&topo, 8, 0, 1) > 0.0);
        assert_eq!(coupling_strength(&topo, 8, 0, 2), 0.0);
        assert_eq!(coupling_strength(&topo, 8, 0, 7), 0.0);
    }

    #[test]
    fn linear_coupling_map_has_n_minus_1_edges() {
        let topo = CouplingTopology::Linear;
        let edges = build_coupling_map(&topo, 8);
        assert_eq!(edges.len(), 7);
    }

    #[test]
    fn all_to_all_coupling_map_is_complete() {
        let topo = CouplingTopology::AllToAll;
        let edges = build_coupling_map(&topo, 5);
        assert_eq!(edges.len(), 10); // C(5,2) = 10
    }

    #[test]
    fn random_coupling_is_deterministic() {
        let topo = CouplingTopology::Random {
            seed: 42,
            density: 0.5,
        };
        let w1 = coupling_strength(&topo, 10, 2, 7);
        let w2 = coupling_strength(&topo, 10, 2, 7);
        assert_eq!(w1, w2);
    }

    #[test]
    fn random_coupling_is_symmetric() {
        let topo = CouplingTopology::Random {
            seed: 42,
            density: 0.5,
        };
        let w1 = coupling_strength(&topo, 10, 2, 7);
        let w2 = coupling_strength(&topo, 10, 7, 2);
        assert_eq!(w1, w2);
    }

    #[test]
    fn toroidal_dist_1d_wraparound() {
        assert_eq!(toroidal_dist_1d(0, 3, 4), 1); // wraps: 4-3 = 1
        assert_eq!(toroidal_dist_1d(0, 2, 4), 2); // direct = wrap = 2
    }

    #[test]
    fn build_coupling_map_no_duplicates() {
        let topo = CouplingTopology::Toroidal { grid_size: 3 };
        let edges = build_coupling_map(&topo, 9);
        for &(i, j, _) in &edges {
            assert!(i < j, "Edge ({}, {}) violates i < j", i, j);
        }
    }
}
