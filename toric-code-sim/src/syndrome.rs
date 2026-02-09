//! Syndrome measurement for the toric code.
//!
//! **Vertex stabilizer** A_v = ∏ Z_e for edges e touching vertex v.
//! A_v = -1 when an odd number of Z errors touch v → **e-particle** present.
//!
//! **Plaquette stabilizer** B_p = ∏ X_e for edges e bounding plaquette p.
//! B_p = -1 when an odd number of X errors bound p → **m-particle** present.
//!
//! **Logical operators**: Non-contractible loops of Z (X) operators along a cycle
//! of the torus commute with all stabilizers but act nontrivially on the code space.

use crate::lattice::{Edge, EdgeDir, ToricLattice};

/// Result of syndrome measurement.
#[derive(Debug, Clone)]
pub struct Syndrome {
    /// Vertex syndromes: true = e-particle present at vertex (r, c).
    pub vertex_syndromes: Vec<Vec<bool>>,
    /// Plaquette syndromes: true = m-particle present at plaquette (r, c).
    pub plaquette_syndromes: Vec<Vec<bool>>,
}

impl Syndrome {
    /// Measure all vertex and plaquette stabilizers.
    pub fn measure(lattice: &ToricLattice) -> Self {
        let n = lattice.size();
        let mut vertex_syndromes = vec![vec![false; n]; n];
        let mut plaquette_syndromes = vec![vec![false; n]; n];

        for r in 0..n {
            for c in 0..n {
                // Vertex stabilizer: parity of Z errors on adjacent edges
                let v_edges = lattice.vertex_edges(r, c);
                let z_parity = v_edges.iter().filter(|&&e| lattice.has_z_error(e)).count();
                vertex_syndromes[r][c] = z_parity % 2 == 1;

                // Plaquette stabilizer: parity of X errors on boundary edges
                let p_edges = lattice.plaquette_edges(r, c);
                let x_parity = p_edges.iter().filter(|&&e| lattice.has_x_error(e)).count();
                plaquette_syndromes[r][c] = x_parity % 2 == 1;
            }
        }

        Self {
            vertex_syndromes,
            plaquette_syndromes,
        }
    }

    /// Locations of e-particles (vertex syndrome violations).
    pub fn e_particles(&self) -> Vec<(usize, usize)> {
        let mut locs = Vec::new();
        for (r, row) in self.vertex_syndromes.iter().enumerate() {
            for (c, &syn) in row.iter().enumerate() {
                if syn {
                    locs.push((r, c));
                }
            }
        }
        locs
    }

    /// Locations of m-particles (plaquette syndrome violations).
    pub fn m_particles(&self) -> Vec<(usize, usize)> {
        let mut locs = Vec::new();
        for (r, row) in self.plaquette_syndromes.iter().enumerate() {
            for (c, &syn) in row.iter().enumerate() {
                if syn {
                    locs.push((r, c));
                }
            }
        }
        locs
    }

    /// Total number of e-particles. Always even on a torus.
    pub fn num_e_particles(&self) -> usize {
        self.vertex_syndromes
            .iter()
            .flat_map(|row| row.iter())
            .filter(|&&s| s)
            .count()
    }

    /// Total number of m-particles. Always even on a torus.
    pub fn num_m_particles(&self) -> usize {
        self.plaquette_syndromes
            .iter()
            .flat_map(|row| row.iter())
            .filter(|&&s| s)
            .count()
    }

    /// Check if the lattice is syndrome-free (ground state).
    pub fn is_clean(&self) -> bool {
        self.num_e_particles() == 0 && self.num_m_particles() == 0
    }
}

/// Detect logical Z₁ errors via a transverse cut.
///
/// Z̄₁ is a horizontal non-contractible Z cycle. We detect it by counting Z errors
/// on a vertical cut (horizontal edges in a fixed column). The algebraic intersection
/// number of the cycle with the cut is 1 → odd parity = logical error present.
pub fn has_logical_z_error(lattice: &ToricLattice) -> bool {
    let n = lattice.size();
    // Vertical cut at col 0: count Z errors on horizontal edges h(r, 0) for all r
    let parity: usize = (0..n)
        .filter(|&r| {
            lattice.has_z_error(Edge {
                dir: EdgeDir::Horizontal,
                row: r,
                col: 0,
            })
        })
        .count();
    parity % 2 == 1
}

/// Detect logical X₁ errors via a transverse cut.
///
/// X̄₁ is a vertical non-contractible X co-cycle (horizontal edges in a column).
/// We detect it by counting X errors on a horizontal cut (horizontal edges in a fixed row).
pub fn has_logical_x_error(lattice: &ToricLattice) -> bool {
    let n = lattice.size();
    // Horizontal cut at row 0: count X errors on horizontal edges h(0, c) for all c
    let parity: usize = (0..n)
        .filter(|&c| {
            lattice.has_x_error(Edge {
                dir: EdgeDir::Horizontal,
                row: 0,
                col: c,
            })
        })
        .count();
    parity % 2 == 1
}

/// Detect logical Z₂ errors via a transverse cut.
///
/// Z̄₂ is a vertical non-contractible Z cycle (vertical edges in a column).
/// We detect it by counting Z errors on a horizontal cut (vertical edges in a fixed row).
pub fn has_logical_z2_error(lattice: &ToricLattice) -> bool {
    let n = lattice.size();
    // Horizontal cut at row 0: count Z errors on vertical edges v(0, c) for all c
    let parity: usize = (0..n)
        .filter(|&c| {
            lattice.has_z_error(Edge {
                dir: EdgeDir::Vertical,
                row: 0,
                col: c,
            })
        })
        .count();
    parity % 2 == 1
}

/// Detect logical X₂ errors via a transverse cut.
///
/// X̄₂ is a horizontal non-contractible X co-cycle (vertical edges in a row).
/// We detect it by counting X errors on a vertical cut (vertical edges in a fixed column).
pub fn has_logical_x2_error(lattice: &ToricLattice) -> bool {
    let n = lattice.size();
    // Vertical cut at col 0: count X errors on vertical edges v(r, 0) for all r
    let parity: usize = (0..n)
        .filter(|&r| {
            lattice.has_x_error(Edge {
                dir: EdgeDir::Vertical,
                row: r,
                col: 0,
            })
        })
        .count();
    parity % 2 == 1
}

/// Check for any logical error (either logical qubit, either X or Z).
pub fn has_any_logical_error(lattice: &ToricLattice) -> bool {
    has_logical_z_error(lattice)
        || has_logical_x_error(lattice)
        || has_logical_z2_error(lattice)
        || has_logical_x2_error(lattice)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clean_lattice_no_syndromes() {
        let lat = ToricLattice::new(4);
        let syn = Syndrome::measure(&lat);
        assert!(syn.is_clean());
        assert_eq!(syn.num_e_particles(), 0);
        assert_eq!(syn.num_m_particles(), 0);
    }

    #[test]
    fn test_single_z_error_creates_two_e_particles() {
        let mut lat = ToricLattice::new(4);
        // Z error on horizontal edge (1,2) → e-particles at vertices (1,2) and (1,3)
        lat.apply_z_error(Edge {
            dir: EdgeDir::Horizontal,
            row: 1,
            col: 2,
        });
        let syn = Syndrome::measure(&lat);
        assert_eq!(syn.num_e_particles(), 2);
        assert_eq!(syn.num_m_particles(), 0);
    }

    #[test]
    fn test_single_x_error_creates_two_m_particles() {
        let mut lat = ToricLattice::new(4);
        // X error on horizontal edge (1,2) → m-particles at adjacent plaquettes
        lat.apply_x_error(Edge {
            dir: EdgeDir::Horizontal,
            row: 1,
            col: 2,
        });
        let syn = Syndrome::measure(&lat);
        assert_eq!(syn.num_e_particles(), 0);
        assert_eq!(syn.num_m_particles(), 2);
    }

    #[test]
    fn test_syndrome_count_always_even() {
        let mut lat = ToricLattice::new(6);
        // Apply several random errors
        lat.apply_z_error(Edge { dir: EdgeDir::Horizontal, row: 0, col: 0 });
        lat.apply_z_error(Edge { dir: EdgeDir::Vertical, row: 2, col: 3 });
        lat.apply_x_error(Edge { dir: EdgeDir::Horizontal, row: 4, col: 1 });
        lat.apply_x_error(Edge { dir: EdgeDir::Vertical, row: 1, col: 5 });
        lat.apply_x_error(Edge { dir: EdgeDir::Vertical, row: 3, col: 0 });

        let syn = Syndrome::measure(&lat);
        assert_eq!(syn.num_e_particles() % 2, 0, "e-particle count must be even");
        assert_eq!(syn.num_m_particles() % 2, 0, "m-particle count must be even");
    }

    #[test]
    fn test_noncontractible_z_loop_no_syndrome() {
        let mut lat = ToricLattice::new(4);
        // Z errors along entire row 0 (non-contractible horizontal loop)
        for c in 0..4 {
            lat.apply_z_error(Edge {
                dir: EdgeDir::Horizontal,
                row: 0,
                col: c,
            });
        }
        let syn = Syndrome::measure(&lat);
        // No syndromes! The loop is a logical operator, not detectable.
        assert!(syn.is_clean());
        // But there IS a logical error
        assert!(has_logical_z_error(&lat));
    }

    #[test]
    fn test_contractible_loop_no_logical_error() {
        let mut lat = ToricLattice::new(4);
        // Z errors around a single plaquette (contractible loop)
        // Plaquette (0,0): top-h(0,0), bottom-h(1,0), left-v(0,0), right-v(0,1)
        lat.apply_z_error(Edge { dir: EdgeDir::Horizontal, row: 0, col: 0 });
        lat.apply_z_error(Edge { dir: EdgeDir::Horizontal, row: 1, col: 0 });
        lat.apply_z_error(Edge { dir: EdgeDir::Vertical, row: 0, col: 0 });
        lat.apply_z_error(Edge { dir: EdgeDir::Vertical, row: 0, col: 1 });

        let syn = Syndrome::measure(&lat);
        // Contractible loop → no syndromes AND no logical error
        assert!(syn.is_clean());
        assert!(!has_logical_z_error(&lat));
    }

    #[test]
    fn test_no_errors_no_logical_error() {
        let lat = ToricLattice::new(4);
        assert!(!has_any_logical_error(&lat));
    }
}
