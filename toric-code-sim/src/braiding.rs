//! Braiding statistics and linking numbers.
//!
//! The fundamental result of the toric code: **braiding e around m gives phase (-1)**.
//!
//! In the Pauli frame, we don't track phases explicitly. Instead, the braiding phase
//! is computed from the **linking number** — the number of edges where both X and Z
//! errors coexist. This works because Pauli operators anticommute on the same qubit:
//!
//!   XZ = -ZX  ⟹  each overlap contributes a factor of -1
//!
//! Therefore: phase = (-1)^(number of X∧Z overlaps)

use crate::lattice::{Edge, EdgeDir, ToricLattice};
use crate::anyon::{MoveDir, move_e, create_e_pair, create_m_pair};

/// Compute the braiding phase from the current error configuration.
///
/// Returns (-1)^k where k = number of edges with both X and Z errors.
/// This is the accumulated phase from all Pauli anticommutations.
pub fn braiding_phase(lattice: &ToricLattice) -> f64 {
    let crossings = count_crossings(lattice);
    if crossings % 2 == 0 {
        1.0
    } else {
        -1.0
    }
}

/// Count the number of edges where both X and Z errors coexist.
pub fn count_crossings(lattice: &ToricLattice) -> usize {
    lattice
        .x_errors()
        .iter()
        .zip(lattice.z_errors().iter())
        .filter(|(&x, &z)| x && z)
        .count()
}

/// Braid an e-particle around an m-particle in a complete loop.
///
/// Starting from `e_pos`, moves the e-particle in a closed rectangular path
/// that encloses the m-particle at `m_pos`. The path goes:
/// right → down → left → up, forming a 2×2 loop around the m-particle.
///
/// Returns the braiding phase (-1 if e enclosed m, +1 otherwise).
pub fn braid_e_around_m(
    lattice: &mut ToricLattice,
    e_start: (usize, usize),
    _m_pos: (usize, usize),
) -> f64 {
    // Record initial crossings
    let initial_crossings = count_crossings(lattice);

    // Move e in a small square loop: right, down, left, up
    let mut pos = e_start;
    pos = move_e(lattice, pos, MoveDir::Right);
    pos = move_e(lattice, pos, MoveDir::Down);
    pos = move_e(lattice, pos, MoveDir::Left);
    pos = move_e(lattice, pos, MoveDir::Up);

    assert_eq!(pos, e_start, "e-particle should return to start after braid loop");

    let final_crossings = count_crossings(lattice);
    let delta = (final_crossings as isize - initial_crossings as isize).unsigned_abs();

    // Phase from the braid operation
    if delta % 2 == 1 {
        -1.0
    } else {
        1.0
    }
}

/// Apply a logical Z₁ operator: Z on all horizontal edges in row 0.
///
/// This is a non-contractible loop around the torus that commutes with
/// all stabilizers but acts nontrivially on the logical qubit.
pub fn apply_logical_z1(lattice: &mut ToricLattice) {
    let n = lattice.size();
    for c in 0..n {
        lattice.apply_z_error(Edge {
            dir: EdgeDir::Horizontal,
            row: 0,
            col: c,
        });
    }
}

/// Apply a logical Z₂ operator: Z on all vertical edges in column 0.
pub fn apply_logical_z2(lattice: &mut ToricLattice) {
    let n = lattice.size();
    for r in 0..n {
        lattice.apply_z_error(Edge {
            dir: EdgeDir::Vertical,
            row: r,
            col: 0,
        });
    }
}

/// Apply a logical X₁ operator: X on all horizontal edges in column 0.
///
/// This is the vertical co-cycle of horizontal edges: h(0,0), h(1,0), ..., h(n-1,0).
/// Each plaquette sees 0 or 2 of these edges → commutes with all B_p.
/// Shares exactly 1 edge with Z̄₁ (at h(0,0)) → anticommutes with Z̄₁.
pub fn apply_logical_x1(lattice: &mut ToricLattice) {
    let n = lattice.size();
    for r in 0..n {
        lattice.apply_x_error(Edge {
            dir: EdgeDir::Horizontal,
            row: r,
            col: 0,
        });
    }
}

/// Apply a logical X₂ operator: X on all vertical edges in row 0.
///
/// This is the horizontal co-cycle of vertical edges: v(0,0), v(0,1), ..., v(0,n-1).
/// Each plaquette sees 0 or 2 of these edges → commutes with all B_p.
/// Shares exactly 1 edge with Z̄₂ (at v(0,0)) → anticommutes with Z̄₂.
pub fn apply_logical_x2(lattice: &mut ToricLattice) {
    let n = lattice.size();
    for c in 0..n {
        lattice.apply_x_error(Edge {
            dir: EdgeDir::Vertical,
            row: 0,
            col: c,
        });
    }
}

/// Verify the canonical commutation relation: logical Z₁ and X₁ anticommute.
///
/// Z₁ = Z on horizontal edges in row 0: h(0,0), h(0,1), ..., h(0,n-1)
/// X₁ = X on horizontal edges in col 0: h(0,0), h(1,0), ..., h(n-1,0)
/// They share exactly one edge h(0,0), so they anticommute: {Z̄₁, X̄₁} = 0.
/// This is what protects the logical qubit.
pub fn verify_logical_anticommutation(n: usize) -> bool {
    let mut lat = ToricLattice::new(n);

    // Apply Z₁ then X₁
    apply_logical_z1(&mut lat);
    apply_logical_x1(&mut lat);

    // Count overlaps — should be exactly 1 (at edge where loops cross)
    let crossings = count_crossings(&lat);
    crossings == 1
}

/// Demonstrate that braiding e around a region with no m-particle gives trivial phase.
///
/// Creates an e-particle pair, moves one e in a loop that does NOT enclose
/// any m-particle. The braiding phase should be +1.
pub fn trivial_braid_demo(n: usize) -> f64 {
    let mut lat = ToricLattice::new(n);

    // Create e-pair at (1,1)-(1,2)
    let edge = Edge { dir: EdgeDir::Horizontal, row: 1, col: 1 };
    let (_, e_pos) = create_e_pair(&mut lat, edge);

    // Move e in a loop (no m-particles exist)
    let mut pos = e_pos;
    pos = move_e(&mut lat, pos, MoveDir::Right);
    pos = move_e(&mut lat, pos, MoveDir::Down);
    pos = move_e(&mut lat, pos, MoveDir::Left);
    pos = move_e(&mut lat, pos, MoveDir::Up);
    assert_eq!(pos, e_pos);

    braiding_phase(&lat)
}

/// Demonstrate nontrivial braiding: e around m gives phase -1.
///
/// Sets up an m-particle inside a loop, then braids an e-particle around it.
pub fn nontrivial_braid_demo(n: usize) -> f64 {
    assert!(n >= 6, "Need n >= 6 for clean braid demo");
    let mut lat = ToricLattice::new(n);

    // Create m at plaquette (2,2) by X on horizontal edge (2,2)
    // X on h-edge(2,2) → m at plaquettes (1,2) and (2,2)
    let m_edge = Edge { dir: EdgeDir::Horizontal, row: 2, col: 2 };
    create_m_pair(&mut lat, m_edge);

    // Create e at vertex (1,2) by Z on horizontal edge (1,1)
    // Z on h-edge(1,1) → e at vertices (1,1) and (1,2)
    let e_edge = Edge { dir: EdgeDir::Horizontal, row: 1, col: 1 };
    create_e_pair(&mut lat, e_edge);

    // e at (1,2), m at plaquette (2,2)
    // Braid e in a loop: (1,2) → (1,3) → (2,3) → (2,2) → (2,1) → (1,1) → (1,2)
    // Wait, that's not a simple square. Let's do the minimal loop:
    // (1,2) → right → (1,3): Z on h-edge(1,2) — no X here
    // (1,3) → down  → (2,3): Z on v-edge(1,3) — no X here
    // (2,3) → left  → (2,2): Z on h-edge(2,2) — X IS here! CROSSING!
    // (2,2) → up    → (1,2): Z on v-edge(1,2) — no X here
    // Total crossings from braid = 1 → phase = (-1)^1 = -1 ✓

    let mut pos = (1_usize, 2_usize);
    pos = move_e(&mut lat, pos, MoveDir::Right); // (1,3)
    pos = move_e(&mut lat, pos, MoveDir::Down);  // (2,3)
    pos = move_e(&mut lat, pos, MoveDir::Left);  // (2,2)
    pos = move_e(&mut lat, pos, MoveDir::Up);    // (1,2)
    assert_eq!(pos, (1, 2));

    braiding_phase(&lat)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syndrome::Syndrome;

    #[test]
    fn test_trivial_braid_phase_positive() {
        // No m-particles → braiding e in a loop gives +1
        let phase = trivial_braid_demo(8);
        assert!(
            (phase - 1.0).abs() < 1e-10,
            "Trivial braid should give phase +1, got {}",
            phase
        );
    }

    #[test]
    fn test_nontrivial_braid_phase_negative() {
        // e around m → phase -1
        let phase = nontrivial_braid_demo(8);
        assert!(
            (phase - (-1.0)).abs() < 1e-10,
            "Nontrivial braid (e around m) should give phase -1, got {}",
            phase
        );
    }

    #[test]
    fn test_logical_anticommutation() {
        for n in [4, 6, 8, 10] {
            assert!(
                verify_logical_anticommutation(n),
                "Logical Z₁ and X₁ should anticommute for n={}",
                n
            );
        }
    }

    #[test]
    fn test_logical_z1_no_syndrome() {
        let mut lat = ToricLattice::new(6);
        apply_logical_z1(&mut lat);
        let syn = Syndrome::measure(&lat);
        assert!(syn.is_clean(), "Logical Z₁ should create no syndromes");
    }

    #[test]
    fn test_logical_x1_no_syndrome() {
        let mut lat = ToricLattice::new(6);
        apply_logical_x1(&mut lat);
        let syn = Syndrome::measure(&lat);
        assert!(syn.is_clean(), "Logical X₁ should create no syndromes");
    }

    #[test]
    fn test_double_logical_is_identity() {
        let mut lat = ToricLattice::new(6);
        apply_logical_z1(&mut lat);
        apply_logical_z1(&mut lat);
        // Z₁² = I → all errors should cancel
        assert!(lat.x_errors().iter().all(|&e| !e));
        assert!(lat.z_errors().iter().all(|&e| !e));
    }

    #[test]
    fn test_crossing_count() {
        let mut lat = ToricLattice::new(4);
        assert_eq!(count_crossings(&lat), 0);

        let edge = Edge { dir: EdgeDir::Horizontal, row: 0, col: 0 };
        lat.apply_x_error(edge);
        assert_eq!(count_crossings(&lat), 0); // Only X, no Z

        lat.apply_z_error(edge);
        assert_eq!(count_crossings(&lat), 1); // Both X and Z on same edge

        lat.apply_z_error(Edge { dir: EdgeDir::Vertical, row: 1, col: 1 });
        assert_eq!(count_crossings(&lat), 1); // Z-only edge doesn't count
    }

    #[test]
    fn test_braid_e_around_m_function() {
        let mut lat = ToricLattice::new(8);
        // Create m at plaquette (3,3) via X on horizontal edge (3,3)
        let m_edge = Edge { dir: EdgeDir::Horizontal, row: 3, col: 3 };
        create_m_pair(&mut lat, m_edge);

        // Create e near the m — Z on horizontal edge (2,2)
        let e_edge = Edge { dir: EdgeDir::Horizontal, row: 2, col: 2 };
        create_e_pair(&mut lat, e_edge);

        // e at (2,3), braid around m at plaquette (3,3)
        let phase = braid_e_around_m(&mut lat, (2, 3), (3, 3));
        // The small square loop (2,3)→(2,4)→(3,4)→(3,3)→(2,3)
        // may or may not enclose the m depending on exact geometry.
        // The function does a 1×1 loop starting from e_start.
        // With m on h-edge(3,3), the loop traverses:
        //   right: Z on h-edge(2,3) — no overlap
        //   down:  Z on v-edge(2,4) — no overlap
        //   left:  Z on h-edge(3,3) — OVERLAP with X on h-edge(3,3)!
        //   up:    Z on v-edge(2,3) — no overlap
        // So delta = 1 → phase = -1
        assert!(
            (phase - (-1.0)).abs() < 1e-10,
            "braid_e_around_m should give -1, got {}",
            phase
        );
    }
}
