//! Anyonic excitations: creation, movement, and fusion.
//!
//! In Kitaev's toric code:
//! - **e-particles** live on vertices (Z-error endpoints)
//! - **m-particles** live on plaquettes (X-error endpoints)
//!
//! Moving an anyon extends the error chain to the adjacent edge.
//! Anyons are always created in pairs. Fusion rules:
//! - e × e → vacuum (1)
//! - m × m → vacuum (1)
//! - e × m → fermion (ε)

use crate::lattice::{Edge, EdgeDir, ToricLattice};
use crate::syndrome::Syndrome;

/// Type of anyonic excitation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnyonType {
    /// Electric charge — vertex stabilizer violation (from Z errors).
    E,
    /// Magnetic flux — plaquette stabilizer violation (from X errors).
    M,
}

/// Fusion result of two anyons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FusionResult {
    /// Trivial particle (vacuum).
    Vacuum,
    /// Electric charge.
    E,
    /// Magnetic flux.
    M,
    /// Fermion (composite e×m).
    Fermion,
}

/// Compute the fusion of two anyon types.
pub fn fuse(a: AnyonType, b: AnyonType) -> FusionResult {
    match (a, b) {
        (AnyonType::E, AnyonType::E) => FusionResult::Vacuum,
        (AnyonType::M, AnyonType::M) => FusionResult::Vacuum,
        (AnyonType::E, AnyonType::M) | (AnyonType::M, AnyonType::E) => FusionResult::Fermion,
    }
}

/// Direction of movement on the lattice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MoveDir {
    Up,
    Down,
    Left,
    Right,
}

/// Create a pair of e-particles by applying a Z error on the given edge.
///
/// Returns the two vertex positions where the e-particles appear.
pub fn create_e_pair(lattice: &mut ToricLattice, edge: Edge) -> ((usize, usize), (usize, usize)) {
    lattice.apply_z_error(edge);
    let n = lattice.size();
    match edge.dir {
        EdgeDir::Horizontal => {
            // Horizontal edge (r,c) → vertices (r,c) and (r, (c+1)%n)
            ((edge.row, edge.col), (edge.row, (edge.col + 1) % n))
        }
        EdgeDir::Vertical => {
            // Vertical edge (r,c) → vertices (r,c) and ((r+1)%n, c)
            ((edge.row, edge.col), ((edge.row + 1) % n, edge.col))
        }
    }
}

/// Create a pair of m-particles by applying an X error on the given edge.
///
/// Returns the two plaquette positions where the m-particles appear.
pub fn create_m_pair(lattice: &mut ToricLattice, edge: Edge) -> ((usize, usize), (usize, usize)) {
    lattice.apply_x_error(edge);
    let n = lattice.size();
    match edge.dir {
        EdgeDir::Horizontal => {
            // Horizontal edge (r,c): adjacent plaquettes are (r-1, c) and (r, c)
            (((edge.row + n - 1) % n, edge.col), (edge.row, edge.col))
        }
        EdgeDir::Vertical => {
            // Vertical edge (r,c): adjacent plaquettes are (r, c-1) and (r, c)
            ((edge.row, (edge.col + n - 1) % n), (edge.row, edge.col))
        }
    }
}

/// Move an e-particle from vertex `pos` in the given direction.
///
/// This applies a Z error on the traversed edge, effectively moving the
/// e-particle to the adjacent vertex. Returns the new position.
pub fn move_e(
    lattice: &mut ToricLattice,
    pos: (usize, usize),
    dir: MoveDir,
) -> (usize, usize) {
    let n = lattice.size();
    let (r, c) = pos;

    let (edge, new_pos) = match dir {
        MoveDir::Right => (
            Edge { dir: EdgeDir::Horizontal, row: r, col: c },
            (r, (c + 1) % n),
        ),
        MoveDir::Left => (
            Edge { dir: EdgeDir::Horizontal, row: r, col: (c + n - 1) % n },
            (r, (c + n - 1) % n),
        ),
        MoveDir::Down => (
            Edge { dir: EdgeDir::Vertical, row: r, col: c },
            ((r + 1) % n, c),
        ),
        MoveDir::Up => (
            Edge { dir: EdgeDir::Vertical, row: (r + n - 1) % n, col: c },
            ((r + n - 1) % n, c),
        ),
    };

    lattice.apply_z_error(edge);
    new_pos
}

/// Move an m-particle from plaquette `pos` in the given direction.
///
/// This applies an X error on the traversed edge, effectively moving the
/// m-particle to the adjacent plaquette. Returns the new position.
pub fn move_m(
    lattice: &mut ToricLattice,
    pos: (usize, usize),
    dir: MoveDir,
) -> (usize, usize) {
    let n = lattice.size();
    let (r, c) = pos;

    let (edge, new_pos) = match dir {
        MoveDir::Right => (
            Edge { dir: EdgeDir::Vertical, row: r, col: (c + 1) % n },
            (r, (c + 1) % n),
        ),
        MoveDir::Left => (
            Edge { dir: EdgeDir::Vertical, row: r, col: c },
            (r, (c + n - 1) % n),
        ),
        MoveDir::Down => (
            Edge { dir: EdgeDir::Horizontal, row: (r + 1) % n, col: c },
            ((r + 1) % n, c),
        ),
        MoveDir::Up => (
            Edge { dir: EdgeDir::Horizontal, row: r, col: c },
            ((r + n - 1) % n, c),
        ),
    };

    lattice.apply_x_error(edge);
    new_pos
}

/// Move an e-particle along a path from `start` to `end` via shortest L-shaped route.
///
/// Returns the final position (should equal `end`).
pub fn move_e_to(
    lattice: &mut ToricLattice,
    start: (usize, usize),
    end: (usize, usize),
) -> (usize, usize) {
    let path = lattice.shortest_path(start, end);
    for edge in &path {
        lattice.apply_z_error(*edge);
    }
    end
}

/// Check if two e-particles at the same vertex have fused to vacuum.
pub fn check_e_fusion(lattice: &ToricLattice, pos: (usize, usize)) -> bool {
    let syn = Syndrome::measure(lattice);
    !syn.vertex_syndromes[pos.0][pos.1]
}

/// Check if two m-particles at the same plaquette have fused to vacuum.
pub fn check_m_fusion(lattice: &ToricLattice, pos: (usize, usize)) -> bool {
    let syn = Syndrome::measure(lattice);
    !syn.plaquette_syndromes[pos.0][pos.1]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_e_pair() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Horizontal, row: 1, col: 2 };
        let (a, b) = create_e_pair(&mut lat, edge);
        assert_eq!(a, (1, 2));
        assert_eq!(b, (1, 3));

        let syn = Syndrome::measure(&lat);
        assert_eq!(syn.num_e_particles(), 2);
        assert!(syn.vertex_syndromes[1][2]);
        assert!(syn.vertex_syndromes[1][3]);
    }

    #[test]
    fn test_create_m_pair() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Horizontal, row: 1, col: 2 };
        let (a, b) = create_m_pair(&mut lat, edge);

        let syn = Syndrome::measure(&lat);
        assert_eq!(syn.num_m_particles(), 2);
        assert!(syn.plaquette_syndromes[a.0][a.1]);
        assert!(syn.plaquette_syndromes[b.0][b.1]);
    }

    #[test]
    fn test_move_e_particle() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Horizontal, row: 1, col: 1 };
        let (_, e_pos) = create_e_pair(&mut lat, edge);
        // e_pos = (1, 2)

        // Move right
        let new_pos = move_e(&mut lat, e_pos, MoveDir::Right);
        assert_eq!(new_pos, (1, 3));

        let syn = Syndrome::measure(&lat);
        assert_eq!(syn.num_e_particles(), 2);
        // Original particle at (1,1), moved particle now at (1,3)
        assert!(syn.vertex_syndromes[1][1]);
        assert!(syn.vertex_syndromes[1][3]);
    }

    #[test]
    fn test_e_fusion_to_vacuum() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Horizontal, row: 0, col: 0 };
        let (a, b) = create_e_pair(&mut lat, edge);
        // a=(0,0), b=(0,1) — move b back to a
        move_e_to(&mut lat, b, a);

        let syn = Syndrome::measure(&lat);
        assert!(syn.is_clean(), "e×e fusion should give vacuum");
    }

    #[test]
    fn test_fusion_rules() {
        assert_eq!(fuse(AnyonType::E, AnyonType::E), FusionResult::Vacuum);
        assert_eq!(fuse(AnyonType::M, AnyonType::M), FusionResult::Vacuum);
        assert_eq!(fuse(AnyonType::E, AnyonType::M), FusionResult::Fermion);
        assert_eq!(fuse(AnyonType::M, AnyonType::E), FusionResult::Fermion);
    }

    #[test]
    fn test_move_wraps_around() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Horizontal, row: 0, col: 0 };
        let (a, _) = create_e_pair(&mut lat, edge);
        // a = (0, 0) — move left should wrap to (0, 3)
        let new_pos = move_e(&mut lat, a, MoveDir::Left);
        assert_eq!(new_pos, (0, 3));
    }

    #[test]
    fn test_move_m_particle() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Vertical, row: 0, col: 0 };
        let (_, m_pos) = create_m_pair(&mut lat, edge);

        let new_pos = move_m(&mut lat, m_pos, MoveDir::Right);
        let syn = Syndrome::measure(&lat);
        assert_eq!(syn.num_m_particles(), 2);
        // Check the m-particle actually moved
        assert!(syn.plaquette_syndromes[new_pos.0][new_pos.1]);
    }
}
