//! Toric lattice with Pauli frame error tracking.
//!
//! The toric code lives on an N×N square lattice with periodic boundary conditions (T²).
//! Qubits sit on **edges**. There are 2N² edges total:
//! - N² horizontal edges: edge (r,c) connects vertex (r,c) to (r, (c+1)%n)
//! - N² vertical edges: edge (r,c) connects vertex (r,c) to ((r+1)%n, c)
//!
//! Instead of a 2^(2N²) state vector, we track errors as classical bit vectors
//! (Pauli frame), giving O(N²) memory and operations.

/// Direction of an edge on the lattice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeDir {
    Horizontal,
    Vertical,
}

/// An edge on the toric lattice, identified by direction and grid position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    pub dir: EdgeDir,
    pub row: usize,
    pub col: usize,
}

/// The toric lattice with Pauli frame error tracking.
///
/// Stores X and Z error frames as boolean vectors over 2N² edges.
/// An X error on an edge creates/annihilates m-particle pairs on adjacent plaquettes.
/// A Z error on an edge creates/annihilates e-particle pairs on adjacent vertices.
#[derive(Debug, Clone)]
pub struct ToricLattice {
    n: usize,
    x_errors: Vec<bool>,
    z_errors: Vec<bool>,
}

impl ToricLattice {
    /// Create a clean N×N toric lattice (no errors).
    pub fn new(n: usize) -> Self {
        assert!(n >= 2, "Lattice size must be at least 2");
        let num_edges = 2 * n * n;
        Self {
            n,
            x_errors: vec![false; num_edges],
            z_errors: vec![false; num_edges],
        }
    }

    /// Lattice dimension.
    pub fn size(&self) -> usize {
        self.n
    }

    /// Total number of edges (qubits).
    pub fn num_edges(&self) -> usize {
        2 * self.n * self.n
    }

    /// Convert an Edge to a linear index.
    pub fn edge_index(&self, edge: Edge) -> usize {
        let r = edge.row % self.n;
        let c = edge.col % self.n;
        match edge.dir {
            EdgeDir::Horizontal => r * self.n + c,
            EdgeDir::Vertical => self.n * self.n + r * self.n + c,
        }
    }

    /// Convert a linear index back to an Edge.
    pub fn index_to_edge(&self, idx: usize) -> Edge {
        let nn = self.n * self.n;
        if idx < nn {
            Edge {
                dir: EdgeDir::Horizontal,
                row: idx / self.n,
                col: idx % self.n,
            }
        } else {
            let idx2 = idx - nn;
            Edge {
                dir: EdgeDir::Vertical,
                row: idx2 / self.n,
                col: idx2 % self.n,
            }
        }
    }

    /// Apply (toggle) an X error on the given edge.
    /// X errors create/annihilate m-particles on adjacent plaquettes.
    pub fn apply_x_error(&mut self, edge: Edge) {
        let idx = self.edge_index(edge);
        self.x_errors[idx] ^= true;
    }

    /// Apply (toggle) a Z error on the given edge.
    /// Z errors create/annihilate e-particles on adjacent vertices.
    pub fn apply_z_error(&mut self, edge: Edge) {
        let idx = self.edge_index(edge);
        self.z_errors[idx] ^= true;
    }

    /// Apply (toggle) a Y error on the given edge (Y = iXZ).
    pub fn apply_y_error(&mut self, edge: Edge) {
        let idx = self.edge_index(edge);
        self.x_errors[idx] ^= true;
        self.z_errors[idx] ^= true;
    }

    /// Check if an X error is present on the given edge.
    pub fn has_x_error(&self, edge: Edge) -> bool {
        self.x_errors[self.edge_index(edge)]
    }

    /// Check if a Z error is present on the given edge.
    pub fn has_z_error(&self, edge: Edge) -> bool {
        self.z_errors[self.edge_index(edge)]
    }

    /// Raw X error frame (read-only).
    pub fn x_errors(&self) -> &[bool] {
        &self.x_errors
    }

    /// Raw Z error frame (read-only).
    pub fn z_errors(&self) -> &[bool] {
        &self.z_errors
    }

    /// Mutable access to X error frame.
    pub fn x_errors_mut(&mut self) -> &mut Vec<bool> {
        &mut self.x_errors
    }

    /// Mutable access to Z error frame.
    pub fn z_errors_mut(&mut self) -> &mut Vec<bool> {
        &mut self.z_errors
    }

    /// Reset all errors to clean state.
    pub fn clear(&mut self) {
        self.x_errors.iter_mut().for_each(|e| *e = false);
        self.z_errors.iter_mut().for_each(|e| *e = false);
    }

    /// The 4 edges touching vertex (r, c).
    ///
    /// A vertex is at the intersection of 4 edges:
    /// - right horizontal: (r, c)
    /// - left horizontal: (r, (c-1+n)%n)
    /// - down vertical: (r, c)
    /// - up vertical: ((r-1+n)%n, c)
    pub fn vertex_edges(&self, row: usize, col: usize) -> [Edge; 4] {
        let n = self.n;
        [
            Edge { dir: EdgeDir::Horizontal, row, col },                           // right
            Edge { dir: EdgeDir::Horizontal, row, col: (col + n - 1) % n },       // left
            Edge { dir: EdgeDir::Vertical, row, col },                             // down
            Edge { dir: EdgeDir::Vertical, row: (row + n - 1) % n, col },         // up
        ]
    }

    /// The 4 edges bounding plaquette (r, c).
    ///
    /// Plaquette (r,c) is the face with corners at (r,c), (r,c+1), (r+1,c), (r+1,c+1):
    /// - top horizontal: (r, c)
    /// - bottom horizontal: ((r+1)%n, c)
    /// - left vertical: (r, c)
    /// - right vertical: (r, (c+1)%n)
    pub fn plaquette_edges(&self, row: usize, col: usize) -> [Edge; 4] {
        let n = self.n;
        [
            Edge { dir: EdgeDir::Horizontal, row, col },                           // top
            Edge { dir: EdgeDir::Horizontal, row: (row + 1) % n, col },           // bottom
            Edge { dir: EdgeDir::Vertical, row, col },                             // left
            Edge { dir: EdgeDir::Vertical, row, col: (col + 1) % n },             // right
        ]
    }

    /// Toroidal Manhattan distance between two vertices.
    pub fn vertex_distance(&self, a: (usize, usize), b: (usize, usize)) -> usize {
        let dr = a.0.abs_diff(b.0);
        let dc = a.1.abs_diff(b.1);
        let dr_wrap = if dr > self.n / 2 { self.n - dr } else { dr };
        let dc_wrap = if dc > self.n / 2 { self.n - dc } else { dc };
        dr_wrap + dc_wrap
    }

    /// Edges along a horizontal path from vertex (r, c1) to (r, c2), wrapping if needed.
    /// Takes the shorter path around the torus.
    pub fn horizontal_path(&self, row: usize, c1: usize, c2: usize) -> Vec<Edge> {
        if c1 == c2 {
            return vec![];
        }
        let n = self.n;
        let forward_dist = (c2 + n - c1) % n;
        let backward_dist = (c1 + n - c2) % n;

        if forward_dist <= backward_dist {
            // Go forward (increasing c)
            (0..forward_dist)
                .map(|i| Edge {
                    dir: EdgeDir::Horizontal,
                    row,
                    col: (c1 + i) % n,
                })
                .collect()
        } else {
            // Go backward (decreasing c)
            (0..backward_dist)
                .map(|i| Edge {
                    dir: EdgeDir::Horizontal,
                    row,
                    col: (c2 + i) % n,
                })
                .collect()
        }
    }

    /// Edges along a vertical path from vertex (r1, c) to (r2, c), wrapping if needed.
    /// Takes the shorter path around the torus.
    pub fn vertical_path(&self, col: usize, r1: usize, r2: usize) -> Vec<Edge> {
        if r1 == r2 {
            return vec![];
        }
        let n = self.n;
        let forward_dist = (r2 + n - r1) % n;
        let backward_dist = (r1 + n - r2) % n;

        if forward_dist <= backward_dist {
            (0..forward_dist)
                .map(|i| Edge {
                    dir: EdgeDir::Vertical,
                    row: (r1 + i) % n,
                    col,
                })
                .collect()
        } else {
            (0..backward_dist)
                .map(|i| Edge {
                    dir: EdgeDir::Vertical,
                    row: (r2 + i) % n,
                    col,
                })
                .collect()
        }
    }

    /// Shortest L-shaped path from vertex a to vertex b (horizontal then vertical).
    pub fn shortest_path(&self, a: (usize, usize), b: (usize, usize)) -> Vec<Edge> {
        let mut path = self.horizontal_path(a.0, a.1, b.1);
        path.extend(self.vertical_path(b.1, a.0, b.0));
        path
    }

    /// Shortest dual-lattice path between plaquettes a and b.
    ///
    /// On the dual lattice, moving right between plaquettes (r,c)→(r,c+1)
    /// crosses vertical edge v(r, c+1). Moving down (r,c)→(r+1,c) crosses
    /// horizontal edge h(r+1, c). This is the "edge-swapped" version of
    /// the primal shortest_path.
    pub fn dual_shortest_path(&self, a: (usize, usize), b: (usize, usize)) -> Vec<Edge> {
        let n = self.n;
        let mut path = Vec::new();

        // Horizontal dual moves (change column)
        let dc_fwd = (b.1 + n - a.1) % n;
        let dc_bwd = (a.1 + n - b.1) % n;

        if a.1 != b.1 {
            if dc_fwd <= dc_bwd {
                // Move right: each step crosses v(r, c+1)
                for i in 0..dc_fwd {
                    path.push(Edge {
                        dir: EdgeDir::Vertical,
                        row: a.0,
                        col: (a.1 + i + 1) % n,
                    });
                }
            } else {
                // Move left: each step crosses v(r, c)
                for i in 0..dc_bwd {
                    path.push(Edge {
                        dir: EdgeDir::Vertical,
                        row: a.0,
                        col: (a.1 + n - i) % n,
                    });
                }
            }
        }

        // Vertical dual moves (change row) — from (a.0, b.1) to (b.0, b.1)
        let dr_fwd = (b.0 + n - a.0) % n;
        let dr_bwd = (a.0 + n - b.0) % n;

        if a.0 != b.0 {
            if dr_fwd <= dr_bwd {
                // Move down: each step crosses h(r+1, c)
                for i in 0..dr_fwd {
                    path.push(Edge {
                        dir: EdgeDir::Horizontal,
                        row: (a.0 + i + 1) % n,
                        col: b.1,
                    });
                }
            } else {
                // Move up: each step crosses h(r, c)
                for i in 0..dr_bwd {
                    path.push(Edge {
                        dir: EdgeDir::Horizontal,
                        row: (a.0 + n - i) % n,
                        col: b.1,
                    });
                }
            }
        }

        path
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_lattice_clean() {
        let lat = ToricLattice::new(4);
        assert_eq!(lat.size(), 4);
        assert_eq!(lat.num_edges(), 32);
        assert!(lat.x_errors().iter().all(|&e| !e));
        assert!(lat.z_errors().iter().all(|&e| !e));
    }

    #[test]
    fn test_edge_index_roundtrip() {
        let lat = ToricLattice::new(5);
        for idx in 0..lat.num_edges() {
            let edge = lat.index_to_edge(idx);
            assert_eq!(lat.edge_index(edge), idx);
        }
    }

    #[test]
    fn test_toggle_errors() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Horizontal, row: 1, col: 2 };
        assert!(!lat.has_x_error(edge));
        lat.apply_x_error(edge);
        assert!(lat.has_x_error(edge));
        lat.apply_x_error(edge);
        assert!(!lat.has_x_error(edge));
    }

    #[test]
    fn test_vertex_edges_count() {
        let lat = ToricLattice::new(4);
        let edges = lat.vertex_edges(0, 0);
        assert_eq!(edges.len(), 4);
        // All edges should be distinct
        for i in 0..4 {
            for j in (i + 1)..4 {
                assert_ne!(lat.edge_index(edges[i]), lat.edge_index(edges[j]));
            }
        }
    }

    #[test]
    fn test_plaquette_edges_count() {
        let lat = ToricLattice::new(4);
        let edges = lat.plaquette_edges(0, 0);
        assert_eq!(edges.len(), 4);
        for i in 0..4 {
            for j in (i + 1)..4 {
                assert_ne!(lat.edge_index(edges[i]), lat.edge_index(edges[j]));
            }
        }
    }

    #[test]
    fn test_toroidal_distance() {
        let lat = ToricLattice::new(8);
        assert_eq!(lat.vertex_distance((0, 0), (0, 0)), 0);
        assert_eq!(lat.vertex_distance((0, 0), (0, 1)), 1);
        assert_eq!(lat.vertex_distance((0, 0), (3, 3)), 6);
        // Wraparound: (0,0) to (0,7) should be 1, not 7
        assert_eq!(lat.vertex_distance((0, 0), (0, 7)), 1);
        assert_eq!(lat.vertex_distance((0, 0), (7, 0)), 1);
    }

    #[test]
    fn test_shortest_path_length() {
        let lat = ToricLattice::new(8);
        let path = lat.shortest_path((0, 0), (3, 3));
        assert_eq!(path.len(), 6); // Manhattan distance
        let path2 = lat.shortest_path((0, 0), (0, 7));
        assert_eq!(path2.len(), 1); // Wraparound
    }

    #[test]
    fn test_clear() {
        let mut lat = ToricLattice::new(4);
        lat.apply_x_error(Edge { dir: EdgeDir::Horizontal, row: 0, col: 0 });
        lat.apply_z_error(Edge { dir: EdgeDir::Vertical, row: 1, col: 1 });
        lat.clear();
        assert!(lat.x_errors().iter().all(|&e| !e));
        assert!(lat.z_errors().iter().all(|&e| !e));
    }

    #[test]
    fn test_y_error_sets_both() {
        let mut lat = ToricLattice::new(4);
        let edge = Edge { dir: EdgeDir::Horizontal, row: 0, col: 0 };
        lat.apply_y_error(edge);
        assert!(lat.has_x_error(edge));
        assert!(lat.has_z_error(edge));
    }

    #[test]
    fn test_toroidal_distance_matches_tonnetz() {
        use topological_coherence::Tonnetz;

        fn check<const N: usize>() {
            let lat = ToricLattice::new(N);
            let _tonnetz = Tonnetz::<N>::new();
            for r1 in 0..N {
                for c1 in 0..N {
                    for r2 in 0..N {
                        for c2 in 0..N {
                            let d_lat = lat.vertex_distance((r1, c1), (r2, c2));
                            let d_ton = Tonnetz::<N>::distance((r1, c1), (r2, c2));
                            assert_eq!(
                                d_lat, d_ton,
                                "Distance mismatch at ({},{})→({},{}) for N={}: lat={} ton={}",
                                r1, c1, r2, c2, N, d_lat, d_ton
                            );
                        }
                    }
                }
            }
        }

        check::<4>();
        check::<8>();
        check::<12>();
    }
}
