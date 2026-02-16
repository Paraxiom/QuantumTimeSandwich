/-
  SpectralGap.Torus

  The discrete torus T² = C_N × C_N as a SimpleGraph on Fin N × Fin N.
  Mirrors: spectral.rs `GraphLaplacian::torus()` and torus.rs `TorusLattice`.

  The 4-connected lattice: each vertex (i,j) is adjacent to
  (i±1 mod N, j) and (i, j±1 mod N).

  Properties proven:
    - torusGraph (definition)  — SimpleGraph structure (sym + irrefl)
    - torusGraph_numVertices   — |V| = N²

  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Prod

namespace SpectralGap

/-- Adjacency on the cycle: i and j differ by 1 mod N. -/
def cycleAdj' (N : Nat) (i j : Fin N) : Prop :=
  (i.val + 1) % N = j.val ∨ (j.val + 1) % N = i.val

/-- (i+1) % N ≠ i for i < N and N ≥ 3. -/
private theorem succ_mod_ne_self' (N : Nat) (hN : N ≥ 3) (i : Nat) (hi : i < N) :
    (i + 1) % N ≠ i := by
  intro h
  by_cases hlt : i + 1 < N
  · rw [Nat.mod_eq_of_lt hlt] at h; omega
  · have : i + 1 = N := by omega
    rw [this, Nat.mod_self] at h; omega

/-- The discrete torus T² = C_N × C_N on `Fin N × Fin N`.
    4-connected: vertex (a,b) is adjacent to (a',b') iff they differ
    by exactly 1 on one coordinate and are equal on the other.
    Mirrors: spectral.rs lines 54-72 `GraphLaplacian::torus()`. -/
def torusGraph (N : Nat) (hN : N ≥ 3) : SimpleGraph (Fin N × Fin N) where
  Adj p q :=
    (cycleAdj' N p.1 q.1 ∧ p.2 = q.2) ∨
    (p.1 = q.1 ∧ cycleAdj' N p.2 q.2)
  symm := by
    intro p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; constructor
      · rcases h1 with h1l | h1r
        · right; exact h1l
        · left; exact h1r
      · exact h2.symm
    · right; constructor
      · exact h1.symm
      · rcases h2 with h2l | h2r
        · right; exact h2l
        · left; exact h2r
  loopless := by
    intro ⟨a, b⟩ h
    simp only [cycleAdj'] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · rcases h1 with h1 | h1
      · exact absurd h1 (succ_mod_ne_self' N hN a.val a.isLt)
      · exact absurd h1 (succ_mod_ne_self' N hN a.val a.isLt)
    · rcases h2 with h2 | h2
      · exact absurd h2 (succ_mod_ne_self' N hN b.val b.isLt)
      · exact absurd h2 (succ_mod_ne_self' N hN b.val b.isLt)

/-- The torus has N² vertices. -/
theorem torusGraph_numVertices (N : Nat) (_hN : N ≥ 3) :
    Fintype.card (Fin N × Fin N) = N * N := by
  simp [Fintype.card_prod, Fintype.card_fin]

end SpectralGap
