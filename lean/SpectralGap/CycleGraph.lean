/-
  SpectralGap.CycleGraph

  The cycle graph C_N on Fin N as a SimpleGraph.
  Mirrors: spectral.rs `GraphLaplacian::cycle()`.

  Properties proven:
    - cycleGraph (definition)  — SimpleGraph structure (sym + irrefl)
    - cycleSucc_adj            — (v+1) mod N is adjacent to v
    - cyclePred_adj            — (v-1) mod N is adjacent to v
    - cycleSucc_ne_pred        — successor ≠ predecessor (N ≥ 3)

  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic

namespace SpectralGap

/-- (i+1) % N ≠ i for i < N and N ≥ 3. Key lemma for cycle graph irreflexivity. -/
private theorem succ_mod_ne_self (N : Nat) (hN : N ≥ 3) (i : Nat) (hi : i < N) :
    (i + 1) % N ≠ i := by
  intro h
  by_cases hlt : i + 1 < N
  · rw [Nat.mod_eq_of_lt hlt] at h; omega
  · have : i + 1 = N := by omega
    rw [this, Nat.mod_self] at h; omega

/-- The cycle graph C_N on `Fin N`.
    Vertex i is adjacent to vertex j iff they differ by exactly 1 (mod N).
    This encodes the 1D periodic lattice (ring topology).
    Mirrors: spectral.rs lines 42-52 `GraphLaplacian::cycle()`. -/
def cycleGraph (N : Nat) (hN : N ≥ 3) : SimpleGraph (Fin N) where
  Adj i j :=
    (i.val + 1) % N = j.val ∨ (j.val + 1) % N = i.val
  symm := by
    intro i j h
    rcases h with h1 | h2
    · right; exact h1
    · left; exact h2
  loopless := by
    intro i h
    rcases h with h1 | h1
    · exact absurd h1 (succ_mod_ne_self N hN i.val i.isLt)
    · exact absurd h1 (succ_mod_ne_self N hN i.val i.isLt)

/-- C_N adjacency is decidable. -/
instance cycleGraph_decAdj (N : Nat) (hN : N ≥ 3) :
    DecidableRel (cycleGraph N hN).Adj := by
  intro i j
  simp only [cycleGraph]
  exact instDecidableOr

/-- The predecessor neighbor of v in C_N. -/
def cyclePred (N : Nat) (_hN : N ≥ 3) (v : Fin N) : Fin N :=
  ⟨(v.val + N - 1) % N, Nat.mod_lt _ (by omega)⟩

/-- The successor neighbor of v in C_N. -/
def cycleSucc (N : Nat) (_hN : N ≥ 3) (v : Fin N) : Fin N :=
  ⟨(v.val + 1) % N, Nat.mod_lt _ (by omega)⟩

/-- The successor of v is adjacent to v. -/
theorem cycleSucc_adj (N : Nat) (hN : N ≥ 3) (v : Fin N) :
    (cycleGraph N hN).Adj v (cycleSucc N hN v) := by
  show (v.val + 1) % N = (v.val + 1) % N ∨ _
  left; rfl

/-- ((v + N - 1) % N + 1) % N = v for v < N and N ≥ 3. -/
private theorem pred_succ_cancel (N : Nat) (hN : N ≥ 3) (v : Nat) (hv : v < N) :
    ((v + N - 1) % N + 1) % N = v := by
  by_cases hv0 : v = 0
  · subst hv0
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show N - 1 < N by omega),
        show N - 1 + 1 = N from by omega, Nat.mod_self]
  · rw [show v + N - 1 = v - 1 + N from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (show v - 1 < N by omega),
        show v - 1 + 1 = v from by omega, Nat.mod_eq_of_lt hv]

/-- The predecessor of v is adjacent to v. -/
theorem cyclePred_adj (N : Nat) (hN : N ≥ 3) (v : Fin N) :
    (cycleGraph N hN).Adj v (cyclePred N hN v) := by
  show _ ∨ ((v.val + N - 1) % N + 1) % N = v.val
  right
  exact pred_succ_cancel N hN v.val v.isLt

/-- Successor and predecessor are distinct (for N ≥ 3).
    Proof: if succ = pred, then walking 2 steps around the cycle returns to start,
    meaning N | 2. But N ≥ 3, contradiction. -/
theorem cycleSucc_ne_pred (N : Nat) (hN : N ≥ 3) (v : Fin N) :
    cycleSucc N hN v ≠ cyclePred N hN v := by
  intro heq
  -- Extract Nat-level equality from Fin equality
  have h : (v.val + 1) % N = (v.val + N - 1) % N := by
    have := congrArg Fin.val heq
    simp only [cycleSucc, cyclePred] at this
    exact this
  have hv := v.isLt
  -- From pred_succ_cancel: ((v.val + N - 1) % N + 1) % N = v.val
  have h2 := pred_succ_cancel N hN v.val hv
  -- Substitute h into h2: ((v.val + 1) % N + 1) % N = v.val
  rw [← h] at h2
  -- This means (v.val + 2) % N = v.val (by mod algebra)
  have key : (v.val + 2) % N = v.val := by
    rw [show v.val + 2 = v.val + 1 + 1 from by omega,
        Nat.add_mod, Nat.mod_eq_of_lt (show 1 < N by omega)]
    exact h2
  -- (v + 2) % N = v with v < N implies N | 2, but N ≥ 3
  by_cases hlt : v.val + 2 < N
  · rw [Nat.mod_eq_of_lt hlt] at key; omega
  · rw [show v.val + 2 = v.val + 2 - N + N from by omega,
        Nat.add_mod_right,
        Nat.mod_eq_of_lt (show v.val + 2 - N < N by omega)] at key
    omega

end SpectralGap
