/-
  SpectralGap.ZModDistance

  Toroidal distance metric on (Z/NZ)² — ported from Verus distance.rs.
  Pure integer arithmetic, no transcendentals.

  Proves all metric space axioms for Manhattan distance on the discrete torus:
    1. circularDist_symm     — circ(a,b,N) = circ(b,a,N)
    2. toroidalDist_symm     — d(a,b) = d(b,a)
    3. toroidalDist_self      — d(a,a) = 0
    4. circularDist_bounded   — circ(a,b,N) ≤ N/2
    5. toroidalDist_bounded   — d(a,b) ≤ N
    6. circularDist_triangle  — circ(a,c,N) ≤ circ(a,b,N) + circ(b,c,N)
    7. toroidalDist_triangle  — d(a,c) ≤ d(a,b) + d(b,c)
    8. toroidalDist_nondeg    — d(a,b) = 0 → a = b

  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

namespace SpectralGap

/-! ## Definitions -/

/-- Absolute difference of two natural numbers. -/
def absDiff (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a

/-- Circular distance on Z/NZ: min(|a-b|, N - |a-b|).
    This is the shortest-path distance on the cycle graph C_N. -/
def circularDist (a b N : Nat) : Nat :=
  let d := absDiff a b
  min d (N - d)

/-- Manhattan (toroidal) distance on the N×N torus T² = (Z/NZ)².
    d((r₁,c₁), (r₂,c₂)) = circ(r₁,r₂,N) + circ(c₁,c₂,N). -/
def toroidalDist (r₁ c₁ r₂ c₂ N : Nat) : Nat :=
  circularDist r₁ r₂ N + circularDist c₁ c₂ N

/-! ## Helper lemmas -/

theorem absDiff_symm (a b : Nat) : absDiff a b = absDiff b a := by
  unfold absDiff
  split <;> split <;> omega

theorem absDiff_self (a : Nat) : absDiff a a = 0 := by
  unfold absDiff; simp

theorem absDiff_lt_of_lt (a b N : Nat) (ha : a < N) (hb : b < N) :
    absDiff a b < N := by
  unfold absDiff
  split <;> omega

theorem absDiff_triangle (a b c : Nat) :
    absDiff a c ≤ absDiff a b + absDiff b c := by
  unfold absDiff
  split <;> split <;> split <;> omega

/-- min(d, N-d) ≤ d for any d ≤ N -/
private theorem min_sub_le_left (d N : Nat) (_h : d ≤ N) : min d (N - d) ≤ d := by
  exact Nat.min_le_left d (N - d)

/-! ## Proof 1: Circular distance is symmetric -/

/-- circ(a,b,N) = circ(b,a,N) — symmetry of circular distance.
    Mirrors: distance.rs `circular_dist_symmetric`. -/
theorem circularDist_symm (a b N : Nat) :
    circularDist a b N = circularDist b a N := by
  unfold circularDist
  rw [absDiff_symm]

/-! ## Proof 2: Toroidal distance is symmetric -/

/-- d(a,b) = d(b,a) — symmetry of Manhattan distance on T².
    Mirrors: distance.rs `distance_symmetric`. -/
theorem toroidalDist_symm (r₁ c₁ r₂ c₂ N : Nat) :
    toroidalDist r₁ c₁ r₂ c₂ N = toroidalDist r₂ c₂ r₁ c₁ N := by
  unfold toroidalDist
  rw [circularDist_symm r₁ r₂, circularDist_symm c₁ c₂]

/-! ## Proof 3: Distance to self is zero -/

/-- d(a,a) = 0 — identity of indiscernibles (one direction).
    Mirrors: distance.rs `distance_identity`. -/
theorem toroidalDist_self (r c N : Nat) :
    toroidalDist r c r c N = 0 := by
  simp [toroidalDist, circularDist, absDiff_self]

/-! ## Proof 4: Circular distance is bounded -/

/-- circ(a,b,N) ≤ N/2 for a, b < N.
    Each axis contributes at most ⌊N/2⌋.
    Mirrors: distance.rs `circular_dist_bounded`. -/
theorem circularDist_bounded (a b N : Nat) (ha : a < N) (hb : b < N) (_hN : N > 0) :
    circularDist a b N ≤ N / 2 := by
  unfold circularDist absDiff
  split
  · -- a ≥ b: d = a - b
    rename_i h
    have hd : a - b < N := by omega
    simp [Nat.min_def]
    split
    · omega  -- d ≤ N - d → d ≤ N/2
    · omega  -- d > N - d → N - d ≤ N/2
  · -- a < b: d = b - a
    rename_i h
    have hd : b - a < N := by omega
    simp [Nat.min_def]
    split
    · omega
    · omega

/-! ## Proof 5: Toroidal distance is bounded -/

/-- d(a,b) ≤ N for any two points on the N×N torus.
    Mirrors: distance.rs `distance_bounded`. -/
theorem toroidalDist_bounded (r₁ c₁ r₂ c₂ N : Nat)
    (hr₁ : r₁ < N) (hc₁ : c₁ < N) (hr₂ : r₂ < N) (hc₂ : c₂ < N) (hN : N > 0) :
    toroidalDist r₁ c₁ r₂ c₂ N ≤ N := by
  have h1 := circularDist_bounded r₁ r₂ N hr₁ hr₂ hN
  have h2 := circularDist_bounded c₁ c₂ N hc₁ hc₂ hN
  unfold toroidalDist
  omega

/-! ## Proof 6: Circular distance triangle inequality -/

/-- Helper: circularDist a b N ≤ absDiff a b when absDiff a b ≤ N. -/
private theorem circularDist_le_absDiff (a b N : Nat) (_h : absDiff a b ≤ N) :
    circularDist a b N ≤ absDiff a b := by
  unfold circularDist
  exact Nat.min_le_left _ _

/-- Circular distance on Z/NZ satisfies the triangle inequality.
    circ(a,c,N) ≤ circ(a,b,N) + circ(b,c,N).
    Mirrors: distance.rs `circular_dist_triangle`.

    Proof idea: circ(a,c,N) = min(|a-c|, N-|a-c|) ≤ |a-c| ≤ |a-b| + |b-c|.
    And circ(a,b,N) + circ(b,c,N) ≥ ... we use that min(d,N-d) ≤ d. -/
theorem circularDist_triangle (a b c N : Nat)
    (ha : a < N) (hb : b < N) (hc : c < N) (hN : N ≥ 2) :
    circularDist a c N ≤ circularDist a b N + circularDist b c N := by
  -- Key insight: circ(a,c) ≤ |a-c| ≤ |a-b| + |b-c|
  -- and |a-b| + |b-c| could exceed N, but then the wrap-around path is shorter.
  -- We handle both cases.
  have h_ac_lt : absDiff a c < N := absDiff_lt_of_lt a c N ha hc
  have h_ab_lt : absDiff a b < N := absDiff_lt_of_lt a b N ha hb
  have h_bc_lt : absDiff b c < N := absDiff_lt_of_lt b c N hb hc
  have h_tri : absDiff a c ≤ absDiff a b + absDiff b c := absDiff_triangle a b c
  -- circ(a,c) ≤ |a-c|
  have h1 : circularDist a c N ≤ absDiff a c :=
    circularDist_le_absDiff a c N (Nat.le_of_lt_succ (by omega))
  -- circ(a,b) ≤ |a-b| and circ(b,c) ≤ |b-c|, but we need the other direction too
  -- Actually: if |a-b| + |b-c| < N, then
  --   circ(a,c) ≤ |a-c| ≤ |a-b| + |b-c|
  --   and |a-b| ≥ circ(a,b) and |b-c| ≥ circ(b,c)
  --   BUT this gives circ(a,c) ≤ |a-b| + |b-c|, not ≤ circ(a,b) + circ(b,c)
  -- We need a different approach. Use the fact that on Z/NZ:
  --   circ(a,c) = min(|a-c|, N-|a-c|)
  --   and min(|a-c|, N-|a-c|) ≤ min(|a-b|, N-|a-b|) + min(|b-c|, N-|b-c|)
  -- This requires careful case analysis on the wrap-around.
  unfold circularDist absDiff
  simp [Nat.min_def]
  split <;> split <;> split <;> split <;> split <;> split <;> omega

/-! ## Proof 7: Toroidal distance triangle inequality -/

/-- d(a,c) ≤ d(a,b) + d(b,c) — triangle inequality on T².
    Mirrors: distance.rs `distance_triangle`. -/
theorem toroidalDist_triangle (r₁ c₁ r₂ c₂ r₃ c₃ N : Nat)
    (hr₁ : r₁ < N) (hc₁ : c₁ < N) (hr₂ : r₂ < N) (hc₂ : c₂ < N)
    (hr₃ : r₃ < N) (hc₃ : c₃ < N) (hN : N ≥ 2) :
    toroidalDist r₁ c₁ r₃ c₃ N ≤ toroidalDist r₁ c₁ r₂ c₂ N + toroidalDist r₂ c₂ r₃ c₃ N := by
  have h1 := circularDist_triangle r₁ r₂ r₃ N hr₁ hr₂ hr₃ hN
  have h2 := circularDist_triangle c₁ c₂ c₃ N hc₁ hc₂ hc₃ hN
  unfold toroidalDist
  omega

/-! ## Proof 8: Non-degeneracy -/

/-- If circ(a,b,N) = 0 then a = b, for a, b < N and N ≥ 2. -/
private theorem circularDist_zero_imp_eq (a b N : Nat)
    (ha : a < N) (hb : b < N) (_hN : N ≥ 2)
    (h : circularDist a b N = 0) : a = b := by
  unfold circularDist absDiff at h
  simp [Nat.min_def] at h
  split at h <;> split at h <;> omega

/-- If d(a,b) = 0 then a = b — non-degeneracy of the toroidal metric.
    Together with d(a,a) = 0, gives identity of indiscernibles.
    Mirrors: distance.rs `distance_nondegenerate`. -/
theorem toroidalDist_nondeg (r₁ c₁ r₂ c₂ N : Nat)
    (hr₁ : r₁ < N) (hc₁ : c₁ < N) (hr₂ : r₂ < N) (hc₂ : c₂ < N) (hN : N ≥ 2)
    (h : toroidalDist r₁ c₁ r₂ c₂ N = 0) :
    r₁ = r₂ ∧ c₁ = c₂ := by
  unfold toroidalDist at h
  have hrow : circularDist r₁ r₂ N = 0 := by omega
  have hcol : circularDist c₁ c₂ N = 0 := by omega
  exact ⟨circularDist_zero_imp_eq r₁ r₂ N hr₁ hr₂ hN hrow,
         circularDist_zero_imp_eq c₁ c₂ N hc₁ hc₂ hN hcol⟩

end SpectralGap
