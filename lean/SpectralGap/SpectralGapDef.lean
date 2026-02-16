/-
  SpectralGap.SpectralGapDef

  The spectral gap formula λ₁ = 2 - 2cos(2π/N) for the cycle graph C_N,
  proven from Mathlib's Real.cos properties — NOT axiomatized.

  Properties proven (from Mathlib foundations):
    - spectralGap_pos       — λ₁ > 0 for N ≥ 3
    - spectralGap_le_four   — λ₁ ≤ 4
    - spectralGap_bounded   — 0 < λ₁ ≤ 4
    - spectralGap_mono      — λ₁(N+1) < λ₁(N) for N ≥ 3
    - spectralGap_at_two_pi — 2 - 2cos(2π) = 0

  Mirrors: spectral_gap.rs `spectral_gap_positive`, `spectral_gap_bounded`,
           `spectral_gap_monotone`, `spectral_gap_zero_at_one`.

  Key difference from Verus: Here cos is Mathlib's `Real.cos` with
  PROVEN properties (not axiomatized). No trusted axioms needed.

  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Real

namespace SpectralGap

/-! ## Definition -/

/-- The spectral gap of the cycle graph C_N.
    λ₁(N) = 2 - 2cos(2π/N).
    This is the smallest nonzero eigenvalue of the graph Laplacian L = D - A.
    Mirrors: torus.rs:47 `TorusLattice::spectral_gap()`. -/
noncomputable def spectralGap (N : Nat) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi / N)

/-! ## Helper: θ = 2π/N range facts -/

private theorem nat_cast_pos (N : Nat) (hN : N ≥ 1) : (N : ℝ) > 0 :=
  Nat.cast_pos.mpr (by omega)

/-- 2π/N > 0 for N ≥ 1. -/
theorem theta_pos (N : Nat) (hN : N ≥ 1) : 2 * Real.pi / (N : ℝ) > 0 :=
  div_pos (by linarith [Real.pi_pos]) (nat_cast_pos N hN)

/-- 2π/N ≤ π for N ≥ 2. -/
theorem theta_le_pi (N : Nat) (hN : N ≥ 2) :
    2 * Real.pi / (N : ℝ) ≤ Real.pi := by
  rw [div_le_iff₀ (nat_cast_pos N (by omega))]
  have : (N : ℝ) ≥ 2 := by exact_mod_cast hN
  nlinarith [Real.pi_pos]

/-- 2π/N < 2π for N ≥ 2. -/
theorem theta_lt_two_pi (N : Nat) (hN : N ≥ 2) :
    2 * Real.pi / (N : ℝ) < 2 * Real.pi := by
  rw [div_lt_iff₀ (nat_cast_pos N (by omega))]
  have : (N : ℝ) ≥ 2 := by exact_mod_cast hN
  have := Real.pi_pos
  nlinarith

/-! ## Proof 1: λ₁ > 0 for N ≥ 3

    cos is strictly decreasing on [0, π]. Since 0 < 2π/N ≤ π for N ≥ 2,
    we have cos(2π/N) < cos(0) = 1, so 2 - 2cos(2π/N) > 0.
    Mirrors: spectral_gap.rs `spectral_gap_positive`. -/

/-- cos(2π/N) < 1 for N ≥ 3, using Mathlib's proven cos properties. -/
theorem cos_theta_lt_one (N : Nat) (hN : N ≥ 3) :
    Real.cos (2 * Real.pi / (N : ℝ)) < 1 := by
  have h_pos : 0 < 2 * Real.pi / (N : ℝ) := theta_pos N (by omega)
  have h_le_pi : 2 * Real.pi / (N : ℝ) ≤ Real.pi := theta_le_pi N (by omega)
  -- strictAntiOn_cos : StrictAntiOn cos (Set.Icc 0 π)
  -- So cos(θ) < cos(0) = 1 for θ ∈ (0, π]
  have h_anti := Real.strictAntiOn_cos
  have h_mem : 2 * Real.pi / (N : ℝ) ∈ Set.Icc 0 Real.pi :=
    ⟨le_of_lt h_pos, h_le_pi⟩
  have h_zero_mem : (0 : ℝ) ∈ Set.Icc 0 Real.pi :=
    ⟨le_refl 0, le_of_lt Real.pi_pos⟩
  have := h_anti h_zero_mem h_mem h_pos
  rwa [Real.cos_zero] at this

/-- λ₁ > 0 for N ≥ 3.
    Proof: cos(2π/N) < 1 → 2 - 2cos(2π/N) > 0. -/
theorem spectralGap_pos (N : Nat) (hN : N ≥ 3) : spectralGap N > 0 := by
  simp only [spectralGap]
  linarith [cos_theta_lt_one N hN]

/-! ## Proof 2: λ₁ ≤ 4 -/

/-- λ₁ ≤ 4 for all N ≥ 1.
    Proof: cos(x) ≥ -1 → 2cos(x) ≥ -2 → 2-2cos(x) ≤ 4.
    Mirrors: spectral_gap.rs `spectral_gap_bounded`. -/
theorem spectralGap_le_four (N : Nat) (_hN : N ≥ 1) : spectralGap N ≤ 4 := by
  simp only [spectralGap]
  linarith [Real.neg_one_le_cos (2 * Real.pi / (N : ℝ))]

/-- Combined bound: 0 < λ₁ ≤ 4 for N ≥ 3.
    Mirrors: spectral_gap.rs `spectral_gap_bounded`. -/
theorem spectralGap_bounded (N : Nat) (hN : N ≥ 3) :
    0 < spectralGap N ∧ spectralGap N ≤ 4 :=
  ⟨spectralGap_pos N hN, spectralGap_le_four N (by omega)⟩

/-! ## Proof 3: Monotonicity — λ₁(N+1) < λ₁(N) for N ≥ 3 -/

/-- For N ≥ 3: 2π/(N+1) < 2π/N, both in (0, π], so by strict antitonicity
    of cos on [0, π]: cos(2π/(N+1)) > cos(2π/N), hence λ₁(N+1) < λ₁(N).
    Mirrors: spectral_gap.rs `spectral_gap_monotone`. -/
theorem spectralGap_mono (N : Nat) (hN : N ≥ 3) :
    spectralGap (N + 1) < spectralGap N := by
  simp only [spectralGap]
  -- Suffices: cos(2π/(N+1)) > cos(2π/N)
  suffices h : Real.cos (2 * Real.pi / ((N + 1 : Nat) : ℝ)) >
               Real.cos (2 * Real.pi / (N : ℝ)) by linarith
  -- Use strictAntiOn_cos on [0, π]
  apply Real.strictAntiOn_cos
  -- 2π/(N+1) ∈ [0, π]
  · exact ⟨le_of_lt (theta_pos (N + 1) (by omega)), theta_le_pi (N + 1) (by omega)⟩
  -- 2π/N ∈ [0, π]
  · exact ⟨le_of_lt (theta_pos N (by omega)), theta_le_pi N (by omega)⟩
  -- 2π/(N+1) < 2π/N
  · apply div_lt_div_of_pos_left
    · linarith [Real.pi_pos]
    · exact nat_cast_pos N (by omega)
    · push_cast; linarith

/-! ## Proof 4: λ₁ at the boundary -/

/-- 2 - 2cos(2π) = 0, corresponding to the trivial case N=1.
    Mirrors: spectral_gap.rs `spectral_gap_zero_at_one`. -/
theorem spectralGap_at_two_pi : 2 - 2 * Real.cos (2 * Real.pi) = 0 := by
  rw [Real.cos_two_pi]; ring

/-! ## Eigenvalue formula

    The spectral gap formula λ₁ = 2 - 2cos(2π/N) is an eigenvalue of the
    graph Laplacian L = D - A for the cycle graph C_N.

    Proved in SpectralGap.FourierBasis via discrete Fourier analysis:
    the character χ₁(x) = ζ^x (where ζ = exp(2πi/N)) is a nonzero
    eigenvector of the Laplacian with eigenvalue spectralGap N.

    Note: minimality (that λ₁ is the SMALLEST nonzero eigenvalue)
    requires the full Fourier basis completeness argument and is
    left as a strengthening for future work. The eigenvector property
    alone establishes that spectralGap N IS an eigenvalue. -/

end SpectralGap
