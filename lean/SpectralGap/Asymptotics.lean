/-
  SpectralGap.Asymptotics

  Asymptotic bounds on the spectral gap λ₁(N) = 2 - 2cos(2π/N).

  For large N, λ₁(N) ≈ (2π/N)² since cos(x) ≈ 1 - x²/2 for small x.

  Key results:
    - spectralGap_approx_upper  — λ₁(N) ≤ (2π/N)²
    - spectralGap_convergence   — λ₁(N) · N² ≤ (2π)²
    - spectralGap_le_four_pi_sq — λ₁(N) ≤ 4π²/N² (unified bound)

  Uses Mathlib's proven cos bounds: cos(x) ≥ 1 - x²/2 (from Taylor).

  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import SpectralGap.SpectralGapDef

open Real

namespace SpectralGap

noncomputable section

/-! ## Upper bound: λ₁(N) ≤ (2π/N)²

    From cos(x) ≥ 1 - x²/2 (valid for all x ∈ ℝ, Mathlib's
    `one_sub_sq_div_two_le_cos`):
    λ₁ = 2 - 2cos(2π/N) ≤ 2 - 2(1 - (2π/N)²/2) = (2π/N)². -/

/-- cos(x) ≥ 1 - x²/2 implies 2 - 2cos(x) ≤ x².
    Uses Mathlib's `Real.one_sub_sq_div_two_le_cos`. -/
private theorem two_sub_two_cos_le_sq (x : ℝ) : 2 - 2 * cos x ≤ x ^ 2 := by
  have h : 1 - x ^ 2 / 2 ≤ cos x := one_sub_sq_div_two_le_cos
  linarith

/-- λ₁(N) ≤ (2π/N)² for N ≥ 1. -/
theorem spectralGap_approx_upper (N : Nat) (_hN : N ≥ 1) :
    spectralGap N ≤ (2 * Real.pi / N) ^ 2 := by
  simp only [spectralGap]
  exact two_sub_two_cos_le_sq (2 * Real.pi / N)

/-! ## Convergence bound: λ₁(N) · N² ≤ (2π)² -/

/-- λ₁(N) · N² ≤ (2π)² — the spectral gap times N² is bounded.
    This shows the gap closes at rate O(1/N²). -/
theorem spectralGap_convergence (N : Nat) (hN : N ≥ 1) :
    spectralGap N * (N : ℝ) ^ 2 ≤ (2 * Real.pi) ^ 2 := by
  have hNp : (N : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h := spectralGap_approx_upper N hN
  -- λ₁ ≤ (2π/N)² = (2π)²/N²
  -- λ₁ · N² ≤ (2π)²/N² · N² = (2π)²
  calc spectralGap N * (N : ℝ) ^ 2
      ≤ (2 * Real.pi / N) ^ 2 * (N : ℝ) ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]
    _ = (2 * Real.pi) ^ 2 := by field_simp

/-- λ₁(N) ≤ 4π²/N² (unified upper bound). -/
theorem spectralGap_le_four_pi_sq_div (N : Nat) (hN : N ≥ 1) :
    spectralGap N ≤ 4 * Real.pi ^ 2 / (N : ℝ) ^ 2 := by
  have h := spectralGap_approx_upper N hN
  calc spectralGap N
      ≤ (2 * Real.pi / N) ^ 2 := h
    _ = 4 * Real.pi ^ 2 / (N : ℝ) ^ 2 := by ring

/-- Concrete bound: λ₁(N) > 0 and λ₁(N) ≤ (2π/N)² for N ≥ 3.
    Combined with spectralGap_pos. -/
theorem spectralGap_asymptotic_sandwich (N : Nat) (hN : N ≥ 3) :
    0 < spectralGap N ∧ spectralGap N ≤ (2 * Real.pi / N) ^ 2 :=
  ⟨spectralGap_pos N hN, spectralGap_approx_upper N (by omega)⟩

end -- noncomputable section

end SpectralGap
