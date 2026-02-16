/-
  SpectralGap.FourierBasis

  Connects the spectral gap formula λ₁ = 2 - 2cos(2π/N) to the graph Laplacian
  via discrete Fourier analysis on the cycle graph C_N.

  Key results:
    - rootOfUnity_pow_N            — ζ^N = 1 (N-th root of unity)
    - rootOfUnity_pow_pred_eq_inv  — ζ^(N-1) = ζ⁻¹
    - rootOfUnity_add_inv          — ζ + ζ⁻¹ = 2cos(2π/N)
    - eigenvalue_eq                — 2 - ζ - ζ^(N-1) = spectralGap N
    - cycleLap_chi₁                — L(χ₁)(x) = λ₁ · χ₁(x)
    - eigenvalueK_zero             — λ_0 = 0
    - spectralGap_le_eigenvalueK   — λ₁ ≤ λ_k for 1 ≤ k ≤ N-1

  Proves that χ₁(x) = ζ^x is an eigenvector of the cycle Laplacian with
  eigenvalue spectralGap N, AND that this is the smallest nonzero eigenvalue.

  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import SpectralGap.CycleGraph
import SpectralGap.SpectralGapDef

open Complex Real

namespace SpectralGap

noncomputable section

/-! ## Definitions -/

/-- The primitive N-th root of unity ζ = exp(2πi/N). -/
def rootOfUnity (N : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)

/-- The first Fourier character χ₁(x) = ζ^(x.val). -/
def chi₁ (N : ℕ) (x : Fin N) : ℂ := rootOfUnity N ^ x.val

/-! ## Root of unity properties -/

/-- ζ = exp(↑θ · I) where θ = 2π/N as a real number. -/
private theorem rootOfUnity_eq_exp_mul_I (N : ℕ) (hN : N ≥ 1) :
    rootOfUnity N = Complex.exp (↑(2 * Real.pi / (↑N : ℝ)) * Complex.I) := by
  unfold rootOfUnity
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

/-- ζ^N = 1: the N-th root of unity property. -/
theorem rootOfUnity_pow_N (N : ℕ) (hN : N ≥ 1) : rootOfUnity N ^ N = 1 := by
  unfold rootOfUnity
  rw [← Complex.exp_nat_mul]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (↑N : ℂ) * (2 * ↑Real.pi * Complex.I / ↑N) = 2 * ↑Real.pi * Complex.I := by
    field_simp
  rw [this]
  exact Complex.exp_two_pi_mul_I

/-- If a^n = 1 then a^(m % n) = a^m. Standard root-of-unity power reduction. -/
private theorem pow_mod_eq {a : ℂ} {n : ℕ} (h : a ^ n = 1) (m : ℕ) :
    a ^ (m % n) = a ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

/-- ζ^(N-1) = ζ⁻¹. -/
theorem rootOfUnity_pow_pred_eq_inv (N : ℕ) (hN : N ≥ 1) :
    rootOfUnity N ^ (N - 1) = (rootOfUnity N)⁻¹ := by
  have hζN := rootOfUnity_pow_N N hN
  have hne : rootOfUnity N ≠ 0 := Complex.exp_ne_zero _
  have hmul : rootOfUnity N ^ (N - 1) * rootOfUnity N = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ N by omega)]
    exact hζN
  have hinv : (rootOfUnity N)⁻¹ * rootOfUnity N = 1 := inv_mul_cancel₀ hne
  exact mul_right_cancel₀ hne (hmul.trans hinv.symm)

/-! ## Euler's formula connection -/

/-- ζ + ζ⁻¹ = 2cos(2π/N): the key identity connecting roots of unity to cosine. -/
theorem rootOfUnity_add_inv (N : ℕ) (hN : N ≥ 1) :
    rootOfUnity N + (rootOfUnity N)⁻¹ = 2 * ↑(Real.cos (2 * Real.pi / ↑N)) := by
  rw [rootOfUnity_eq_exp_mul_I N hN]
  set θ : ℝ := 2 * Real.pi / ↑N
  rw [← Complex.exp_neg]
  -- exp(↑θ · I) = cos(↑θ) + sin(↑θ) · I   [Euler's formula]
  have h1 : Complex.exp (↑θ * Complex.I) = Complex.cos ↑θ + Complex.sin ↑θ * Complex.I :=
    Complex.exp_mul_I ↑θ
  -- exp(-↑θ · I) = cos(↑θ) - sin(↑θ) · I   [conjugate]
  have h2 : Complex.exp (-(↑θ * Complex.I)) = Complex.cos ↑θ - Complex.sin ↑θ * Complex.I := by
    have : -(↑θ * Complex.I) = (-↑θ) * Complex.I := by ring
    rw [this]
    exact (Complex.cos_sub_sin_I (↑θ)).symm
  rw [h1, h2, ← Complex.ofReal_cos θ]
  ring

/-! ## Eigenvalue equation -/

/-- The characteristic equation: 2 - ζ - ζ^(N-1) = spectralGap N.
    This is the eigenvalue of the Laplacian corresponding to χ₁. -/
theorem eigenvalue_eq (N : ℕ) (hN : N ≥ 3) :
    (2 : ℂ) - rootOfUnity N - rootOfUnity N ^ (N - 1) = ↑(spectralGap N) := by
  rw [rootOfUnity_pow_pred_eq_inv N (by omega : N ≥ 1)]
  have hadd := rootOfUnity_add_inv N (by omega : N ≥ 1)
  simp only [spectralGap, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination -hadd

/-! ## Character shift lemmas -/

/-- χ₁(succ x) = χ₁(x) · ζ -/
theorem chi_cycleSucc (N : ℕ) (hN : N ≥ 3) (x : Fin N) :
    chi₁ N (cycleSucc N hN x) = chi₁ N x * rootOfUnity N := by
  simp only [chi₁, cycleSucc]
  rw [pow_mod_eq (rootOfUnity_pow_N N (by omega)) (x.val + 1)]
  rw [pow_succ]

/-- χ₁(pred x) = χ₁(x) · ζ^(N-1) -/
theorem chi_cyclePred (N : ℕ) (hN : N ≥ 3) (x : Fin N) :
    chi₁ N (cyclePred N hN x) = chi₁ N x * rootOfUnity N ^ (N - 1) := by
  simp only [chi₁, cyclePred]
  rw [pow_mod_eq (rootOfUnity_pow_N N (by omega)) (x.val + N - 1)]
  rw [show x.val + N - 1 = x.val + (N - 1) from by omega]
  rw [pow_add]

/-! ## Eigenvector theorem -/

/-- L(χ₁)(x) = spectralGap(N) · χ₁(x): the first Fourier character is an eigenvector
    of the cycle Laplacian with eigenvalue spectralGap N. -/
theorem cycleLap_chi₁ (N : ℕ) (hN : N ≥ 3) (x : Fin N) :
    2 * chi₁ N x - chi₁ N (cycleSucc N hN x) - chi₁ N (cyclePred N hN x) =
    ↑(spectralGap N) * chi₁ N x := by
  rw [chi_cycleSucc, chi_cyclePred]
  have h := eigenvalue_eq N hN
  linear_combination chi₁ N x * h

/-- χ₁ is nonzero: χ₁(0) = ζ^0 = 1 ≠ 0. -/
theorem chi₁_ne_zero (N : ℕ) (hN : N ≥ 1) : ∃ x : Fin N, chi₁ N x ≠ 0 := by
  exact ⟨⟨0, by omega⟩, by simp [chi₁, pow_zero]⟩

/-! ## Minimality: spectralGap N is minimum among Fourier eigenvalues -/

/-- The k-th Laplacian eigenvalue of cycle graph C_N: λ_k = 2 - 2cos(2πk/N). -/
noncomputable def eigenvalueK (N k : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi * k / N)

/-- λ_0 = 0: the constant eigenfunction has eigenvalue zero. -/
theorem eigenvalueK_zero (N : ℕ) (_hN : N ≥ 1) : eigenvalueK N 0 = 0 := by
  simp only [eigenvalueK, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero]
  norm_num

/-- λ_1 = spectralGap N. -/
theorem eigenvalueK_one (N : ℕ) : eigenvalueK N 1 = spectralGap N := by
  simp only [eigenvalueK, spectralGap, Nat.cast_one, mul_one]

/-- cos(2π - x) = cos(x), from periodicity and evenness. -/
private theorem cos_two_pi_sub (x : ℝ) : Real.cos (2 * Real.pi - x) = Real.cos x := by
  rw [show 2 * Real.pi - x = -x + 2 * Real.pi from by ring,
      Real.cos_add_two_pi, Real.cos_neg]

/-- Cosine complementarity: cos(2πk/N) = cos(2π(N-k)/N) for k ≤ N. -/
private theorem cos_complementary (N k : ℕ) (hN : N ≥ 1) (hk : k ≤ N) :
    Real.cos (2 * Real.pi * ↑k / ↑N) = Real.cos (2 * Real.pi * ↑(N - k) / ↑N) := by
  rw [Nat.cast_sub hk]
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : 2 * Real.pi * ↑k / ↑N = 2 * Real.pi - 2 * Real.pi * (↑N - ↑k) / ↑N := by
    field_simp; ring
  rw [h, cos_two_pi_sub]

/-- For k in the first half (2k ≤ N): cos(2πk/N) ≤ cos(2π/N).
    Uses antitonicity of cos on [0, π]. -/
private theorem cos_le_first_half (N k : ℕ) (hN : N ≥ 3) (hk1 : 1 ≤ k) (hk2 : 2 * k ≤ N) :
    Real.cos (2 * Real.pi * ↑k / ↑N) ≤ Real.cos (2 * Real.pi / ↑N) := by
  have hNp : (N : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  apply Real.strictAntiOn_cos.antitoneOn
  · -- 2π/N ∈ [0, π]
    exact ⟨le_of_lt (theta_pos N (by omega)), theta_le_pi N (by omega)⟩
  · -- 2πk/N ∈ [0, π]
    constructor
    · apply le_of_lt
      apply div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos)
        (Nat.cast_pos.mpr (show 0 < k by omega))) hNp
    · rw [div_le_iff₀ hNp]
      have : 2 * (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk2
      nlinarith [Real.pi_pos]
  · -- 2π/N ≤ 2πk/N
    apply div_le_div_of_nonneg_right _ (le_of_lt hNp)
    have : (k : ℝ) ≥ 1 := by exact_mod_cast hk1
    nlinarith [Real.pi_pos]

/-- **Minimality**: spectralGap N ≤ eigenvalueK N k for all 1 ≤ k ≤ N-1.
    The spectral gap is the smallest nonzero Laplacian eigenvalue of C_N.
    Proof splits into two cases by cosine antitonicity on [0, π] and
    the complementarity cos(2πk/N) = cos(2π(N-k)/N). -/
theorem spectralGap_le_eigenvalueK (N k : ℕ) (hN : N ≥ 3) (hk1 : 1 ≤ k) (hk2 : k ≤ N - 1) :
    spectralGap N ≤ eigenvalueK N k := by
  simp only [spectralGap, eigenvalueK]
  suffices h : Real.cos (2 * Real.pi * ↑k / ↑N) ≤ Real.cos (2 * Real.pi / ↑N) by linarith
  by_cases h2k : 2 * k ≤ N
  · exact cos_le_first_half N k hN hk1 h2k
  · push_neg at h2k
    rw [cos_complementary N k (by omega) (by omega : k ≤ N)]
    exact cos_le_first_half N (N - k) hN (by omega) (by omega)

end -- noncomputable section

end SpectralGap
