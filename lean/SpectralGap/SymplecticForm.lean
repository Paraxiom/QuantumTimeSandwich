/-
  SpectralGap.SymplecticForm

  The canonical symplectic form ω = Σ dqⁱ ∧ dpⁱ on the phase space ℝⁿ × ℝⁿ,
  connecting the spectral gap analysis to Souriau's geometric quantization,
  ERLHS agent tuples (M, ω, H, T, C), and Karmonic admissibility.

  Key results (17 theorems):
    - symplecticForm_alt           — ω(u,u) = 0
    - symplecticForm_skew          — ω(u,v) = -ω(v,u)
    - symplecticForm_add_left      — ω(u+v, w) = ω(u,w) + ω(v,w)
    - symplecticForm_smul_left     — ω(cu, v) = c·ω(u,v)
    - symplecticForm_add_right     — ω(u, v+w) = ω(u,v) + ω(u,w)
    - symplecticForm_nondegenerate — (∀v, ω(u,v)=0) → u=0
    - torusPhaseSpace_dim          — 2·N² = N² + N²
    - torus8_phaseSpace_dim        — 2·512 = 1024
    - cycleHamiltonian_nonneg      — H(q) ≥ 0
    - cycleHamiltonian_const       — H(c,...,c) = 0
    - cycleHamiltonian_eq_zero_iff — H=0 ↔ all neighbors equal
    - poissonBracket_skew          — {f,g} = -{g,f}
    - poissonBracket_self          — {f,f} = 0
    - identity_admissible          — staying put is Karmonic-admissible
    - admissible_trans             — admissibility composes with ε accumulation
    - symplecticForm_unit_cell     — ω(eᵢ^q, eᵢ^p) = 1
    - symplecticForm_basis         — ω(eᵢ^q, eⱼ^p) = δᵢⱼ

  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import SpectralGap.SpectralGapDef
import SpectralGap.CycleGraph

namespace SpectralGap

noncomputable section

/-! ## Phase Space Types -/

/-- Configuration vector: positions on an n-dimensional discrete space. -/
abbrev ConfigVec (n : Nat) := Fin n → ℝ

/-- Phase space vector: (positions, momenta) in ℝⁿ × ℝⁿ. -/
abbrev PhaseVec (n : Nat) := (Fin n → ℝ) × (Fin n → ℝ)

/-- Component-wise addition of phase vectors. -/
def phaseAdd {n : Nat} (u v : PhaseVec n) : PhaseVec n :=
  (fun i => u.1 i + v.1 i, fun i => u.2 i + v.2 i)

/-- Scalar multiplication of phase vectors. -/
def phaseSmul {n : Nat} (c : ℝ) (u : PhaseVec n) : PhaseVec n :=
  (fun i => c * u.1 i, fun i => c * u.2 i)

/-! ## Canonical Symplectic Form -/

/-- The canonical symplectic form ω on ℝⁿ × ℝⁿ:
    ω(u, v) = Σᵢ (qᵢ pᵢ' - pᵢ qᵢ')
    where u = (q, p) and v = (q', p').
    This is Souriau's 2-form ω = Σ dqⁱ ∧ dpⁱ on the cotangent bundle T*Q.
    Mirrors: ERLHS Definition 2.1 (agent symplectic structure). -/
def symplecticForm (n : Nat) (u v : PhaseVec n) : ℝ :=
  Finset.sum Finset.univ fun i : Fin n => u.1 i * v.2 i - u.2 i * v.1 i

/-- ω(u, u) = 0: the symplectic form is alternating. -/
theorem symplecticForm_alt (n : Nat) (u : PhaseVec n) :
    symplecticForm n u u = 0 := by
  unfold symplecticForm
  apply Finset.sum_eq_zero
  intro i _; ring

/-- ω(u, v) = -ω(v, u): the symplectic form is skew-symmetric. -/
theorem symplecticForm_skew (n : Nat) (u v : PhaseVec n) :
    symplecticForm n u v = -symplecticForm n v u := by
  unfold symplecticForm
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

/-- ω(u+v, w) = ω(u,w) + ω(v,w): left-additivity. -/
theorem symplecticForm_add_left (n : Nat) (u v w : PhaseVec n) :
    symplecticForm n (phaseAdd u v) w =
    symplecticForm n u w + symplecticForm n v w := by
  unfold symplecticForm phaseAdd
  dsimp only []
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

/-- ω(c·u, v) = c·ω(u,v): left scalar multiplication. -/
theorem symplecticForm_smul_left (n : Nat) (c : ℝ) (u v : PhaseVec n) :
    symplecticForm n (phaseSmul c u) v = c * symplecticForm n u v := by
  unfold symplecticForm phaseSmul
  dsimp only []
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

/-- ω(u, v+w) = ω(u,v) + ω(u,w): right-additivity. -/
theorem symplecticForm_add_right (n : Nat) (u v w : PhaseVec n) :
    symplecticForm n u (phaseAdd v w) =
    symplecticForm n u v + symplecticForm n u w := by
  unfold symplecticForm phaseAdd
  dsimp only []
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

/-- Position basis vector: eᵢ^q = (δᵢ, 0). -/
def basisQ {n : Nat} (i : Fin n) : PhaseVec n :=
  (fun j => if j = i then 1 else 0, fun _ => 0)

/-- Momentum basis vector: eᵢ^p = (0, δᵢ). -/
def basisP {n : Nat} (i : Fin n) : PhaseVec n :=
  (fun _ => 0, fun j => if j = i then 1 else 0)

/-- Evaluating ω against eᵢ^p extracts the q-component. -/
private theorem symplecticForm_basisP (n : Nat) (u : PhaseVec n) (i : Fin n) :
    symplecticForm n u (basisP i) = u.1 i := by
  unfold symplecticForm basisP
  dsimp only []
  simp only [mul_ite, mul_one, mul_zero, sub_zero]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]

/-- Evaluating ω against eᵢ^q extracts minus the p-component. -/
private theorem symplecticForm_basisQ (n : Nat) (u : PhaseVec n) (i : Fin n) :
    symplecticForm n u (basisQ i) = -u.2 i := by
  unfold symplecticForm basisQ
  dsimp only []
  simp only [mul_zero, zero_sub, mul_ite, mul_one]
  rw [Finset.sum_neg_distrib, Finset.sum_ite_eq']
  simp [Finset.mem_univ]

/-- (∀ v, ω(u,v) = 0) → u = 0: the symplectic form is nondegenerate. -/
theorem symplecticForm_nondegenerate (n : Nat) (u : PhaseVec n)
    (h : ∀ v : PhaseVec n, symplecticForm n u v = 0) :
    u = (fun _ => 0, fun _ => 0) := by
  have hq : u.1 = fun _ => 0 := by
    ext i
    have := h (basisP i)
    rwa [symplecticForm_basisP] at this
  have hp : u.2 = fun _ => 0 := by
    ext i
    have := h (basisQ i)
    rw [symplecticForm_basisQ] at this
    linarith
  exact Prod.ext hq hp

/-! ## Torus Phase Space -/

/-- The phase space of the N×N torus has dimension 2N² = N² + N². -/
theorem torusPhaseSpace_dim (N : Nat) : 2 * (N * N) = N * N + N * N := by ring

/-- Concrete: the 8×8×8 torus (512 vertices) has 1024-dimensional phase space. -/
theorem torus8_phaseSpace_dim : 2 * 512 = 1024 := by norm_num

/-! ## Harmonic Hamiltonian on the Cycle -/

/-- The harmonic Hamiltonian on the cycle graph C_N:
    H(q) = (1/2) Σᵢ (qᵢ - q_{i+1 mod N})²
    This is the discrete Laplacian energy whose spectrum gives the spectral gap.
    Uses `cycleSucc` from CycleGraph.lean. -/
def cycleHamiltonian (N : Nat) (hN : N ≥ 3) (q : Fin N → ℝ) : ℝ :=
  (1 / 2 : ℝ) * Finset.sum Finset.univ fun i : Fin N => (q i - q (cycleSucc N hN i)) ^ 2

/-- H(q) ≥ 0: the harmonic Hamiltonian is non-negative. -/
theorem cycleHamiltonian_nonneg (N : Nat) (hN : N ≥ 3) (q : Fin N → ℝ) :
    cycleHamiltonian N hN q ≥ 0 := by
  apply mul_nonneg (by norm_num : (1 / 2 : ℝ) ≥ 0)
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- H(c,...,c) = 0: a constant configuration has zero energy. -/
theorem cycleHamiltonian_const (N : Nat) (hN : N ≥ 3) (c : ℝ) :
    cycleHamiltonian N hN (fun _ => c) = 0 := by
  unfold cycleHamiltonian
  suffices h : Finset.sum Finset.univ (fun i : Fin N =>
      ((fun _ : Fin N => c) i - (fun _ : Fin N => c) (cycleSucc N hN i)) ^ 2) = 0 by
    rw [h, mul_zero]
  apply Finset.sum_eq_zero
  intro i _; ring

/-- H(q) = 0 ↔ ∀ i, qᵢ = q_{i+1}: zero energy characterizes constant configurations. -/
theorem cycleHamiltonian_eq_zero_iff (N : Nat) (hN : N ≥ 3) (q : Fin N → ℝ) :
    cycleHamiltonian N hN q = 0 ↔ ∀ i : Fin N, q i = q (cycleSucc N hN i) := by
  constructor
  · intro h
    unfold cycleHamiltonian at h
    have hsum : Finset.sum Finset.univ
        (fun i : Fin N => (q i - q (cycleSucc N hN i)) ^ 2) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · norm_num at h1
      · exact h1
    intro i
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (q j - q (cycleSucc N hN j)))).mp hsum i (Finset.mem_univ i)
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide)).mp hall)
  · intro h
    unfold cycleHamiltonian
    have : Finset.sum Finset.univ
        (fun i : Fin N => (q i - q (cycleSucc N hN i)) ^ 2) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [h i, sub_self]; ring
    rw [this, mul_zero]

/-! ## Poisson Bracket -/

/-- The Poisson bracket {f, g} = ω(∇f, ∇g) on phase space.
    Here ∇f and ∇g are phase-space gradient vectors. -/
def poissonBracket (n : Nat) (gf gg : PhaseVec n) : ℝ :=
  symplecticForm n gf gg

/-- {f, g} = -{g, f}: the Poisson bracket is skew-symmetric. -/
theorem poissonBracket_skew (n : Nat) (gf gg : PhaseVec n) :
    poissonBracket n gf gg = -poissonBracket n gg gf :=
  symplecticForm_skew n gf gg

/-- {f, f} = 0: the Poisson bracket is alternating. -/
theorem poissonBracket_self (n : Nat) (gf : PhaseVec n) :
    poissonBracket n gf gf = 0 :=
  symplecticForm_alt n gf

/-! ## Karmonic Admissibility -/

/-- Karmonic admissibility: a transition q_t → q_next is admissible if the
    Hamiltonian does not increase by more than ε.
    From the Karmonic Mesh paper: evolution constrained to the admissibility surface. -/
def karmonicAdmissible (N : Nat) (hN : N ≥ 3) (ε : ℝ) (q_t q_next : Fin N → ℝ) : Prop :=
  cycleHamiltonian N hN q_next ≤ cycleHamiltonian N hN q_t + ε

/-- The identity transition is always admissible (for ε ≥ 0). -/
theorem identity_admissible (N : Nat) (hN : N ≥ 3) (ε : ℝ) (hε : ε ≥ 0)
    (q : Fin N → ℝ) : karmonicAdmissible N hN ε q q := by
  unfold karmonicAdmissible; linarith

/-- Admissibility composes: q₁→q₂ within ε₁ and q₂→q₃ within ε₂
    implies q₁→q₃ within ε₁+ε₂. -/
theorem admissible_trans (N : Nat) (hN : N ≥ 3) (ε₁ ε₂ : ℝ)
    (q₁ q₂ q₃ : Fin N → ℝ)
    (h₁ : karmonicAdmissible N hN ε₁ q₁ q₂)
    (h₂ : karmonicAdmissible N hN ε₂ q₂ q₃) :
    karmonicAdmissible N hN (ε₁ + ε₂) q₁ q₃ := by
  unfold karmonicAdmissible at *; linarith

/-! ## Souriau Integrality / Symplectic Basis -/

/-- ω(eᵢ^q, eᵢ^p) = 1: the symplectic form evaluates to 1 on conjugate basis pairs.
    This is the Souriau integrality condition for geometric quantization. -/
theorem symplecticForm_unit_cell (n : Nat) (i : Fin n) :
    symplecticForm n (basisQ i) (basisP i) = 1 := by
  unfold symplecticForm basisQ basisP
  dsimp only []
  simp only [zero_mul, sub_zero]
  have : ∀ j : Fin n,
      (if j = i then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0) =
      if j = i then 1 else 0 := fun j => by split_ifs <;> simp
  simp_rw [this]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]

/-- ω(eᵢ^q, eⱼ^p) = δᵢⱼ: the symplectic form on basis pairs is the Kronecker delta.
    Encodes the canonical commutation relations [qᵢ, pⱼ] = iħδᵢⱼ. -/
theorem symplecticForm_basis (n : Nat) (i j : Fin n) :
    symplecticForm n (basisQ i) (basisP j) = if i = j then 1 else 0 := by
  unfold symplecticForm basisQ basisP
  dsimp only []
  simp only [zero_mul, sub_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]

end -- noncomputable section

end SpectralGap
