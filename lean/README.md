# Lean 4 Formal Verification — Tier 3

Formal proofs of spectral gap properties on the discrete torus T² = C_N x C_N,
built on **Mathlib** foundations. No axiomatized transcendentals.

## Verification Tiers

| Tier | Tool  | Proofs | What it proves |
|------|-------|--------|----------------|
| 1    | Kani  | 42     | Panic-freedom, integer safety |
| 2    | Verus | 29     | Functional correctness (axiomatized cos) |
| **3**| **Lean 4** | **17** | **Mathematical theorems from Mathlib** |

## Theorem Inventory

### ZModDistance.lean — 8 proven, 0 sorry'd
Port of `verus-proofs/distance.rs`. Pure integer arithmetic.

| Lean theorem | Verus proof | Status |
|-------------|-------------|--------|
| `circularDist_symm` | `circular_dist_symmetric` | Proven |
| `toroidalDist_symm` | `distance_symmetric` | Proven |
| `toroidalDist_self` | `distance_identity` | Proven |
| `circularDist_bounded` | `circular_dist_bounded` | Proven |
| `toroidalDist_bounded` | `distance_bounded` | Proven |
| `circularDist_triangle` | `circular_dist_triangle` | Proven |
| `toroidalDist_triangle` | `distance_triangle` | Proven |
| `toroidalDist_nondeg` | `distance_nondegenerate` | Proven |

### CycleGraph.lean — 4 proven, 0 sorry'd
Definition of C_N as `SimpleGraph (Fin N)`.

| Lean theorem | What it proves | Status |
|-------------|----------------|--------|
| `cycleGraph` (def) | Symmetric + irreflexive | Proven |
| `cycleSucc_adj` | (v+1)%N is adjacent to v | Proven |
| `cyclePred_adj` | (v-1)%N is adjacent to v | Proven |
| `cycleSucc_ne_pred` | Successor != predecessor (N>=3) | Proven |

### Torus.lean — 2 proven, 0 sorry'd
Definition of T² = C_N x C_N as `SimpleGraph (Fin N x Fin N)`.

| Lean theorem | What it proves | Status |
|-------------|----------------|--------|
| `torusGraph` (def) | Symmetric + irreflexive | Proven |
| `torusGraph_numVertices` | \|V\| = N^2 | Proven |

### SpectralGapDef.lean — 3 proven, 1 sorry'd
Spectral gap lambda_1 = 2 - 2cos(2pi/N) from Mathlib's `Real.cos`.

| Lean theorem | Verus proof | Status |
|-------------|-------------|--------|
| `spectralGap_pos` | `spectral_gap_positive` | Proven (N >= 3) |
| `spectralGap_le_four` | `spectral_gap_bounded` | Proven |
| `spectralGap_mono` | `spectral_gap_monotone` | Proven (N >= 3) |
| `spectralGap_at_two_pi` | `spectral_gap_zero_at_one` | Proven |
| `spectralGap_is_eigenvalue` | — | **sorry** (Phase 4) |

## Key Improvement Over Verus

Verus (Tier 2) axiomatizes cosine as an uninterpreted function with trusted
`#[verifier::external_body]` axioms: `cos_bounded`, `cos_zero`, `cos_two_pi`,
`cos_strict_less_one`, `cos_decreasing_0_pi`.

Lean 4 (Tier 3) uses Mathlib's **proven** `Real.cos` with:
- `Real.strictAntiOn_cos` — strict antitonicity on [0, pi], proven from analysis
- `Real.neg_one_le_cos` — lower bound, proven
- `Real.cos_two_pi` — periodicity, proven
- No trusted axioms. Zero axiomatized transcendentals.

## Deferred (Phase 4)

- **Eigenvalue formula proof**: Requires discrete Fourier basis on Z/NZ
- **Poincare inequality**: Depends on eigenvalue formula
- **Cheeger inequality**: Requires isoperimetric constant machinery
- **Aeneas Rust->Lean bridge**: Verify `torus.rs::spectral_gap()` against theorem

## Building

```bash
# Install Lean 4 (if needed)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y

# Build
cd lean/
lake update    # fetch Mathlib (first time only)
lake build     # 0 errors, 1 sorry warning
```

Requires: Lean 4 v4.27.0, Mathlib v4.27.0.
