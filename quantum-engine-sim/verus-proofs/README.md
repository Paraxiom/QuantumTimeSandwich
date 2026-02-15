# Verus Formal Verification — quantum-engine-sim

**Tier 2** of the 3-tier verification strategy:

| Tier | Tool | What it proves | Status |
|------|------|----------------|--------|
| 1 | **Kani** (CBMC) | Panic-freedom, integer safety | 42 proofs |
| 2 | **Verus** (Z3 SMT) | Functional correctness, value properties | **29 proofs** |
| 3 | Lean 4 | Full mathematical theorems | Planned |

## Why Verus?

Kani's CBMC backend models transcendental functions (`cos`, `sin`, `exp`, `ln`)
**non-deterministically** — it can prove that `spectral_gap()` never panics, but
cannot verify that the result is positive. Verus uses Z3 SMT solving with
axiomatized specs for transcendentals, enabling proofs about **values**.

## Architecture

Standalone `.rs` files compiled by Verus independently (Verus uses its own `rustc`
fork and cannot consume `nalgebra`/`egui`/`rand` dependencies). Each file is a
verified re-implementation of key functions from `src/`, using Verus's `real` type
for exact mathematical reasoning.

```
verus-proofs/
├── spectral_gap.rs    — λ₁ = 2-2cos(2π/N): positivity, bounds, monotonicity  (5 verified)
├── distance.rs        — Toroidal Manhattan distance: full metric axioms        (8 verified)
├── coherence.rs       — τ = -ln(ε)/λ₁: positivity, monotonicity, enhancement  (6 verified)
├── thermal.rs         — n_th = 1/(e^x-1): non-negativity, monotonicity, limit  (5 verified)
├── engine.rs          — Engine cycle: work ≥ 0, protection ∈ [0,1], η ∈ [0,1] (5 verified)
├── Makefile           — Verification commands
└── README.md          — This file
```

## Proof Inventory (29 total, 0 errors)

### spectral_gap.rs (5 verified)
| Proof | Statement | Axioms used |
|-------|-----------|-------------|
| `theta_in_range` | 0 < 2π/N ≤ π < 2π for N ≥ 2 | TWO_PI > 0, div helpers |
| `spectral_gap_positive` | λ₁ > 0 for N ≥ 2 | cos < 1 on (0,2π) |
| `spectral_gap_bounded` | 0 < λ₁ ≤ 4 | cos ∈ [-1,1] |
| `spectral_gap_monotone` | λ₁(N+1) < λ₁(N) | cos decreasing on [0,π] |
| `spectral_gap_zero_at_one` | λ₁(1) = 0 | cos(2π) = 1 |

### distance.rs (8 verified) — **axiom-free (pure integer)**
| Proof | Statement |
|-------|-----------|
| `circular_dist_symmetric` | circ(a,b,N) = circ(b,a,N) |
| `distance_symmetric` | d(a,b) = d(b,a) |
| `distance_identity` | d(a,a) = 0 |
| `circular_dist_bounded` | circ(a,b,N) ≤ N/2 |
| `distance_bounded` | d(a,b) ≤ N |
| `circular_dist_triangle` | circ(a,c,N) ≤ circ(a,b,N) + circ(b,c,N) |
| `distance_triangle` | d(a,c) ≤ d(a,b) + d(b,c) |
| `distance_nondegenerate` | d(a,b) = 0 ⟹ a = b |

### coherence.rs (6 verified)
| Proof | Statement | Axioms used |
|-------|-----------|-------------|
| `coherence_time_positive` | τ > 0 when λ₁ > 0, 0 < ε < 1 | ln < 0 below 1 |
| `coherence_time_monotone` | gap₁ < gap₂ ⟹ τ₁ > τ₂ | ln < 0, div ordering |
| `coherence_time_threshold_monotone` | ε₁ < ε₂ ⟹ τ₁ > τ₂ | ln monotone |
| `tonnetz_enhancement_at_least_one` | enhancement ≥ 1 | exp > 0 |
| `tonnetz_enhanced_t2_geq_bare` | enhanced T₂ ≥ bare T₂ | exp > 0, mul_ge_one |
| `torus_coherence_time_positive` | τ(N, ε) > 0 for N ≥ 2 | cos < 1, ln < 0 |

### thermal.rs (5 verified)
| Proof | Statement | Axioms used |
|-------|-----------|-------------|
| `thermal_non_negative` | n_th > 0 for x > 0 | exp > 1 for x > 0 |
| `thermal_decreasing_in_x` | x₁ < x₂ ⟹ n_th(x₁) > n_th(x₂) | exp monotone |
| `thermal_monotone_in_x_values` | colder (larger x) → fewer photons | thermal_decreasing |
| `thermal_upper_bound` | n_th(x) ≤ 1/x | exp ≥ 1+x |
| `thermal_vanishes_bound` | x·ε > 1 ⟹ n_th(x) < ε | exp ≥ 1+x, reciprocal |

### engine.rs (5 verified)
| Proof | Statement | Axioms used |
|-------|-----------|-------------|
| `work_non_negative` | \|E₁-E₂\| ≥ 0 | (none — pure arithmetic) |
| `protection_bounded` | 0 < exp(-λ₁/γ) ≤ 1 | exp > 0, exp ≤ 1 for x ≤ 0 |
| `protection_monotone` | gap₁ < gap₂ ⟹ prot₂ < prot₁ | exp monotone |
| `efficiency_bounded` | 0 ≤ η ≤ 1 when W_net ≤ W_comp | div ordering |
| `work_symmetric` | \|E₁-E₂\| = \|E₂-E₁\| | (none — pure arithmetic) |

## Trusted Axiom Base

All proofs reduce to these trusted properties of transcendental functions:

**cos:** bounded in [-1,1], cos(0)=1, cos(2π)=1, cos < 1 on (0,2π), decreasing on [0,π]

**ln:** negative below 1, strictly increasing

**exp:** positive everywhere, strictly increasing, exp(0)=1, exp(x) ≤ 1 for x ≤ 0, exp(x) ≥ 1+x for x > 0

**Arithmetic:** division/multiplication ordering lemmas for nonlinear real arithmetic (Z3 workarounds)

## Source Mapping

| Verus proof file | Source file | Key function |
|------------------|------------|--------------|
| spectral_gap.rs | src/torus.rs:47 | `spectral_gap()` |
| distance.rs | src/torus.rs:129, src/logit_drift.rs:153 | `distance()`, `toroidal_distance()` |
| coherence.rs | src/coherence.rs:72 | `coherence_time_normalized()` |
| thermal.rs | src/vacuum.rs:83 | `thermal_occupation()` |
| engine.rs | src/engine.rs:187 | `run_cycle()` |

## Running

```bash
# Install Verus (macOS arm64)
curl -LO https://github.com/verus-lang/verus/releases/latest/download/verus-aarch64-apple-darwin.zip
unzip verus-aarch64-apple-darwin.zip -d ~/.verus/

# Verify all proofs
cd quantum-engine-sim/verus-proofs
make all

# Quick check (axiom-free integer proofs only)
make check

# See proof summary
make summary
```

## Verification Coverage Across Tiers

| Property | Kani (Tier 1) | Verus (Tier 2) |
|----------|--------------|----------------|
| `spectral_gap()` no panic | **42 proofs** | — |
| `spectral_gap() > 0` | ✗ (cos non-det) | **verified** |
| `spectral_gap() ≤ 4` | ✗ | **verified** |
| `spectral_gap()` monotone in N | ✗ | **verified** |
| `distance()` symmetric | verified (symbolic) | **verified** |
| `distance()` triangle inequality | ✗ (too expensive) | **verified** |
| `distance()` bounded | verified (symbolic) | **verified** |
| `distance()` non-degenerate | ✗ | **verified** |
| `coherence_time() > 0` | ✗ (ln non-det) | **verified** |
| `thermal_occupation() > 0` | verified (symbolic) | **verified** |
| `thermal_occupation()` monotone | ✗ (exp non-det) | **verified** |
| `thermal_occupation()` vanishes at T→0 | ✗ | **verified** |
| `protection_factor ∈ (0,1]` | ✗ | **verified** |
| `efficiency ∈ [0,1]` | ✗ | **verified** |
| Tonnetz enhancement ≥ 1 | ✗ | **verified** |
