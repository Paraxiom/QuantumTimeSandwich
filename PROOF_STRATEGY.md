# Proof Strategy: Spectral Gap as Domain-Invariant Bound

**Status**: Working document
**Author**: Sylvain Cormier, Paraxiom Technologies Inc.
**Date**: 2026-02-14
**Repository**: QuantumTimeSandwich

---

## 1. The Thesis

The spectral gap `lambda_1 = 2 - 2*cos(2*pi/N)` of the graph Laplacian on the
discrete torus T^2 = C_N x C_N is a **domain-invariant bound** that controls:

| Domain | What lambda_1 bounds | Where in code |
|--------|---------------------|---------------|
| **Quantum error correction** | Logical error suppression: P_L ~ exp(-alpha*N) | `toric-code-sim/` |
| **Coherence decay** | State fidelity: F(t) >= exp(-c*lambda_1*p*t) | `tonnetz-coherence-sim/src/coherence.rs` |
| **LLM hallucination** | Drift rate reduction: toroidal mask constrains random walk | `quantum-engine-sim/src/logit_drift.rs` |
| **Optimization** | Convergence rate: loss(t) ~ exp(-2*eta*lambda_1*t) | `quantum-engine-sim/src/covariant.rs` |
| **Random walk mixing** | Mixing time: t_mix = O(1/lambda_1) | `quantum-engine-sim/src/torus.rs` |

### What is proven (established mathematics)

- `lambda_1 = 2 - 2*cos(2*pi/N)` for the 4-connected N*N torus (elementary spectral graph theory)
- Poincare inequality on T^2: `||f - f_bar||^2 <= (1/lambda_1) * ||grad f||^2`
- Mixing time bound: `t_mix(eps) <= (1/lambda_1) * ln(|V|/eps)` (standard Markov chain theory)
- Toric code threshold: P_L ~ exp(-alpha*N) for i.i.d. noise below p_c (Dennis et al. 2002)
- Cheeger inequality: `h^2/2 <= lambda_1 <= 2h` (Cheeger 1970, Alon-Milman 1985)

### What is numerically validated (our code)

- Coherence decay rate matches `exp(-lambda_1*t)` across grid sizes (`tonnetz-coherence-sim`)
- Covariant descent convergence rate proportional to `eta * lambda_1` (`covariant.rs`)
- Toroidal mask drift reduction increases with grid size (`logit_drift.rs`)
- Biased noise shifts decoder threshold (`toric-code-sim` with `apply_biased_errors`)

### What needs formal proof (the gap)

The cross-domain claim: that these four phenomena are governed by the **same** spectral
gap is currently supported by numerical evidence and mathematical analogy. To make it a
theorem, we need:

1. **Coherence bound**: Prove that for depolarizing noise on qubits coupled via the
   Tonnetz topology, the state fidelity satisfies F(t) >= exp(-c*lambda_1*p*t) where
   c depends only on the noise model.

2. **Drift bound**: Prove that for a random walk with Sinkhorn-normalized toroidal
   transition kernel M, the probability of drift > d in t steps is bounded by
   exp(-d^2 * lambda_1 / t) (concentration inequality on T^2).

3. **Convergence-coherence equivalence**: Show that the convergence rate of gradient
   descent on T^2 and the coherence decay rate of a quantum system on the same lattice
   are both determined by lambda_1 through the Poincare inequality.

---

## 2. Proof Toolchain

### Recommended stack

```
Simulations:     Rust (QuantumTimeSandwich)
Formal proofs:   Lean 4 + Mathlib
Rust -> Lean:    Aeneas (translates Rust MIR to Lean 4)
Safety proofs:   Kani (bounded model checking, panic/overflow/UB)
Crypto proofs:   hax (Rust -> F*, following libcrux model)
SMT checking:    Verus (for functional correctness in Rust syntax)
```

### Tool details

| Tool | What it does | Maturity | Install |
|------|-------------|----------|---------|
| **Kani** (AWS) | Bounded model checking for Rust | Production | `cargo install kani-verifier && cargo kani setup` |
| **Verus** (MSR) | SMT-based proof annotations in Rust | Research-grade | github.com/verus-lang/verus |
| **Aeneas** | Rust MIR -> Lean 4 / F* / Coq | Research, used by MSFT | github.com/AeneasVerif/aeneas |
| **hax** (Cryspen) | Rust -> F* for crypto verification | Production for crypto | github.com/cryspen/hax |
| **ESBMC** | SMT bounded model checking | Emerging for Rust | github.com/esbmc/esbmc |
| **Creusot** (Inria) | Deductive verification via Why3 | Research | github.com/xldenis/creusot |

### Why Lean 4 for the proofs

- **Mathlib** has linear algebra, spectral theory foundations, topological spaces
- Aeneas bridges Rust -> Lean for implementation verification
- $100M+ funding behind Lean ecosystem (Harmonic AI, 2025)
- Best community momentum of any proof assistant
- Dependent types + tactic-based proofs

### Why Rust for the code

- Existing 129 source files, 9 crates, published on crates.io
- Ownership system prevents entire classes of bugs without runtime cost
- Kani/Verus/hax provide multiple verification angles
- libcrux proves verified PQC is possible in Rust
- No viable alternative matches Rust's performance + safety + ecosystem

---

## 3. Crate Ecosystem for Augmentation

### Spectral graph theory (must-add)

| Crate | Purpose | Status |
|-------|---------|--------|
| `faer` | Pure Rust eigenvalue decomposition (dense + sparse) | Add to quantum-engine-sim |
| `lanczos` | Iterative extremal eigenvalue computation | Add for large-scale spectral gap |
| `scirs2-sparse` | Graph Laplacian construction (`csgraph` module) | Evaluate for integration |
| `petgraph` | Graph representation (already implicit in coupling maps) | Consider for generalization |

### PQC verification reference

| Crate | Purpose | Status |
|-------|---------|--------|
| `libcrux` | Formally verified ML-KEM (hax + F*) | Reference model for qssh/qssl |
| `ml-kem` (RustCrypto) | Pure Rust ML-KEM, NIST vectors | Alternative if no verification needed |
| `ml-dsa` (RustCrypto) | Pure Rust ML-DSA, NIST vectors | For signature schemes |

### Verification tools

| Crate | Purpose | Status |
|-------|---------|--------|
| `kani-verifier` | Prove absence of panics/overflow | Add to CI |
| `z3` (v0.13.3) | SMT solver bindings | Available if needed for Verus |

---

## 4. Current Code Map

### What exists and works (41 tests passing in toric-code-sim alone)

```
toric-code-sim/
  src/lattice.rs        -- ToricLattice, Edge, EdgeDir, Pauli frame
  src/syndrome.rs       -- Syndrome measurement, e/m particles
  src/anyon.rs          -- AnyonType, fusion rules, pair creation
  src/braiding.rs       -- Braiding phase, logical operators
  src/simulation.rs     -- Monte Carlo threshold, apply_random_errors,
                           apply_biased_errors (NEW), greedy decoder

tonnetz-coherence-sim/
  src/topology.rs       -- CouplingTopology (Toroidal, Linear, Random, AllToAll)
  src/coherence.rs      -- state_fidelity, CoherenceTracker,
                           theoretical_decay_rate (lambda_1 formula)
  src/noise.rs          -- NoiseChannel (Depolarizing)
  src/simulation.rs     -- SimulationConfig, run_single_trial

quantum-engine-sim/
  src/torus.rs          -- TorusLattice, spectral_gap(), spectrum(),
                           mode_frequencies(), mixing_time
  src/covariant.rs      -- TorusPoint, TorusLoss, LatticeLoss, ContinuumLoss,
                           descent(), convergence_validation()
  src/logit_drift.rs    -- DriftConfig, simulate_drift(), benchmark_data(),
                           spectral_decay_curves()
  src/toric_code.rs     -- ToricCode integration
  src/vacuum.rs         -- casimir_energy(), dynamical_casimir(), unruh_analysis()
  src/engine.rs         -- EngineConfig, quantum engine cycle
```

### What is dead (to remove)

```
QuantumTimeSandwich/grpc/           -- 10 CVEs, mock crypto, unused OQS import
QuantumTimeSandwich/src/grpc/       -- skeleton oqs_kex_rpc, never imported
```

---

## 5. TODOs

### Phase 0: Cleanup (immediate) — COMPLETE

- [x] **Remove grpc crate**: Deleted (already removed in prior cleanup)
- [x] **Remove grpc skeleton**: Deleted (already removed in prior cleanup)
- [x] **cargo update iterators**: Bumped all deps across all crates (2026-02-15)
- [x] **Re-audit**: 0 vulnerabilities across all crates (1 unmaintained warning: paste via faer-core dev-dep)

### Phase 1: Numerical evidence (code) — COMPLETE

- [x] **Spectral gap computation**: `spectral.rs` — nalgebra eigenvalue solver,
      GraphLaplacian for cycle/torus/linear/arbitrary graphs, 16 tests cross-validating
      against analytic formula. Verified for N=4..32.
- [x] **Biased threshold sweep**: `biased_threshold_sweep()` in toric-code-sim with
      bias ratios [1.0, 1.5, 2.0, 3.0]. Validates unity-bias ≈ isotropic, 46 tests.
- [x] **Drift-vs-spectral-gap regression**: `spectral_gap_regression()` in logit_drift.rs.
      Sweeps N=4..20, verifies positive correlation between λ₁ and drift_reduction.
      4 new tests (51 total in quantum-engine-sim).
- [x] **Coherence-vs-spectral-gap regression**: Sweep grid sizes [2,3] (fast) + [2,3,4]
      (extended, #[ignore]). Verifies coherence time increases with 1/λ₁, theoretical
      ratio matches exactly. 4 new tests (54 total in tonnetz-coherence-sim).

### Phase 2: Safety proofs (Kani + Verus) — COMPLETE

- [x] **Kani Tier 1** (42 proofs): panic-freedom, integer safety, symbolic distance proofs
- [x] **Verus Tier 2** (29 proofs): functional correctness — spectral_gap > 0, bounded,
      monotone; distance metric axioms (8, axiom-free); coherence time positivity,
      monotonicity, Tonnetz enhancement; thermal occupation bounds; engine cycle
      work/protection/efficiency bounds. See `quantum-engine-sim/verus-proofs/`.

### Phase 3: Formal proofs (Lean 4)

- [ ] **Formalize Poincare inequality on T^2 in Lean 4 + Mathlib**:
      `||f - f_bar||^2 <= (1/lambda_1) * ||grad f||^2`
- [ ] **Formalize spectral gap formula**:
      Prove `lambda_1 = 2 - 2*cos(2*pi/N)` for cycle graph C_N
- [ ] **Formalize Cheeger inequality for T^2**:
      `h^2/2 <= lambda_1 <= 2h` with explicit h for the torus
- [ ] **Use Aeneas to verify Rust implementation**:
      Translate `torus.rs::spectral_gap()` to Lean, prove it matches the theorem

### Phase 4: Cross-domain proof (the thesis)

- [ ] **State the unified theorem precisely** (see Section 1)
- [ ] **Prove coherence bound**: F(t) >= exp(-c*lambda_1*p*t) for Tonnetz coupling
- [ ] **Prove drift concentration**: P(drift > d) <= exp(-d^2*lambda_1/t)
- [ ] **Prove convergence-coherence equivalence**: Both rates = lambda_1 via Poincare
- [ ] **Write paper**: Combine proofs + numerical evidence + code references

### Phase 5: PQC verification (future)

- [ ] **Evaluate libcrux/hax pipeline** for qssh and qssl
- [ ] **Port qssh key exchange to use libcrux ML-KEM** (formally verified)
- [ ] **Apply hax to verify qssl TLS handshake**

---

## 6. Key References

### Spectral theory
- Cheeger, J. (1970). "A lower bound for the smallest eigenvalue of the Laplacian"
- Buser, P. (1982). "A note on the isoperimetric constant"
- Alon, N. & Milman, V. (1985). "lambda_1, isoperimetric inequalities for graphs"
- Lubotzky, A., Phillips, R., Sarnak, P. (1988). "Ramanujan graphs"
- Hoory, Linial, Wigderson (2006). "Expander graphs and their applications" (survey)

### Toric code
- Kitaev, A. (2003). "Fault-tolerant quantum computation by anyons"
- Dennis, Kitaev, Landahl, Preskill (2002). "Topological quantum memory"
- Bravyi, Hastings, Michalakis (2010). "Topological order at nonzero temperature"

### Quantum information
- Muller-Lennert, Dupuis, Szehr, Fehr, Tomamichel (2013). "Sandwiched Renyi divergence"
- Wilde, Winter, Yang (2014). "Strong converse for classical capacity"
- Ben-Aroya, Ta-Shma (arXiv:0709.1142). "Quantum expanders from Cayley graphs"

### Toroidal logit bias
- Cormier, S. (2026). "Topological Constraints for Coherent Language Models"
  DOI: 10.5281/zenodo.18624950

### Verified cryptography
- Cryspen. "Verifying Libcrux's ML-KEM" (cryspen.com/post/ml-kem-verification/)
- hax paper: IACR ePrint 2025/142

---

## 7. On AI Generating Binary Directly (Musk Claim)

Musk has claimed AI will generate machine code directly, bypassing compilers. Assessment:

**What matters is not skipping compilation — it's proof-carrying code.**

- Compilers aren't the bottleneck. LLVM compiles Rust to optimized x86 in seconds.
- Skipping the compiler loses all static guarantees (borrow checker, type system, lifetimes).
- Verifying binary is orders of magnitude harder than verifying source.
- The real frontier: AI that writes **formally verified source** (see AutoVerus, POPL 2025:
  LLM-automated proof generation with 90%+ success rate on Verus benchmarks).

The future is AI that writes Rust + Lean proofs, not AI that writes raw bytes.

---

## 8. Language Decision

**Stay with Rust.** Rationale:

| Criterion | Rust | Lean 4 | F* | Idris 2 | ATS |
|-----------|------|--------|-----|---------|-----|
| Performance | Native | Good | Via C | Moderate | Near-C |
| Proofs | Kani/Verus/Aeneas | Built-in | Built-in | Built-in | Built-in |
| Ecosystem | Massive | Mathlib | HACL* | Small | Tiny |
| PQC libs | libcrux, ml-kem | None | HACL* | None | None |
| Interop | Aeneas -> Lean | Aeneas <- Rust | hax <- Rust | None | None |

**Dual-language strategy**: Rust for implementation, Lean 4 for proofs, Aeneas for the bridge.
