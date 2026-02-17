# QuantumTimeSandwich

A Rust quantum computing platform that merges quantum algorithms, cryptographic protocols, and topological simulations.

## Why "Quantum Time Sandwich"?

In quantum mechanics, everything happens **between two moments in time**. The present quantum state is always sandwiched between temporal boundary conditions — past preparation and future measurement. This is not just an engineering pattern. It is the physics.

The name captures a principle that appears across all of quantum theory:

1. **Bra-Ket Sandwich** — Every quantum observable is an operator sandwiched between temporal states: the bra (future) and ket (past) in Dirac notation.

2. **Aharonov Two-State Vector Formalism** — The present measurement is sandwiched between a pre-selected state from the past and a post-selected state from the future. Quantum mechanics is time-symmetric — the future constrains the present just as much as the past (Aharonov, Bergmann, Lebowitz, 1964).

3. **Wheeler's Delayed Choice** — A future measurement choice retroactively determines past photon behavior. The quantum event is time-sandwiched by a decision that hasn't happened yet.

4. **Quantum Circuit Model** — State preparation, gate operations, and measurement form a temporal sandwich. All quantum computation is bounded by two moments in time.

5. **Quantum Error Correction Cycles** — Data qubits persist through time, sandwiched between repeated syndrome measurements at each timestep. The decoder works across this temporal sandwich.

6. **Toric Code Space-Time Lattice** — 2D toric code layers stack in time. Vertex and plaquette operators sandwich qubits across stabilizer cycles. Errors are decoded across the full space-time sandwich.

7. **Sandwiched Renyi Divergence** — In quantum information theory, the density matrix is sandwiched between reference states across time, bounding quantum channel capacity and QKD security (Wilde et al., Muller-Lennert et al., 2013).

8. **Sandwich Quantization** — In gauge field theory, physical states are defined by requiring constraints to vanish when sandwiched between any two physical states across time.

9. **Quantum Gravity Sandwich Theorem** — Initial and final 3-geometries sandwich the 4D spacetime evolution between them. The classical sandwich theorem emerges from the semiclassical limit of the quantum propagation amplitude.

10. **Quantum Channel Sandwich** — Encoding before, noise during, decoding after. Every quantum communication protocol is a temporal sandwich.

11. **Topological Boundary Sandwich** — In topological quantum computing (Levin-Wen, Walker-Wang models), bulk topological order is sandwiched between boundary conditions that constrain which anyons can exist.

**The unifying principle: quantum mechanics is what happens between two temporal boundaries.** Every quantum protocol — from a single measurement to fault-tolerant quantum computing — is constrained from both ends in time.

This platform implements all layers of the sandwich in Rust.

## Install

```bash
git clone https://github.com/Paraxiom/QuantumTimeSandwich.git
cd QuantumTimeSandwich/[subdirectory]
cargo build
cargo test
```

## Crates

| Crate | Description | crates.io |
|-------|-------------|-----------|
| `QuantumTimeSandwich` | Core quantum gate simulation (Deutsch, Grover, Bell, CSWAP) | [v1.4.0](https://crates.io/crates/QuantumTimeSandwich) |
| `QuantumTimeSandwich-iterators` | Tensor product matrix multiplication iterators | [v1.4.0](https://crates.io/crates/QuantumTimeSandwich-iterators) |
| `QuantumTimeSandwich-macros` | Procedural macros for quantum circuit construction | [v1.0.0](https://crates.io/crates/QuantumTimeSandwich-macros) |
| `bb84` | BB84 quantum key distribution with AES integration and eavesdrop detection | — |
| `tonnetz-coherence-sim` | Toroidal coherence simulation on Tonnetz topology | — |
| `toric-code-sim` | Kitaev toric code simulator with anyonic excitations and braiding on T² | — |
| `toric-doppler-sim` | Toric code visualization with Doppler effects (Egui) | — |
| `unit_circle_state_machine` | Unit circle state machine for phase tracking | — |

## Project Structure

### BB84 — Quantum Key Distribution
- **Location:** `bb84/`
- BB84 protocol with basis selection, eavesdropping detection, privacy amplification
- Post-quantum cryptography: Learning With Errors (LWE), Ring-LWE
- AES-GCM integration with quantum-derived keys
- **Examples:** `bb84_simulation`, `eavesdropping_demo`, `lattice_crypto_demo`, `lwe-demo`, `ring-lwe-demo`

### QuantumTimeSandwich Core
- **Location:** `QuantumTimeSandwich/`
- Quantum gate simulation, state vector manipulation, boolean circuits
- Parallel execution via Rayon, exact arithmetic via `num-rational`
- **Examples:** `bell_inequalities`, `grovers`, `dense_coding`, `deutch`, `cswap`

### Tonnetz Coherence Simulation
- **Location:** `tonnetz-coherence-sim/`
- Numerical validation of toroidal coherence on quantum circuits
- Same Tonnetz topology used in [Topological Coherence](https://doi.org/10.5281/zenodo.18624950) for LLM hallucination reduction

### Toric Code Simulation
- **Location:** `toric-code-sim/`
- Kitaev toric code on T² — Pauli frame tracking, anyonic excitations, braiding
- The lattice sandwich: vertex and plaquette operators sandwich physical qubits

### Toric Doppler Simulation
- **Location:** `toric-doppler-sim/`
- Interactive visualization of toric code dynamics (Egui GUI)

## Cross-Domain Coherence

The same toroidal geometry that constrains drift in quantum error correction (toric code) also reduces hallucination in large language models (toroidal logit bias). The spectral gap is a geometric property, not domain-specific.

- **Quantum:** `toric-code-sim`, `tonnetz-coherence-sim`
- **AI/ML:** [topological-coherence](https://github.com/Paraxiom/topological-coherence) (+19.5% TruthfulQA)
- **Blockchain:** [QuantumHarmony](https://github.com/Paraxiom/quantumharmony) (Proof of Coherence consensus)

Paper: [Topological Constraints for Coherent Language Models](https://doi.org/10.5281/zenodo.18624950)

## Formal Verification

3-tier verification pipeline — zero sorries, zero axiomatized transcendentals.

| Tier | Tool | Scope | Count |
|------|------|-------|-------|
| **Tier 1** | Kani (AWS) | Panic-freedom, integer overflow, UB | 42 harnesses |
| **Tier 2** | Verus (MSR) | Functional correctness via Z3 | 29 proofs |
| **Tier 3** | Lean 4 + Mathlib | Mathematical foundations | 48 theorems |

**Lean 4 proof files** (`lean/SpectralGap/`):

| File | Theorems | Description |
|------|----------|-------------|
| `Basic.lean` | 0 | Definitions and foundations |
| `SpectralGapDef.lean` | 9 | Spectral gap definition, positivity for N >= 3 |
| `FourierBasis.lean` | 11 | Eigenvector proof, minimality (spectral gap is smallest nonzero eigenvalue) |
| `CycleGraph.lean` | 3 | Cycle graph properties |
| `ZModDistance.lean` | 12 | Distance metrics on Z/nZ |
| `ProductGraph.lean` | 8 | Product spectral gap: min(lambda_1(C_N), lambda_1(C_M)), 3D torus, 8x8x8 positivity |
| `Asymptotics.lean` | 4 | Upper bound lambda_1(N) <= (2pi/N)^2 from cos Taylor, O(1/N^2) convergence |
| `Torus.lean` | 1 | Toroidal topology |
| **Total** | **48** | |

```bash
cd lean && lake build  # 0 errors, 0 sorries
```

**Paper**: [562 Lean 4 Theorems for Post-Quantum Infrastructure](https://doi.org/10.5281/zenodo.18663125) (Zenodo, Feb 2026)

## License

MIT. Based on contributions from [RustQIP](https://github.com/Renmusxd/RustQIP).

## Author

Sylvain Cormier — [Paraxiom Research](https://paraxiom.org) — sylvain@paraxiom.org
