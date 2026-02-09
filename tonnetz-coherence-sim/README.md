# tonnetz-coherence-sim

Numerical simulation of toroidal coherence scaling on quantum hardware, bridging the [QuantumTimeSandwich](../QuantumTimeSandwich/) circuit simulator with [Tonnetz topology](../../topological-coherence/) from the topological-coherence crate.

## Hypothesis

Qubits coupled through a **toroidal (Tonnetz) topology** exhibit **sqrt(N) coherence scaling** compared to O(1) for random or linear coupling. This follows from the spectral gap advantage of the torus Laplacian and has been validated empirically in the LLM domain (+2.8pp TruthfulQA across 4 models, DOI: 10.5281/zenodo.18516477).

This crate provides the numerical simulation bridge between:
- **Theory**: Analytical predictions from Tonnetz spectral gap (topological-coherence crate)
- **LLM validation**: Toroidal logit bias experiments showing +40% error reduction
- **Quantum hardware**: Simulated qubit arrays with noise and topology-dependent coupling

## Architecture

```
noise.rs       — Quantum noise channels (depolarizing, dephasing, amplitude damping)
topology.rs    — Coupling topologies (toroidal, linear, random, all-to-all)
coherence.rs   — State fidelity and coherence time tracking
simulation.rs  — Monte Carlo experiment runner
```

## Quick Start

```bash
# Check compilation
cargo check

# Run tests
cargo test

# Compare topologies at fixed N=9
cargo run --example topology_comparison

# Scaling experiment across N = {4, 9, 16}
cargo run --example scaling_experiment
```

## Noise Model

Noise is implemented as Monte Carlo sampling over Kraus operators applied through QTS's `apply_matrix` interface:

| Channel | Kraus Operators | Physical Model |
|---------|----------------|----------------|
| Depolarizing(p) | {sqrt(1-p)I, sqrt(p/3)X, sqrt(p/3)Y, sqrt(p/3)Z} | Uniform random errors |
| Dephasing(p) | {sqrt(1-p)I, sqrt(p)Z} | Phase noise (T2) |
| AmplitudeDamping(gamma) | {[[1,0],[0,sqrt(1-gamma)]], [[0,sqrt(gamma)],[0,0]]} | Energy relaxation (T1) |

## Coupling Topologies

| Topology | Edge Weight | Expected Scaling |
|----------|-------------|-----------------|
| **Toroidal** | exp(-d_T(i,j)) | sqrt(N) |
| Linear | 1 if \|i-j\|=1 | O(1) |
| Random (ER) | 1 with density d | O(log N) |
| All-to-all | 1 for all pairs | O(N) |

## Dependencies

- **QuantumTimeSandwich** (v1.4.0) — Circuit simulation, gate application, state extraction
- **topological-coherence** (v0.1.2) — Tonnetz geometry, spectral gap, drift measurement
- **num-complex** — Complex number arithmetic
- **rand** — Monte Carlo noise sampling

## References

- Cormier, S. (2026). "Toroidal Logit Bias." Zenodo. DOI: 10.5281/zenodo.18516477
- Cormier, S. (2025). "Topological Coherence." Zenodo. DOI: 10.5281/zenodo.14538933
