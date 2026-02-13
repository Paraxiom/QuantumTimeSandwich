# Quantum Engine Simulator

Unified simulation framework chaining five layers of toroidal physics into a single "quantum engine" pipeline.

## The Five Layers

```
Atlas Spectral Gap (λ₁ = 1)
  ↓ geometric principle
Tonnetz Coherence (λ₁ = 2 - 2cos(2π/N))
  ↓ decay rate
Toric Code Protection (P_L ~ exp(-αN))
  ↓ error suppression
Vacuum Physics (Casimir, Unruh, DCE on T²)
  ↓ energy extraction
Quantum Engine Cycle (vacuum → work)
```

The spectral gap of T² is a geometric invariant — not domain-specific. It bounds drift in LLMs (toroidal logit bias), suppresses errors in quantum codes (toric code), and protects vacuum states from decoherence (Casimir cavity). Same torus, same math, five applications.

## Analog Gravity Connection

The engine cycle on T² maps to analog gravity phenomena:

- **Unruh effect**: The spectral gap creates a minimum detectable acceleration. Below this threshold, the toroidal vacuum is topologically protected from thermal excitation — the geometry makes the vacuum "rigid."

- **Dynamical Casimir effect**: Boundary oscillation of the toroidal cavity produces photon pairs from the vacuum. Only modes above the spectral gap are excited — topological protection prevents sub-gap vacuum noise.

- **Casimir energy**: The vacuum energy on T² scales as E ~ -ℏc/L². Compressing the torus stores energy in the vacuum field. This is the "fuel" for the engine cycle.

- **Engine cycle** (analog of Otto cycle on quantum vacuum):
  1. **Compress** (L_max → L_min): Blue-shift mode frequencies, increase vacuum energy
  2. **Extract**: Oscillate boundary (dynamical Casimir), produce coherent photon pairs
  3. **Expand** (L_min → L_max): Release stored elastic energy
  4. **Idle**: Vacuum re-thermalizes, protected by spectral gap from decoherence

## Run

```bash
cargo test    # 18 tests
cargo run     # full 5-layer simulation
```

## Output

The simulator prints results for each layer:

1. **Spectral gap** — eigenvalues of the torus Laplacian for N = 4..32
2. **Coherence** — T₂ enhancement from toroidal coupling (toroidal vs linear vs complete graph)
3. **Toric code** — Monte Carlo logical error rates showing threshold behavior
4. **Vacuum physics** — Casimir energy, Unruh threshold, dynamical Casimir photon production
5. **Engine cycle** — energy budget, topological protection factor, power output, scaling study

## Modules

| Module | Description |
|--------|-------------|
| `torus` | T² lattice geometry, Laplacian spectrum, spectral gap |
| `coherence` | Tonnetz-enhanced coherence times, topology comparison |
| `toric_code` | Kitaev toric code Monte Carlo, error suppression |
| `vacuum` | Casimir energy, Unruh effect, dynamical Casimir on T² |
| `engine` | Quantum engine cycle simulation, scaling analysis |
| `units` | Physical constants (ℏ, c, k_B) |

## Cross-Domain Evidence

The same toroidal geometry constrains drift across three domains:

| Domain | Observable | Result |
|--------|-----------|--------|
| **LLM** | TruthfulQA | +19.5% (Phi-2), +2.8pp (4 models via API) |
| **Quantum** | Logical error rate | P_L ~ exp(-αN) below p_c ≈ 10.3% |
| **Vacuum** | Casimir energy | E ~ -ℏc/L² (topologically protected) |

## References

- Cormier (2026), ["Topological Constraints for Coherent Language Models"](https://doi.org/10.5281/zenodo.18624950)
- Kitaev (2003), "Fault-tolerant quantum computation by anyons"
- Casimir (1948), "On the attraction between two perfectly conducting plates"
- Unruh (1976), "Notes on black-hole evaporation"
- Moore (1970), "Quantum theory of the electromagnetic field in a variable-length one-dimensional cavity"
- Aharonov, Bergmann, Lebowitz (1964), "Time symmetry in the quantum process of measurement"

## License

MIT — [Paraxiom Research](https://paraxiom.org)
