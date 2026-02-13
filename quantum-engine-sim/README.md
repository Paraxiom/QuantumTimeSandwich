# Quantum Engine Simulator

Unified simulation framework chaining five layers of toroidal physics into a single "quantum engine" pipeline, with a GPU-accelerated egui/wgpu visualizer.

## Quick Start

```bash
cargo test              # 28 tests
cargo run               # CLI: full 5-layer text output
cargo run --bin gui     # GUI: interactive visualizer with 3D torus
```

## The Five Layers

```
Atlas Spectral Gap (lambda_1 = 1)
  | geometric principle
Tonnetz Coherence (lambda_1 = 2 - 2cos(2pi/N))
  | decay rate
Toric Code Protection (P_L ~ exp(-alpha*N))
  | error suppression
Vacuum Physics (Casimir, Unruh, DCE on T^2)
  | energy extraction
Quantum Engine Cycle (vacuum -> work)
```

The spectral gap of T^2 is a geometric invariant -- not domain-specific. It bounds drift in LLMs (toroidal logit bias), suppresses errors in quantum codes (toric code), and protects vacuum states from decoherence (Casimir cavity). Same torus, same math, five applications.

## GUI Visualizer

The interactive visualizer (`cargo run --bin gui`) provides:

### Layout

```
+---------------+--------------------------------------+---------------+
|               |                                      |               |
|   Presets     |   3D Rotating Torus (T^2)            |   Engine      |
|   + Sliders   |   + engine cycle animation           |   Results     |
|               |   + covariant descent paths           |   Readout     |
|               |   + DCE photon sparks                |               |
|               +------------+-----------+-------------+               |
|               | Energy     | Conv Rate | Scaling     |               |
|               | Budget     | vs lambda | Study       |               |
|               | (bars)     | (scatter) | (lines)     |               |
+---------------+------------+-----------+-------------+---------------+
```

### Controls (Left Panel)

**Presets** -- one-click regime selection:
- **Microwave**: 3 cm superconducting cavity, 20 mK, Q ~ 10^10 (default)
- **Mid-IR**: 10 um photonic crystal, 300 K, Q ~ 10^6
- **Optical**: 50 um silica microtoroid, 4 K, Q ~ 10^8

**Cavity Parameters** (logarithmic sliders spanning 6 orders of magnitude):
- L_max, L_min: 1 um to 10 cm (covers microwave through optical)
- Temperature: 1 mK to 300 K
- Decoherence rate gamma: 0.1 Hz to 1 GHz
- Modulation depth delta_L/L: 10^-8 to 10^-2

**Lattice**: N = 4 to 32 (N x N torus)

**Covariant Descent**: Learning rate, start point, Euclidean path toggle

### Visualizations (Center Panel)

1. **3D Rotating Torus** -- animated engine cycle phases:
   - Compress (blue, minor radius shrinks)
   - Extract (gold photon sparks on surface)
   - Expand (green, radius restores)
   - Idle (dim, re-thermalize)
   - Drag to rotate, double-click for auto-rotate

2. **Engine Cycle Energy Budget** -- bar chart:
   W_compression, E_extracted, decoherence loss, thermal noise, net work

3. **Convergence Rate vs lambda_1** -- scatter plot:
   Measured descent rate vs spectral gap across lattice sizes, confirming rate proportional to lambda_1

4. **Scaling Study** -- line chart:
   Coherence enhancement, DCE pair rate, spectral gap vs N

### Results (Right Panel)

Live-updating readout: fundamental frequency, Q factor, thermal photons, perturbative parameter, spectral gap, protection factor, energy budget, efficiency (protected vs bare), coherence enhancement, descent comparison (Euclidean vs Covariant).

Status badge: PERTURBATIVE (green) or NON-PERTURBATIVE (red).

## Physical Regimes

The simulation is frequency-agnostic. The same physics engine covers:

| Regime | Cavity Size | Frequency | Temperature | Q Factor | Modulation |
|--------|-------------|-----------|-------------|----------|------------|
| **Microwave** | 1-10 cm | 1-100 GHz | 10-50 mK | 10^8-10^12 | SQUID |
| **Mid-infrared** | 1-100 um | 1-30 THz | 4-300 K | 10^5-10^7 | MEMS |
| **Optical** | 10-100 um | 100-1000 THz | 4-300 K | 10^7-10^9 | Electro-optic |

Key scaling: energy per DCE photon pair = hbar * Omega. Optical frequencies give ~10^4x more energy per pair than microwave.

## The Engine Cycle

Analog of the Otto thermodynamic cycle operating on the quantum vacuum of a toroidal cavity:

1. **Compression** (L_max -> L_min): Adiabatic size reduction. Casimir energy becomes more negative. Mode frequencies blue-shift.

2. **Extraction**: Drive boundary at Omega ~ 2*omega_1 (parametric resonance). Dynamical Casimir effect produces photon pairs from vacuum. Spectral gap protects sub-gap modes.

3. **Expansion** (L_min -> L_max): Release stored vacuum elastic energy.

4. **Idle**: Re-thermalize. Spectral gap exponentially suppresses thermal decoherence.

### What is the fuel?

The quantum vacuum itself. Every electromagnetic mode has zero-point energy (1/2)*hbar*omega. The Casimir effect (1948, measured 1997) and the Dynamical Casimir Effect (Wilson et al. 2011, observed at Chalmers) confirm this energy is real and extractable.

The engine extracts work from the difference in Casimir energy between two cavity configurations. Efficiency eta > 1 means more energy is extracted than the compression work input -- the excess comes from vacuum fluctuations, not from violation of thermodynamics.

### Typical results (microwave regime)

| Parameter | Value |
|-----------|-------|
| omega_1 | ~33 GHz |
| Q | ~10^12 |
| n_th | ~10^-78 (quantum ground state) |
| delta_L*omega/c | ~6 x 10^-3 (perturbative) |
| lambda_1 | 0.229 (12x12 torus) |
| Net work per cycle | ~3.5 x 10^-21 J |
| Power output | ~2.3 x 10^-16 W (attoWatts) |
| Efficiency eta | ~1.9 |
| Coherence enhancement | ~4.2x |

## Analog Gravity Connection

The engine cycle on T^2 maps to analog gravity phenomena:

- **Unruh effect**: The spectral gap creates a minimum detectable acceleration. Below this threshold, the toroidal vacuum is topologically protected from thermal excitation.

- **Dynamical Casimir effect**: Boundary oscillation produces photon pairs from vacuum. Only modes above the spectral gap contribute (topological protection).

- **Casimir energy**: E ~ -hbar*c/L^2 on T^2. Compressing the torus stores energy in the vacuum field.

- **Hawking analog**: Topological defects on T^2 create acoustic horizons.

## Covariant Descent

Demonstrates that the spectral gap lambda_1 is the convergence rate for gradient descent on T^2:

- **Euclidean** (flat): theta_{t+1} = theta_t - eta * grad(L). No convergence guarantee. Can "fly off" the torus.
- **Covariant** (on T^2): Uses exponential map (wraps around). Poincare inequality guarantees exponential convergence at rate lambda_1.

The GUI overlays both paths on the 3D torus surface, showing the covariant path stays on the manifold while Euclidean drifts.

## Architecture

```
quantum-engine-sim/src/
  lib.rs          -- public module declarations
  main.rs         -- CLI text output (5-layer simulation)
  bin/gui.rs      -- eframe entry point (1400x900, wgpu/Metal)
  gui.rs          -- egui App: torus drawing, charts, sliders, results
  sim_worker.rs   -- background thread for heavy computation
  engine.rs       -- quantum engine cycle, presets (microwave/optical/mid-IR)
  covariant.rs    -- gradient descent on T^2, convergence validation
  toric_code.rs   -- Kitaev toric code Monte Carlo
  coherence.rs    -- Tonnetz-enhanced coherence times
  torus.rs        -- T^2 lattice geometry, Laplacian spectrum
  vacuum.rs       -- Casimir energy, Unruh effect, dynamical Casimir
  units.rs        -- physical constants (hbar, c, k_B)
```

The GUI uses a worker thread (crossbeam channels) for non-blocking simulation. Four request types:
- `RunEngine` -- full engine simulation
- `RunDescent` -- Euclidean vs Covariant comparison
- `RunScaling` -- performance across lattice sizes
- `RunConvergence` -- convergence rate validation

## Cross-Domain Evidence

The same toroidal geometry constrains drift across three domains:

| Domain | Observable | Result |
|--------|-----------|--------|
| **LLM** | TruthfulQA | +19.5% (Phi-2), +2.8pp (4 models via API) |
| **Quantum** | Logical error rate | P_L ~ exp(-alpha*N) below p_c ~ 10.3% |
| **Vacuum** | Casimir energy | E ~ -hbar*c/L^2 (topologically protected) |

## Experimental Status

| Component | Status |
|-----------|--------|
| DCE photon pairs from vacuum | **Observed** (Wilson et al., Nature 2011) |
| Casimir force | **Measured** (Lamoreaux 1997, <1% accuracy) |
| SC microwave cavities at mK | **Routine** (circuit QED labs worldwide) |
| SQUID boundary modulation | **Demonstrated** (Wilson 2011) |
| Full engine cycle on T^2 | **Not yet built** (this simulation) |
| Toroidal cavity for DCE | **Not yet built** (novel Paraxiom contribution) |
| Optical toroidal DCE | **Not yet built** (proposed here) |

## Dependencies

```toml
rand = "0.8"
eframe = { version = "0.31", features = ["wgpu", "default_fonts"] }
egui_plot = "0.31"
crossbeam-channel = "0.5"
```

## References

- Cormier (2026), ["Topological Constraints for Coherent Language Models"](https://doi.org/10.5281/zenodo.18624950)
- Wilson et al. (2011), "Observation of the dynamical Casimir effect in a superconducting circuit", Nature 479, 376
- Casimir (1948), "On the attraction between two perfectly conducting plates"
- Unruh (1976), "Notes on black-hole evaporation"
- Moore (1970), "Quantum theory of the electromagnetic field in a variable-length one-dimensional cavity"
- Kitaev (2003), "Fault-tolerant quantum computation by anyons"
- Dodonov (2010), "Current status of the dynamical Casimir effect", Phys. Scr. 82, 038105
- Aharonov, Bergmann, Lebowitz (1964), "Time symmetry in the quantum process of measurement"

## License

MIT -- [Paraxiom Research](https://paraxiom.org)
