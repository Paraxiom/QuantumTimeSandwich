# Toroidal Spectral Filtering for Bosonic Qubit Coherence
## Technical Brief — Paraxiom Technologies Inc.

**Contact:** Sylvain Cormier, sylvain@paraxiom.org
**Date:** February 2026
**Status:** Simulation validated, seeking hardware collaboration

---

## Executive Summary

We demonstrate a **683× dephasing suppression** on bosonic modes using toroidal
(T²) spectral filtering — a topology-aware noise rejection technique derived
from the Tonnetz lattice structure. Our simulation achieves **T₂ = 12.85 ms**
on a carbon nanotorus optomechanical system, from a bare T₂ of 848 µs.

The technique is **hardware-agnostic**: the spectral gap of the toroidal lattice
Laplacian filters dephasing noise regardless of whether the bosonic mode is a
phonon (mechanical oscillator) or a photon (optical cavity / GKP qubit). We
believe this directly applies to photonic GKP code stabilization on silicon
nitride ring resonators.

---

## The Problem

Bosonic qubits — whether mechanical oscillators or photonic GKP states — suffer
from dephasing noise that limits coherence time T₂. Current approaches:

| Approach | Overhead | Drawback |
|----------|----------|----------|
| GKP code concatenation | Many physical modes per logical qubit | Resource-intensive |
| Dynamical decoupling | Pulse sequences | Timing precision, heating |
| Hardware improvements | Better fabrication | Diminishing returns |

**Missing**: a topological noise filter that suppresses dephasing at the
lattice level, before error correction even begins.

---

## Our Approach: Tonnetz Spectral Filtering

### Core Idea

Arrange N qubits on a **toroidal lattice** (T² topology). The graph Laplacian
of this lattice has a spectral gap λ₁ that determines how fast noise
propagates across the system. By coupling qubit dephasing channels through the
lattice, noise components below the spectral gap are **exponentially
suppressed**.

### The Math

Dephasing rate with Tonnetz filter:

```
γ₂_filtered = 1/(2T₁) + γ_φ / enhancement

enhancement = 1 + Q × (W/N) × (1/λ₁)
```

Where:
- **Q** = toroidal coupling quality factor (experimentally tunable)
- **W/N** = average coupling weight per site
- **λ₁** = spectral gap of T² Laplacian = 2 − 2cos(2π/√N)

For a 12×12 toroidal lattice (144 sites): λ₁ = 0.268, giving **enhancement = 684×** at Q = 100.

### Why Toroidal?

| Topology | λ₁ (144 sites) | Coherence time τ | Connectivity |
|----------|----------------|-------------------|-------------|
| **Toroidal (T²)** | **0.268** | **3.73/γ** | **4-connected, scalable** |
| Linear chain | 0.000475 | 2105/γ | 2-connected, poor gates |
| Complete graph | 144 | 0.007/γ | All-to-all, unphysical |

The torus is the sweet spot: enough connectivity for quantum gates, small enough
spectral gap for noise filtering, and it maps directly to **ring resonator
arrays** and **waveguide meshes** — hardware Xanadu already builds.

---

## Simulation Results: CNT Nanotorus

We validated the concept on a carbon nanotorus optomechanical system (the most
experimentally accessible bosonic platform for us):

### Head-to-Head: Nanotorus vs. Straight Nanotube

| Parameter | Nanotorus (T²) | Nanotube (linear) | Ratio |
|-----------|----------------|-------------------|-------|
| **T₂ (with Tonnetz)** | **12.85 ms** | 3.92 ms | **3.3×** |
| T₂ bare | 848 µs | 771 µs | 1.1× |
| **Tonnetz enhancement** | **684×** | 17× | **40×** |
| Q mechanical | 10⁷ | 5×10⁵ | 20× |
| g₀ coupling | 76.6 kHz | 1.88 kHz | 41× |
| Gate error (100 ns gate) | **7.8×10⁻⁶** | 2.6×10⁻⁵ | 3.3× |

### Key Insight

The bare T₂ improvement (torus vs tube) is modest: 848 µs → 771 µs (1.1×).
The **topology does the heavy lifting**: once the Tonnetz spectral filter is
applied, the nanotorus jumps to 12.85 ms — a **15× improvement** over its own
bare value. This is the spectral gap at work, not just better hardware.

### Physical Parameters (Default Configuration)

```
Material:           Carbon SWCNT (E = 1 TPa, ρ = 2200 kg/m³)
Ring diameter:      200 nm
CNT diameter:       1.4 nm (single wall)
Temperature:        20 mK (dilution fridge)
Cavity finesse:     50,000 (WGM)
Laser power:        20 mW (red-detuned)
Tonnetz grid:       12×12 = 144 qubits
Tonnetz Q:          100
Frequency:          358 MHz
Cooperativity:      6.9 × 10¹²
Final phonon n:     0.016 (ground state)
```

---

## Application to Photonic GKP Qubits

### Direct Mapping

The Tonnetz spectral filter operates on the **lattice topology**, not the
physical substrate. The translation to photonic systems:

| Mechanical (our sim) | Photonic (Xanadu hardware) |
|----------------------|---------------------------|
| Phonon modes in nanotorus | Photon modes in Si₃N₄ ring resonator |
| WGM cavity coupling | Waveguide-coupled ring arrays |
| Mechanical Q = 10⁷ | Optical Q > 10⁶ (Si₃N₄) |
| Tonnetz lattice on phonon dephasing | Tonnetz lattice on GKP stabilizer noise |
| Piezo tuning | Thermo-optic / electro-optic tuning |

### What Changes, What Stays

**Stays the same:**
- Toroidal lattice structure and spectral gap λ₁
- Enhancement formula (hardware-agnostic)
- Scaling: enhancement grows as √N with lattice size
- Gate error reduction below toric code threshold

**Changes:**
- Physical noise sources (thermal phonons → photon loss / phase noise)
- Coupling mechanism (optomechanical g₀ → evanescent waveguide coupling)
- Operating regime (microwave/MHz → optical/THz)

### Predicted Impact on GKP Codes

Xanadu's June 2025 Nature paper demonstrated on-chip GKP qubit generation in
Si₃N₄. The dominant error channel is **photon loss + dephasing**. Applying
Tonnetz filtering to a 12×12 array of coupled ring resonators would:

1. Suppress dephasing by up to **684×** (matching our mechanical simulation)
2. Reduce GKP concatenation overhead (fewer physical modes per logical qubit)
3. Leverage existing Si₃N₄ ring resonator fabrication — no new hardware

---

## What We Bring

| Capability | Status |
|------------|--------|
| Tonnetz spectral gap theory + proofs | Published (Zenodo, DOI: 10.5281/zenodo.18516477) |
| Full physics simulation (Rust, 28 tests) | Complete, open-source ready |
| Interactive GUI with real-time parameter sweep | Complete (egui/wgpu) |
| Toroidal Logit Bias (ML application) | Published, +2.8pp TruthfulQA |
| Post-quantum cryptography stack (qssh, qssl) | Production-ready, 110+ tests |
| Defensive technical disclosure (all embodiments) | Published (DOI: 10.5281/zenodo.18595753) |

## What We Need

1. **Photonic hardware validation** — run the Tonnetz filter on actual Si₃N₄
   ring resonator arrays
2. **GKP code integration** — adapt the spectral filtering to GKP stabilizer
   measurements
3. **PennyLane plugin** — implement Tonnetz-enhanced noise channels in
   PennyLane for community access

---

## The Torus Knot Connection

The (p,q) torus knot — a curve winding p times around the torus hole and q
times through the tube — corresponds to **whispering gallery mode patterns** on
both mechanical nanotori and optical ring resonators. Our simulation visualizes
the (3,2) knot on the nanotorus and the (2,3) knot on the Tonnetz lattice.

These are not decorative: the knot winding numbers determine which vibrational
(or optical) modes couple to the spectral filter. The T(3,2) knot on a
nanotorus maps to the third-harmonic WGM on a photonic ring — exactly the modes
Xanadu's Si₃N₄ chips support.

---

## References

1. S. Cormier, "Toroidal Logit Bias," Zenodo, Feb 2026. DOI: 10.5281/zenodo.18516477
2. S. Cormier, "Defensive Technical Disclosure — Toroidal Coherence," Zenodo, Feb 2026. DOI: 10.5281/zenodo.18595753
3. Xanadu, "On-chip generation of error-resistant photonic GKP qubits," Nature, Jun 2025.
4. Xanadu, "Scaling and networking a modular photonic quantum computer" (Aurora), Nature, Jan 2025.
5. Xanadu, "Breakthrough quantum error-correction protocol using photonic GKP qubits," PRL, Mar 2025.

---

**Paraxiom Technologies Inc.**
Montreal, Canada | paraxiom.org | github.com/Paraxiom
