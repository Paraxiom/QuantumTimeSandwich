# QuantumTimeSandwich

Rust quantum computing library — the core of the QuantumTimeSandwich platform.

## Why "Quantum Time Sandwich"?

Every quantum application follows the same architecture: classical operations **sandwich** the quantum operation.

```
Classical (pre)   → prepare keys, authenticate, set up state
Quantum (middle)  → QKD, QRNG, entanglement, gate operations
Classical (post)  → sign, verify, attest, process results
```

This library implements all three layers in Rust.

## Features

- Quantum gate simulation (Deutsch, Grover, CSWAP, Bell inequalities)
- Dense coding and quantum state manipulation
- Boolean circuit construction via macros
- Parallel execution via Rayon
- Exact arithmetic with `num-rational`

## Usage

```rust
use QuantumTimeSandwich::prelude::*;
```

## License

MIT. Based on contributions from [RustQIP](https://github.com/Renmusxd/RustQIP).

## Links

- [Repository](https://github.com/Paraxiom/QuantumTimeSandwich)
- [Paper](https://doi.org/10.5281/zenodo.18624950)
