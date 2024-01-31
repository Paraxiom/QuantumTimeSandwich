# 🌌 QuantumTimeSandwich Overview 🥪


Simulation platform 🚀 that merges advanced quantum algorithms with cryptographic techniques.

## Install
```
git clone https://github.com/Paraxiom/QuantumTimeSandwich.git
cd QuantumTimeSandwich/[subdirectory]
cargo build
cargo test
cargo bench
```



## 📁 Project Structure

The QuantumTimeSandwich project is organized into multiple subdirectories. Each subdirectory is a unique crate, packed with its own functionalities, examples, tests, and benchmarks.





### 🔐 BB84
- **Location:** `bb84/`
- **Functionality:** Specializes in the BB84 quantum key distribution protocol.
- **Available Examples:**
  - `basis_selection_demo`
  - `bb84_aes_integration`
  - `bb84_simulation`
  - `eavesdropping_demo`
  - `lattice_crypto_demo`
  - `lwe-demo`
  - `ring-lwe-demo`
- **Commands:**
  ```bash
  cd bb84/
  cargo run --example [example_name]
  cargo test
  cargo bench
```
  - **GRPC:**
  ```
   RUST_LOG=debug cargo run  --bin quantum_time_sandwich_server
   ```

#### 2. 🧠 QuantumTimeSandwich Core

- **Location:** `QuantumTimeSandwich/`
- **Functionality:** Core quantum computing simulations and cryptographic functions.
- **Examples:** 
  - `bell_inequalities`
  - `cswap`
  - `dense_coding`
  - `deutch`
  - `grovers`
  - `inverse_example`
  - `macro_example`
  - `optimizer_example`
  - `simple`
- **Commands:**
  ```bash
  cd QuantumTimeSandwich/
  cargo run --example [example_name]
  cargo test
  cargo bench

#### 3. 🔁 QuantumTimeSandwich Iterators

- **Location:** `QuantumTimeSandwich-iterators/`
- **Functionality:** Advanced iterators for quantum state manipulation.
- **Commands:**
  ```bash
  cd QuantumTimeSandwich-iterators/
  cargo test




Follow the specific commands listed under each subdirectory to run examples, tests, and benchmarks.

License 📜

QuantumTimeSandwich, with contributions from https://github.com/Renmusxd/RustQIP, is released under the MIT License. You are free to use, modify, and distribute the software, provided that proper credit is given.
