# 🌌 QuantumTimeSandwich Overview 🥪

#### QuantumTimeSandwich  
cutting-edge simulation platform 🚀 that merges advanced quantum algorithms with cryptographic techniques. Developed alongside Cryptonique, its goal is to propel the fields of quantum computing and encryption into new frontiers.


#### Delicious
  **Preparation:** Like the first slice of bread, we begin with setting up quantum gates and initializing qubits, laying the foundation for complex quantum processes

**Execution:** At the core, akin to the sandwich filling, lies the execution of quantum algorithms where timing and synchronization are critical to success.

**Validation:** The final layer, reminiscent of the top slice of bread, involves error correction and validation, ensuring the accuracy and integrity of our quantum computations.



## Install
'''
git clone https://github.com/Paraxiom/QuantumTimeSandwich.git
cd QuantumTimeSandwich/[subdirectory]
cargo build
cargo test
cargo bench
'''



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