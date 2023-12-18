QuantumTimeSandwich
Overview

QuantumTimeSandwich is a comprehensive simulation platform integrating advanced quantum algorithms with cryptographic techniques. Developed in collaboration with Cryptonique, it aims to advance the fields of quantum computing and encryption.
Project Structure

The QuantumTimeSandwich project consists of multiple subdirectories, each representing a separate crate with its own set of functionalities, examples, tests, and benchmarks.
1. BB84

    Location: bb84/
    Functionality: Focuses on the BB84 quantum key distribution protocol.
    Examples: basis_selection_demo, bb84_aes_integration, bb84_simulation, eavesdropping_demo, lattice_crypto_demo, lwe-demo, ring-lwe-demo
    Commands:

    bash

    cd bb84/
    cargo run --example [example_name]
    cargo test
    cargo bench

2. QuantumTimeSandwich Core

    Location: QuantumTimeSandwich/
    Functionality: Core quantum computing simulations and cryptographic functions.
    Examples: bell_inequalities, cswap, dense_coding, deutch, grovers, inverse_example, macro_example, optimizer_example, simple
    Commands:

    bash

    cd QuantumTimeSandwich/
    cargo run --example [example_name]
    cargo test
    cargo bench

3. QuantumTimeSandwich Iterators

    Location: QuantumTimeSandwich-iterators/
    Functionality: Advanced iterators for quantum state manipulation.
    Commands:

    bash

    cd QuantumTimeSandwich-iterators/
    cargo test
    cargo bench

4. Unit Circle State Machine

    Location: unit_circle_state_machine/
    Functionality: Simulations related to the unit circle state machine concept.
    Commands:

    bash

    cd unit_circle_state_machine/
    cargo test
    cargo bench

5. Visualisation

    Location: visualisation/
    Functionality: Visualization tools for quantum states and operations.
    Commands:

    bash

    cd visualisation/
    cargo run
    cargo test

Getting Started 🚀

To get started with QuantumTimeSandwich, clone the repository and navigate to the subdirectory of interest. Each subdirectory is a separate Rust crate with its own examples, tests, and benchmarks.

bash

git clone https://github.com/Paraxiom/QuantumTimeSandwich.git
cd QuantumTimeSandwich/[subdirectory]

Follow the specific commands listed under each subdirectory to run examples, tests, and benchmarks.
License 📜

QuantumTimeSandwich, with contributions from https://github.com/Renmusxd/RustQIP, is released under the MIT License. You are free to use, modify, and distribute the software, provided that proper credit is given.