Running Examples in QuantumTimeSandwich 🥪

Welcome to the practical guide for QuantumTimeSandwich, your gateway to exploring the quantum-cryptographic universe! 🌌
Overview

QuantumTimeSandwich includes a variety of examples that demonstrate the capabilities of the platform. These examples cover a range of topics from basic quantum simulations to intricate cryptographic protocols.
Getting Started 🚀

Before running the examples, ensure you've cloned the repository and installed the necessary dependencies:

bash

git clone https://github.com/Paraxiom/QuantumTimeSandwich.git
cd QuantumTimeSandwich
cargo build

Running an Example

To run an example, use the cargo run --example command followed by the name of the example file (without the .rs extension). Examples are located in the examples directory of each module.
Example: Running the BB84 AES Integration

Navigate to the root directory of QuantumTimeSandwich and execute the following command:

bash

cargo run --package bb84 --example bb84_aes_integration

This command runs the bb84_aes_integration example from the bb84 package.
Other Examples

Replace bb84_aes_integration with the name of the example you wish to run. For instance:

    cargo run --package bb84 --example bb84_simulation for BB84 protocol simulation.
    cargo run --package quantum_time_sandwich --example grovers for Grover's algorithm simulation.

Note on GUI

Currently, the GUI component of QuantumTimeSandwich is under development. Running the command cargo run without specifying an example will launch the UI, which might not have functional content yet.
Need Help?

If you encounter any issues or need further assistance, feel free to open an issue on our GitHub repository.
Contribute and Collaborate 🤝

Your contributions make QuantumTimeSandwich better! Whether it's improving the codebase, adding new examples, or sharing ideas, we welcome your involvement.
License 📜

QuantumTimeSandwich is proudly open-source, licensed under the MIT License. We encourage you to use, adapt, and share our project, keeping the spirit of collaboration alive.

Happy Quantum Computing! 🌌🥪🚀
